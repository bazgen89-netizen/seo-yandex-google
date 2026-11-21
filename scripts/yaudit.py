#!/usr/bin/env python3
"""yaudit – SEO-аудит сайта под Яндекс.

Обходит сайт так, как его видит робот Яндекса (YandexBot, правила robots.txt для группы Yandex),
проверяет то, что важно именно для Яндекса, и пишет отчёт на русском: что исправить, почему и как.
По желанию добавляет данные Яндекс Вебмастера (API, нужен OAuth-токен), проверку орфографии
Яндекс Спеллером и проверку YML-фида для Яндекс Маркета и «Товаров».

Только стандартная библиотека Python 3.10+, ставить ничего не нужно.

    python3 yaudit.py https://example.ru
    python3 yaudit.py https://example.ru --max-pages 500 --speller --webmaster -o report.md
    python3 yaudit.py https://example.ru --yml https://example.ru/feed.yml --format json -o report.json
"""
import argparse
import concurrent.futures as cf
import gzip
import hashlib
import html
import json
import os
import random
import re
import socket
import ssl
import string
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from collections import Counter, defaultdict
from html.parser import HTMLParser

VERSION = "1.0.0"
YANDEX_UA = "Mozilla/5.0 (compatible; YandexBot/3.0; +http://yandex.com/bots)"
BROWSER_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
              "Chrome/128.0.0.0 YaBrowser/24.10.0.0 Safari/537.36")
MAX_BODY = 6 * 1024 * 1024
SEV_ORDER = {"critical": 0, "important": 1, "advice": 2, "info": 3}
SEV_TITLE = {"critical": "Критично", "important": "Важно", "advice": "Желательно", "info": "К сведению"}
TRACKING_PARAMS = ("utm_", "yclid", "gclid", "fbclid", "from", "_openstat", "ysclid", "etext")

# ---------------------------------------------------------------- сеть


class _NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *a, **k):
        return None


def _opener():
    ctx = ssl.create_default_context(cafile=os.environ.get("SSL_CERT_FILE") or None)
    return urllib.request.build_opener(_NoRedirect, urllib.request.HTTPSHandler(context=ctx),
                                       urllib.request.ProxyHandler())


OPENER = _opener()


def fetch(url, ua=YANDEX_UA, timeout=20, follow=True, method="GET", headers=None, data=None, tries=3):
    """Запрос с повтором при обрыве соединения (сетевые сбои – не ошибка сайта)."""
    for i in range(tries):
        r = _fetch(url, ua, timeout, follow, method, headers, data)
        if r["status"] or i == tries - 1 or "больше 10" in (r["error"] or ""):
            return r
        time.sleep(1.5 * (i + 1))
    return r


def _fetch(url, ua=YANDEX_UA, timeout=20, follow=True, method="GET", headers=None, data=None):
    """Запрос с ручным проходом редиректов: возвращает цепочку, код, заголовки, тело, время ответа."""
    chain, cur, t0 = [], url, time.time()
    for _ in range(10):
        h = {"User-Agent": ua, "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
             "Accept-Language": "ru-RU,ru;q=0.9", "Accept-Encoding": "gzip"}
        h.update(headers or {})
        req = urllib.request.Request(to_uri(cur), headers=h, method=method, data=data)
        try:
            r = OPENER.open(req, timeout=timeout)
            code, hdrs = r.status, r.headers
            body = r.read(MAX_BODY) if method != "HEAD" else b""
        except urllib.error.HTTPError as e:
            code, hdrs = e.code, e.headers
            try:
                body = e.read(MAX_BODY)
            except Exception:
                body = b""
        except Exception as e:  # DNS, TLS, таймаут, обрыв
            return {"url": url, "final": cur, "status": 0, "error": f"{type(e).__name__}: {e}"[:200],
                    "chain": chain, "headers": {}, "body": b"", "time": time.time() - t0}
        if hdrs.get("Content-Encoding", "").lower() == "gzip" and body:
            try:
                body = gzip.decompress(body)
            except Exception:
                pass
        if code in (301, 302, 303, 307, 308) and follow and hdrs.get("Location"):
            nxt = urllib.parse.urljoin(cur, hdrs["Location"])
            chain.append((cur, code))
            cur = nxt
            continue
        return {"url": url, "final": cur, "status": code, "error": None, "chain": chain,
                "headers": {k.lower(): v for k, v in hdrs.items()}, "body": body, "time": time.time() - t0}
    return {"url": url, "final": cur, "status": 0, "error": "больше 10 редиректов", "chain": chain,
            "headers": {}, "body": b"", "time": time.time() - t0}


def text_of(resp):
    b = resp["body"]
    m = re.search(r"charset=([\w-]+)", resp["headers"].get("content-type", ""), re.I)
    for enc in ([m.group(1)] if m else []) + ["utf-8", "cp1251"]:
        try:
            return b.decode(enc)
        except Exception:
            continue
    return b.decode("utf-8", "replace")


_SAFE = "/%:@!$&'()*+,;=-._~"


def to_uri(url):
    """Адрес с кириллицей и другими не-ASCII символами – в процентную запись (как отправляет браузер)."""
    p = urllib.parse.urlsplit(url)
    host = p.netloc.encode("idna").decode() if any(ord(c) > 127 for c in p.netloc) else p.netloc
    return urllib.parse.urlunsplit((p.scheme, host, urllib.parse.quote(p.path, safe=_SAFE),
                                    urllib.parse.quote(p.query, safe=_SAFE + "?"), ""))


def norm(url):
    """Адрес без #фрагмента, в единой процентной записи (адреса «ʺ» и «%CA%BA» – один адрес);
    путь как есть: слеш в конце важен – это разные адреса."""
    p = urllib.parse.urlsplit(url)
    path = urllib.parse.quote(urllib.parse.unquote(p.path or "/"), safe=_SAFE)
    query = urllib.parse.quote(urllib.parse.unquote(p.query), safe=_SAFE + "?")
    return urllib.parse.urlunsplit((p.scheme.lower(), p.netloc.lower(), path, query, ""))


# ---------------------------------------------------------------- robots.txt по правилам Яндекса


class Robots:
    """Разбор robots.txt так, как его читает Яндекс: группа User-agent: Yandex, если она есть, иначе *;
    Allow/Disallow с * и $, побеждает самое длинное совпадение, при равенстве – Allow; Clean-param."""

    def __init__(self, text):
        self.text = text or ""
        self.groups = []          # [(agents, [(allow, pattern)])]
        self.sitemaps, self.clean_params, self.hosts, self.crawl_delay = [], [], [], []
        agents, rules, last_was_agent = [], [], False
        for raw in self.text.splitlines():
            line = raw.split("#", 1)[0].strip()
            if ":" not in line:
                continue
            k, v = [x.strip() for x in line.split(":", 1)]
            k = k.lower()
            if k == "user-agent":
                if not last_was_agent and agents:
                    self.groups.append((agents, rules))
                    agents, rules = [], []
                agents.append(v.lower())
                last_was_agent = True
                continue
            last_was_agent = False
            if k in ("allow", "disallow"):
                rules.append((k == "allow", v))
            elif k == "sitemap":
                self.sitemaps.append(v)
            elif k == "clean-param":
                self.clean_params.append(v)
            elif k == "host":
                self.hosts.append(v)
            elif k == "crawl-delay":
                self.crawl_delay.append(v)
        if agents:
            self.groups.append((agents, rules))
        self.yandex_group = next((r for a, r in self.groups if any(x in ("yandex", "yandexbot") for x in a)), None)
        self.star_group = next((r for a, r in self.groups if "*" in a), None)
        self.rules = self.yandex_group if self.yandex_group is not None else (self.star_group or [])

    @staticmethod
    def _rx(pattern):
        end = pattern.endswith("$")
        p = re.escape(pattern.rstrip("$")).replace(r"\*", ".*")
        return re.compile("^" + p + ("$" if end else ""))

    def allowed(self, url):
        p = urllib.parse.urlsplit(url)
        path = (p.path or "/") + (("?" + p.query) if p.query else "")
        best = None  # (длина, allow)
        for allow, pat in self.rules:
            if pat == "":
                if not allow:
                    continue      # пустой Disallow – разрешено всё
                pat = "/"
            if self._rx(pat).match(path):
                cand = (len(pat), allow)
                if best is None or cand[0] > best[0] or (cand[0] == best[0] and allow):
                    best = cand
        return True if best is None else best[1]

    def clean_param_names(self):
        names = set()
        for cp in self.clean_params:
            first = cp.split()[0] if cp.split() else ""
            names.update(x.strip() for x in first.split("&") if x.strip())
        return names


# ---------------------------------------------------------------- разбор HTML


class Page(HTMLParser):
    SKIP = {"script", "style", "noscript", "template", "svg"}

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.lang, self.title, self.in_title = None, None, False
        self.metas, self.links, self.anchors, self.imgs = [], [], [], []
        self.headings, self._h, self._htext = [], None, []
        self.jsonld, self._ld, self._ldbuf = [], False, []
        self.scripts_src, self.inline_js = [], []
        self._script, self._scriptbuf = False, []
        self.text, self._skip = [], 0
        self.noindex_tags, self.iframes, self.mixed = 0, 0, []
        self.forms = 0
        self._tpl = 0   # внутри <template>: разметка для скриптов, браузер её не показывает

    def handle_starttag(self, tag, attrs):
        a = {k.lower(): (v or "") for k, v in attrs}
        if tag == "template":
            self._tpl += 1
        if self._tpl and tag in ("a", "img"):
            return
        if tag == "html":
            self.lang = a.get("lang")
        elif tag == "title" and self.title is None:
            self.in_title, self.title = True, ""
        elif tag == "meta":
            self.metas.append(a)
        elif tag == "link":
            self.links.append(a)
        elif tag == "a" and "href" in a:
            self.anchors.append(a)
        elif tag == "img":
            self.imgs.append(a)
        elif tag == "noindex":
            self.noindex_tags += 1
        elif tag == "iframe":
            self.iframes += 1
        elif tag == "form":
            self.forms += 1
        elif tag in ("h1", "h2", "h3", "h4", "h5", "h6"):
            self._h, self._htext = tag, []
        if tag == "script":
            if "src" in a:
                self.scripts_src.append(a["src"])
            if "ld+json" in a.get("type", ""):
                self._ld, self._ldbuf = True, []
            else:
                self._script, self._scriptbuf = True, []
        for k in ("src", "href"):
            v = a.get(k, "")
            if v.startswith("http://") and tag in ("img", "script", "iframe", "source", "video", "audio") or \
                    (tag == "link" and v.startswith("http://") and a.get("rel", "").lower() in ("stylesheet", "preload", "icon")):
                self.mixed.append(v)
        if tag in self.SKIP:
            self._skip += 1

    def handle_endtag(self, tag):
        if tag == "template" and self._tpl:
            self._tpl -= 1
        if tag == "title":
            self.in_title = False
        elif tag == self._h:
            self.headings.append((self._h, " ".join("".join(self._htext).split())))
            self._h = None
        if tag == "script":
            if self._ld:
                self.jsonld.append("".join(self._ldbuf))
                self._ld = False
            elif self._script:
                self.inline_js.append("".join(self._scriptbuf))
                self._script = False
        if tag in self.SKIP and self._skip:
            self._skip -= 1

    def handle_data(self, data):
        if self.in_title:
            self.title += data
        if self._h:
            self._htext.append(data)
        if self._ld:
            self._ldbuf.append(data)
        elif self._script:
            self._scriptbuf.append(data)
        elif not self._skip:
            self.text.append(data)

    # удобные выборки
    def meta(self, name=None, prop=None):
        for m in self.metas:
            if name and m.get("name", "").lower() == name:
                return m.get("content")
            if prop and m.get("property", "").lower() == prop:
                return m.get("content")
        return None

    def link_rel(self, rel):
        return [l for l in self.links if rel in l.get("rel", "").lower().split()]


def ld_types(blocks):
    """Типы schema.org из JSON-LD (с @graph); None в списке – блок с ошибкой JSON."""
    out, objs = [], []
    for b in blocks:
        try:
            d = json.loads(b.strip())
        except Exception:
            out.append(None)
            continue
        stack = [d]
        while stack:
            x = stack.pop()
            if isinstance(x, list):
                stack.extend(x)
            elif isinstance(x, dict):
                t = x.get("@type")
                if t:
                    for tt in (t if isinstance(t, list) else [t]):
                        out.append(str(tt))
                        objs.append((str(tt), x))
                if "@graph" in x:
                    stack.append(x["@graph"])
    return out, objs


CYR_WORD = re.compile(r"[А-Яа-яЁё][А-Яа-яЁё\-]+")

# ---------------------------------------------------------------- аудит


class Audit:
    def __init__(self, start, args):
        self.args = args
        p = urllib.parse.urlsplit(start if "://" in start else "https://" + start)
        self.scheme, self.host = p.scheme, p.netloc.lower()
        self.root = f"{self.scheme}://{self.host}/"
        self.findings = defaultdict(lambda: {"urls": [], "count": 0, "extra": []})
        self.meta = {}
        self.passed = []
        self.pages = {}          # url -> данные страницы
        self.status = {}         # url -> код
        self.inlinks = defaultdict(set)
        self.sitemap_urls = set()
        self.robots = Robots("")
        self.started = time.time()

    # -- учёт находок
    def add(self, fid, sev, title, why, fix, url=None, extra=None):
        f = self.findings[fid]
        f.update(id=fid, sev=sev, title=title, why=why, fix=fix)
        f["count"] += 1
        if url and len(f["urls"]) < 8 and url not in f["urls"]:
            f["urls"].append(url)
        if extra and len(f["extra"]) < 8:
            f["extra"].append(extra)

    def ok(self, name):
        self.passed.append(name)

    def log(self, *a):
        if not self.args.quiet:
            print(*a, file=sys.stderr, flush=True)

    def same_host(self, url):
        return urllib.parse.urlsplit(url).netloc.lower() == self.host

    # -- шаг 1: сайт целиком
    def site_checks(self):
        self.log("robots.txt, зеркала, 404…")
        r = fetch(self.root + "robots.txt", timeout=self.args.timeout)
        self.meta["robots_status"] = r["status"]
        if r["status"] != 200:
            self.add("robots-missing", "important", "robots.txt не отдаётся",
                     f"Ответ {r['status'] or r['error']}. Без robots.txt Яндекс не знает, что не индексировать, "
                     "и не видит Clean-param и Sitemap; в Вебмастере это ошибка NO_ROBOTS_TXT.",
                     "Положите robots.txt в корень сайта с кодом 200.", self.root + "robots.txt")
        else:
            body = text_of(r)
            self.robots = Robots(body)
            rb = self.robots
            if len(r["body"]) > 500 * 1024:
                self.add("robots-big", "important", "robots.txt больше 500 КБ",
                         "Яндекс читает robots.txt только до 500 КБ, остальное считает разрешённым.",
                         "Сократите правила, объедините похожие через *.", self.root + "robots.txt")
            if not rb.allowed(self.root):
                self.add("robots-blocks-site", "critical", "robots.txt закрывает сайт от Яндекса",
                         "Для группы, которую читает Яндекс, главная страница под Disallow. Сайт выпадет из поиска.",
                         "Уберите Disallow: / из группы User-agent: Yandex (или *).", self.root + "robots.txt")
            else:
                self.ok("Главная открыта для Яндекса в robots.txt")
            if rb.yandex_group is not None and rb.star_group:
                star_dis = {p for a, p in rb.star_group if not a and p}
                y_dis = {p for a, p in rb.yandex_group if not a and p}
                miss = sorted(star_dis - y_dis)
                if miss:
                    self.add("robots-yandex-group", "important", "В группе Yandex нет запретов из группы *",
                             "Если в robots.txt есть User-agent: Yandex, Яндекс читает только её и игнорирует *. "
                             f"Запреты из * для него не действуют: {', '.join(miss[:8])}.",
                             "Повторите нужные Disallow в группе Yandex или удалите отдельную группу.",
                             self.root + "robots.txt")
            blocked_assets = [p for a, p in rb.rules if not a and re.search(r"\.css|\.js|/wp-includes|/assets|/static|/images?/|/wp-content/?$", p)]
            if blocked_assets:
                self.add("robots-assets", "important", "robots.txt закрывает CSS, JS или картинки",
                         "Без стилей и скриптов Яндекс не может отрисовать страницу и оценить удобство на телефоне "
                         f"(NOT_MOBILE_FRIENDLY). Закрыто: {', '.join(blocked_assets[:6])}.",
                         "Откройте папки со стилями, скриптами и картинками (Allow) для Яндекса.",
                         self.root + "robots.txt")
            if not rb.sitemaps:
                self.add("robots-no-sitemap", "advice", "В robots.txt нет строки Sitemap",
                         "Яндекс находит карту сайта по robots.txt; без строки её нужно добавлять в Вебмастере вручную.",
                         f"Добавьте: Sitemap: {self.root}sitemap.xml", self.root + "robots.txt")
            if not rb.clean_params:
                self.add("robots-no-clean-param", "advice", "Нет Clean-param для меток (utm, yclid и т. п.)",
                         "Clean-param понимает только Яндекс: он склеивает адреса с метками рекламы и рассылок, "
                         "и робот не тратит обход на дубли. Иначе в Вебмастере бывает INSIGNIFICANT_CGI_PARAMETER.",
                         "Добавьте в robots.txt: Clean-param: utm_source&utm_medium&utm_campaign&utm_content&utm_term&yclid&gclid&fbclid&ysclid&from",
                         self.root + "robots.txt")
            else:
                self.ok("Clean-param в robots.txt есть")
            if rb.hosts:
                self.add("robots-host", "info", "В robots.txt осталась директива Host",
                         "С 2018 года Яндекс её не учитывает: главное зеркало задаётся 301-редиректом.",
                         "Строку можно удалить; главное зеркало – через редирект и в Вебмастере.", self.root + "robots.txt")
            if rb.crawl_delay:
                self.add("robots-crawl-delay", "info", "В robots.txt есть Crawl-delay",
                         "Яндекс не учитывает Crawl-delay с 2018 года.",
                         "Скорость обхода задаётся в Вебмастере: Индексирование → Скорость обхода.", self.root + "robots.txt")

        # главное зеркало: http → https, www ↔ без www
        bare = self.host[4:] if self.host.startswith("www.") else self.host
        variants = {f"http://{bare}/", f"http://www.{bare}/", f"https://{bare}/", f"https://www.{bare}/"}
        variants.discard(self.root)
        for v in sorted(variants):
            rv = fetch(v, timeout=self.args.timeout, follow=False)
            if rv["status"] == 0:
                continue
            loc = rv["headers"].get("location", "")
            if rv["status"] == 200:
                self.add("mirror-no-redirect", "critical", "Второе зеркало сайта отдаёт 200 без редиректа",
                         f"{v} открывается сам по себе. Для Яндекса это два разных сайта с одинаковыми страницами: "
                         "дубли и риск, что главным зеркалом станет не тот адрес (MAIN_MIRROR_IS_NOT_HTTPS).",
                         f"Поставьте 301-редирект со всех вариантов адреса на {self.root}", v)
            elif rv["status"] in (302, 303, 307):
                self.add("mirror-302", "important", "Зеркало перенаправляет временным редиректом",
                         f"{v} → {loc} кодом {rv['status']}. Склейку зеркал Яндекс делает по постоянному 301.",
                         "Замените редирект на 301.", v)
        r0 = fetch(self.root, timeout=self.args.timeout, follow=False)
        if r0["status"] in (301, 302, 303, 307, 308):
            self.add("main-redirects", "important", "Главная страница перенаправляет",
                     f"{self.root} → {r0['headers'].get('location')} ({r0['status']}). В Вебмастере это MAIN_PAGE_REDIRECTS: "
                     "робот может не дойти до содержимого главной.",
                     "Главная должна отвечать 200 по основному адресу.", self.root)
        elif r0["status"] == 0:
            self.add("main-down", "critical", "Главная не открывается", r0["error"] or "",
                     "Проверьте сервер, DNS и сертификат.", self.root)

        # мягкая 404
        junk = self.root + "yaudit-" + "".join(random.choices(string.ascii_lowercase, k=10)) + "/"
        rj = fetch(junk, timeout=self.args.timeout)
        self.meta["soft404_status"] = rj["status"]
        if rj["status"] == 200:
            self.add("soft-404", "important", "Несуществующая страница отвечает 200",
                     "Робот получает «страницу» на любой адрес и может индексировать мусор; в Вебмастере – SOFT_404.",
                     "Для несуществующих адресов отдавайте код 404 (страница может быть красивой, но код – 404).", junk)
        elif rj["status"] in (404, 410):
            self.ok("Несуществующий адрес отвечает 404")
        elif rj["status"] >= 500 or rj["status"] == 0:
            self.add("soft-404-5xx", "important", f"Несуществующая страница отвечает {rj['status'] or rj['error']}",
                     "Код 5xx для робота значит «сервер сломан», а не «страницы нет»; при частых 5xx Яндекс снижает "
                     "скорость обхода (URL_ALERT_5XX).", "Отдавайте 404 для несуществующих адресов.", junk)

        # фавикон: Яндекс показывает его в выдаче, рекомендует SVG или PNG от 120×120
        rf = fetch(self.root + "favicon.ico", timeout=self.args.timeout)
        self.meta["favicon_ico"] = rf["status"]

    # -- шаг 2: карта сайта
    def sitemaps(self):
        cand = list(self.robots.sitemaps) or [self.root + "sitemap.xml", self.root + "sitemap_index.xml"]
        seen, queue, found_any = set(), list(cand), False
        while queue and len(seen) < 60:
            sm = queue.pop(0)
            if sm in seen:
                continue
            seen.add(sm)
            r = fetch(sm, timeout=self.args.timeout)
            if r["status"] != 200:
                if sm in self.robots.sitemaps:
                    self.add("sitemap-broken", "important", "Карта сайта из robots.txt не открывается",
                             f"Ответ {r['status'] or r['error']}. В Вебмастере это ERRORS_IN_SITEMAPS.",
                             "Исправьте адрес в robots.txt или верните файл.", sm)
                continue
            body = r["body"]
            if sm.endswith(".gz"):
                try:
                    body = gzip.decompress(body)
                except Exception:
                    pass
            try:
                root = ET.fromstring(body)
            except Exception as e:
                self.add("sitemap-xml", "important", "Карта сайта – не XML", f"{e}"[:160],
                         "Проверьте файл валидатором в Вебмастере: Инструменты → Анализ файлов Sitemap.", sm)
                continue
            found_any = True
            ns = ""
            if root.tag.startswith("{"):
                ns = root.tag.split("}")[0] + "}"
            if root.tag.endswith("sitemapindex"):
                for loc in root.iter(ns + "loc"):
                    queue.append((loc.text or "").strip())
                continue
            n, bad_lastmod = 0, 0
            for u in root.iter(ns + "url"):
                loc = u.find(ns + "loc")
                if loc is None or not (loc.text or "").strip():
                    continue
                url = loc.text.strip()
                n += 1
                if not self.same_host(url):
                    self.add("sitemap-foreign", "important", "В карте сайта адреса другого домена или зеркала",
                             "Яндекс игнорирует адреса не с того хоста, на котором лежит карта.",
                             "Оставьте в карте только адреса главного зеркала.", url)
                    continue
                self.sitemap_urls.add(norm(url))
                lm = u.find(ns + "lastmod")
                if lm is not None and lm.text and not re.match(r"^\d{4}-\d{2}-\d{2}(T\d{2}:\d{2}(:\d{2}(\.\d+)?)?(Z|[+-]\d{2}:\d{2}))?$", lm.text.strip()):
                    bad_lastmod += 1
            if n > 50000 or len(body) > 50 * 1024 * 1024:
                self.add("sitemap-too-big", "important", "Карта сайта больше 50 000 адресов или 50 МБ",
                         "Яндекс читает не больше 50 000 адресов и 50 МБ в одном файле.",
                         "Разбейте на несколько файлов и соберите их в sitemap index.", sm)
            if bad_lastmod:
                self.add("sitemap-lastmod", "advice", "Неверный формат lastmod в карте сайта",
                         f"{bad_lastmod} записей не в формате W3C Datetime; Яндекс их пропускает.",
                         "Пишите дату как 2026-01-31 или 2026-01-31T12:00:00+03:00.", sm)
        self.meta["sitemap_files"] = len(seen)
        self.meta["sitemap_urls"] = len(self.sitemap_urls)
        if not found_any:
            self.add("sitemap-none", "important", "Карта сайта не найдена",
                     "Ни в robots.txt, ни по адресам /sitemap.xml и /sitemap_index.xml карты нет (NO_SITEMAPS). "
                     "Без неё новые страницы попадают в индекс медленнее.",
                     "Сделайте sitemap.xml, пропишите в robots.txt и добавьте в Вебмастер.", self.root)
        else:
            self.ok(f"Карта сайта найдена: {len(seen)} файл(ов), {len(self.sitemap_urls)} адресов")
        blocked = [u for u in self.sitemap_urls if not self.robots.allowed(u)]
        for u in blocked[:8]:
            self.add("sitemap-disallowed", "important", "В карте сайта адреса, закрытые в robots.txt",
                     "Противоречивый сигнал: карта просит проиндексировать, robots.txt запрещает.",
                     "Уберите закрытые адреса из карты или откройте их в robots.txt.", u)
        if len(blocked) > 8:
            self.findings["sitemap-disallowed"]["count"] = len(blocked)

    # -- шаг 3: обход страниц
    def crawl(self):
        start = [self.root] + sorted(self.sitemap_urls)
        queue, seen = [], set()
        for u in start:
            n = norm(u)
            if n not in seen:
                seen.add(n)
                queue.append(n)
        limit = self.args.max_pages
        inc = re.compile(self.args.include) if self.args.include else None
        exc = re.compile(self.args.exclude) if self.args.exclude else None
        self.log(f"обход: до {limit} страниц, в очереди {len(queue)}")
        done, failed = 0, []
        with cf.ThreadPoolExecutor(max_workers=self.args.workers) as pool:
            while queue and done < limit:
                batch = []
                while queue and len(batch) < self.args.workers * 4 and done + len(batch) < limit:
                    u = queue.pop(0)
                    path = urllib.parse.urlsplit(u).path
                    if (inc and not inc.search(path)) or (exc and exc.search(path)):
                        continue
                    if not self.robots.allowed(u):
                        self.pages[u] = {"blocked": True}
                        continue
                    batch.append(u)
                for u, r in zip(batch, pool.map(lambda x: self._get(x), batch)):
                    done += 1
                    if r["status"] == 0:     # сетевой сбой – перепроверим в конце, по одной и не спеша
                        failed.append(u)
                        continue
                    for link in self.page(u, r):
                        if link not in seen and len(seen) < limit * 20:
                            seen.add(link)
                            queue.append(link)
                if self.args.delay:
                    time.sleep(self.args.delay)
                if done and done % 50 < self.args.workers * 4:
                    self.log(f"  страниц: {done}, в очереди {len(queue)}")
        if failed:
            self.log(f"перепроверка {len(failed)} страниц после сетевых сбоев")
        for u in failed:
            time.sleep(2)
            self.page(u, fetch(u, timeout=self.args.timeout + 10, tries=4))
        self.meta["pages_crawled"] = done

    def _get(self, u):
        return fetch(u, timeout=self.args.timeout)

    def page(self, u, r):
        """Проверки одной страницы; возвращает внутренние ссылки для обхода."""
        self.status[u] = r["status"]
        info = {"status": r["status"], "time": r["time"], "chain": r["chain"], "final": r["final"]}
        self.pages[u] = info
        if r["status"] == 0:
            self.add("fetch-error", "critical", "Страница не открывается роботом",
                     "Ошибка соединения: робот не получит страницу.", "Проверьте сервер, сертификат, защиту от ботов.",
                     u, r["error"])
            return []
        if r["chain"]:
            info["redirect"] = True
            if len(r["chain"]) > 1:
                self.add("redirect-chain", "advice", "Цепочка из нескольких редиректов",
                         "Каждый лишний шаг тратит обход робота, а после 5 шагов он может не дойти до страницы.",
                         "Ведите ссылку сразу на конечный адрес одним 301.", u,
                         " → ".join(f"{x} ({c})" for x, c in r["chain"]) + " → " + r["final"])
            if any(c in (302, 303, 307) for _, c in r["chain"]):
                self.add("redirect-302", "advice", "Временный редирект (302/307) внутри сайта",
                         "Яндекс оставляет в индексе старый адрес, пока редирект временный.",
                         "Если переезд навсегда – используйте 301.", u, f"{r['chain'][0][0]} → {r['final']}")
            if not self.same_host(r["final"]):
                return []
        if r["status"] >= 400:
            sev = "critical" if r["status"] >= 500 else "important"
            self.add(f"http-{r['status'] // 100}xx", sev, f"Страницы отвечают кодом {r['status'] // 100}xx",
                     "Робот получает ошибку. 5xx – сигнал, что сервер сломан (URL_ALERT_5XX), 4xx на страницах, "
                     "на которые есть ссылки, – битые ссылки (URL_ALERT_4XX).",
                     "Почините страницу или уберите на неё ссылки и уберите её из карты сайта.", u, str(r["status"]))
            return []
        ctype = r["headers"].get("content-type", "")
        if "html" not in ctype:
            return []
        doc = text_of(r)
        info["bytes"] = len(r["body"])
        P = Page()
        try:
            P.feed(doc)
        except Exception:
            pass
        title = " ".join((P.title or "").split())
        desc = " ".join((P.meta(name="description") or "").split())
        robots_meta = ",".join(filter(None, [(P.meta(name="robots") or ""), (P.meta(name="yandex") or ""),
                                             r["headers"].get("x-robots-tag", "")])).lower()
        noindex = "noindex" in robots_meta or "none" in robots_meta.split(",")
        canon = [l.get("href", "") for l in P.link_rel("canonical")]
        text = " ".join(" ".join(P.text).split())
        words = CYR_WORD.findall(text)
        info.update(title=title, desc=desc, noindex=noindex, canonical=canon[0] if canon else None,
                    words=len(words), text_hash=hashlib.md5(text.encode()).hexdigest() if len(text) > 200 else None)
        in_sm = u in self.sitemap_urls

        # индексация
        if noindex:
            if in_sm:
                self.add("noindex-in-sitemap", "important", "Страница в карте сайта закрыта noindex",
                         "Карта просит проиндексировать, мета-тег запрещает – Яндекс считает это ошибкой карты.",
                         "Уберите страницу из карты или снимите noindex.", u)
            else:
                self.add("noindex", "info", "Страницы закрыты от индексации (noindex)",
                         "Проверьте, что это сделано намеренно (корзина, личный кабинет, поиск).",
                         "Если страница не должна быть в поиске, всё верно.", u)
        if len(canon) > 1:
            self.add("canonical-multi", "important", "Несколько rel=canonical на странице",
                     "Яндекс игнорирует canonical, если их несколько.", "Оставьте один.", u)
        if canon:
            c = urllib.parse.urljoin(u, canon[0])
            if not canon[0].startswith("http"):
                self.add("canonical-relative", "advice", "rel=canonical с относительным адресом",
                         "Яндекс рекомендует полный адрес с протоколом и доменом.", "Пишите canonical полностью.", u)
            if norm(c) != norm(u):
                info["canonical_other"] = norm(c)
                if in_sm:
                    self.add("canonical-in-sitemap", "important", "В карте сайта неканонические страницы",
                             "Страница указывает canonical на другой адрес, а в карте стоит она сама. Яндекс исключит "
                             "её как NOT_CANONICAL.", "В карте должны быть только канонические адреса.", u, c)
        elif not noindex:
            self.add("canonical-missing", "advice", "Нет rel=canonical",
                     "Без canonical дубли с метками и параметрами Яндекс склеивает сам и не всегда в пользу нужного адреса.",
                     "Добавьте <link rel=\"canonical\" href=\"полный адрес страницы\">.", u)

        if not noindex:
            # заголовок и описание
            if not title:
                self.add("title-missing", "critical", "Нет заголовка <title>",
                         "Без title Яндекс собирает заголовок сниппета сам (DOCUMENTS_MISSING_TITLE).",
                         "Напишите уникальный title со смыслом страницы и главным запросом.", u)
            elif len(title) > 70:
                self.add("title-long", "advice", "Заголовок длиннее 70 знаков",
                         "В выдаче Яндекса видно примерно 55-70 знаков, хвост обрезается.",
                         "Главное слово и запрос – в начале заголовка.", u, f"{len(title)}: {title[:90]}")
            elif len(title) < 15:
                self.add("title-short", "advice", "Заголовок короче 15 знаков",
                         "Слишком короткий title не описывает страницу и не содержит запросов.",
                         "Добавьте суть страницы и регион или тип товара.", u, title)
            if not desc:
                self.add("desc-missing", "important", "Нет meta description",
                         "Яндекс берёт описание для сниппета из description; без него – случайный кусок текста. "
                         "В Вебмастере это DOCUMENTS_MISSING_DESCRIPTION.",
                         "Напишите 1-2 предложения о странице, до 160 знаков.", u)
            elif len(desc) > 200:
                self.add("desc-long", "advice", "meta description длиннее 200 знаков",
                         "Яндекс показывает около 160 знаков.", "Сократите, главное – в начало.", u, f"{len(desc)} знаков")
            h1 = [t for h, t in P.headings if h == "h1"]
            if not h1:
                self.add("h1-missing", "important", "Нет заголовка H1",
                         "H1 – главный заголовок для робота и для человека.", "Добавьте один H1 со смыслом страницы.", u)
            elif len(h1) > 1:
                self.add("h1-multi", "advice", "Несколько H1 на странице",
                         "Робот хуже понимает, о чём страница.", "Оставьте один H1, остальные – H2.", u,
                         " | ".join(h1[:3])[:150])
            if len(words) < 80 and not re.search(r"/(cart|basket|korzina|checkout|login|account|search)", u):
                self.add("thin", "advice", "Мало текста на странице (меньше 80 слов)",
                         "Почти пустые страницы Яндекс может исключить как малоценные (LOW_QUALITY).",
                         "Добавьте полезный текст или закройте страницу от индексации.", u, f"{len(words)} слов")

        # телефон и разметка
        if not any(m.get("name", "").lower() == "viewport" for m in P.metas):
            self.add("viewport", "important", "Нет meta viewport",
                     "Без него страница не адаптирована для телефона (NOT_MOBILE_FRIENDLY), а это больше половины поиска Яндекса.",
                     'Добавьте <meta name="viewport" content="width=device-width, initial-scale=1">.', u)
        if not P.lang:
            self.add("lang", "advice", "Нет атрибута lang у <html>",
                     "Язык страницы помогает роботу и экранным читалкам.", 'Укажите <html lang="ru">.', u)
        types, objs = ld_types(P.jsonld)
        if None in types:
            self.add("jsonld-invalid", "important", "Ошибка в JSON-LD разметке",
                     "Блок с ошибкой JSON Яндекс пропускает целиком.",
                     "Проверьте разметку валидатором Вебмастера: Инструменты → Валидатор микроразметки.", u)
        info["types"] = sorted(set(t for t in types if t))
        for t, o in objs:
            if t == "Product":
                offers = o.get("offers")
                if not offers:
                    self.add("product-no-offer", "important", "Разметка Product без offers (цены)",
                             "Без цены и наличия Яндекс не покажет товарный сниппет и не возьмёт товар в «Товары».",
                             "Добавьте offers: price, priceCurrency (RUB), availability.", u)
                else:
                    off = offers[0] if isinstance(offers, list) and offers else offers
                    if isinstance(off, dict) and not (off.get("price") or off.get("lowPrice")):
                        self.add("product-no-price", "important", "В разметке Product нет цены",
                                 "Товарный сниппет и «Товары» Яндекса требуют цену.", "Заполните offers.price.", u)
        if not P.meta(prop="og:title") and not noindex:
            self.add("og-missing", "advice", "Нет Open Graph (og:title, og:image)",
                     "По Open Graph Яндекс строит карточки ссылок в Мессенджере, Дзене и соцсетях.",
                     "Добавьте og:title, og:description, og:image (от 600 px), og:url.", u)
        elif not P.meta(prop="og:image") and not noindex:
            self.add("og-image", "advice", "Нет og:image", "Ссылка на страницу будет без картинки.",
                     "Добавьте og:image с полным адресом картинки.", u)

        # Метрика, смешанный контент, картинки
        html_low = doc.lower()
        m = re.findall(r"ym\(\s*(\d{5,10})\s*,\s*['\"]init", doc) or re.findall(r"mc\.yandex\.ru/watch/(\d+)", doc)
        if m:
            info["metrika"] = m[0]
        elif "mc.yandex.ru/metrika" not in html_low:
            self.add("metrika-missing", "important", "Нет счётчика Яндекс Метрики",
                     "Без Метрики Яндекс не видит поведение посетителей, а Вебмастер – обход по счётчику "
                     "(NO_METRIKA_COUNTER_CRAWL_ENABLED). Это ещё и потеря аналитики.",
                     "Поставьте счётчик на все страницы и свяжите его с сайтом в Вебмастере.", u)
        if P.mixed and self.scheme == "https":
            self.add("mixed-content", "important", "Смешанный контент: http-ресурсы на https-странице",
                     "Браузер блокирует такие картинки и скрипты, Яндекс может посчитать страницу небезопасной.",
                     "Замените адреса на https.", u, P.mixed[0][:150])
        no_alt = [i.get("src", "")[:120] for i in P.imgs if "alt" not in i]
        if no_alt:
            self.add("img-alt", "advice", "Картинки без alt",
                     "Для Яндекс Картинок и для людей с экранными читалками alt – единственное описание картинки.",
                     "Опишите картинку в alt; для декоративных – alt=\"\".", u, f"{len(no_alt)} шт., напр. {no_alt[0]}")
        if P.noindex_tags:
            info["noindex_tags"] = P.noindex_tags
        if info.get("bytes", 0) > 2 * 1024 * 1024:
            self.add("html-heavy", "advice", "HTML страницы больше 2 МБ",
                     "Тяжёлая страница медленно грузится, а робот может прочитать её не до конца.",
                     "Уберите встроенные картинки base64, лишние стили и скрипты.", u, f"{info['bytes'] // 1024} КБ")

        # ссылки
        out = []
        for a in P.anchors:
            href = a.get("href", "").strip()
            if not href or href.startswith(("#", "mailto:", "tel:", "javascript:", "sms:", "whatsapp:", "tg:", "viber:")):
                continue
            full = norm(urllib.parse.urljoin(r["final"], href))
            if not full.startswith(("http://", "https://")) or not self.same_host(full):
                continue
            if re.search(r"\.(jpe?g|png|gif|webp|svg|pdf|zip|docx?|xlsx?|mp4|mp3)$", urllib.parse.urlsplit(full).path, re.I):
                continue
            self.inlinks[full].add(u)
            if "nofollow" in a.get("rel", "").lower():
                self.add("internal-nofollow", "advice", "Внутренние ссылки с nofollow",
                         "Яндекс не передаёт по ним вес; внутри сайта это обычно ошибка.", "Уберите rel=nofollow с внутренних ссылок.",
                         u, full)
            out.append(full)
        return out

    # -- шаг 4: итоги по всем страницам
    def site_wide(self):
        ok_pages = {u: p for u, p in self.pages.items() if p.get("status") == 200 and not p.get("redirect") and "title" in p}
        idx = {u: p for u, p in ok_pages.items() if not p.get("noindex") and not p.get("canonical_other")}
        for field, fid, title, why in (
                ("title", "title-dup", "Одинаковые заголовки на разных страницах",
                 "Для Яндекса страницы с одинаковым title – похожие на дубли (DUPLICATE_CONTENT_ATTRS)."),
                ("desc", "desc-dup", "Одинаковые description на разных страницах",
                 "Одинаковые описания – признак дублей и шаблонных страниц (DUPLICATE_CONTENT_ATTRS).")):
            groups = defaultdict(list)
            for u, p in idx.items():
                if p.get(field):
                    groups[p[field]].append(u)
            dups = {k: v for k, v in groups.items() if len(v) > 1}
            for k, v in sorted(dups.items(), key=lambda x: -len(x[1]))[:8]:
                self.add(fid, "important", title, why, "Сделайте заголовки и описания уникальными.", v[0],
                         f"{len(v)} стр.: «{k[:80]}» – {', '.join(v[:3])}")
            if dups:
                self.findings[fid]["count"] = sum(len(v) for v in dups.values())
        hashes = defaultdict(list)
        for u, p in idx.items():
            if p.get("text_hash"):
                hashes[p["text_hash"]].append(u)
        dup_txt = [v for v in hashes.values() if len(v) > 1]
        for v in dup_txt[:8]:
            self.add("content-dup", "important", "Страницы с одинаковым текстом",
                     "Яндекс оставит в поиске одну, остальные исключит как дубли (DUPLICATE_PAGES).",
                     "Склейте дубли 301-редиректом или canonical, или сделайте текст разным.", v[0], ", ".join(v[:4]))
        # битые внутренние ссылки
        for target, sources in self.inlinks.items():
            st = self.status.get(target)
            if st and st >= 400:
                self.add("broken-links", "important", "Битые внутренние ссылки",
                         "Ссылки ведут на страницы с ошибкой: робот тратит обход, посетитель упирается в ошибку.",
                         "Исправьте или уберите ссылки.", target, f"{st}, ссылается: {', '.join(sorted(sources)[:3])}")
            elif self.pages.get(target, {}).get("redirect"):
                self.add("links-to-redirect", "advice", "Внутренние ссылки ведут на редирект",
                         "Лишний шаг для робота и посетителя.", "Ставьте в ссылках конечный адрес.", target,
                         f"→ {self.pages[target].get('final')}, ссылается: {', '.join(sorted(sources)[:2])}")
        # страницы из карты, на которые нет ссылок
        if self.sitemap_urls and self.meta.get("pages_crawled", 0) >= len(self.sitemap_urls):
            orphans = [u for u in self.sitemap_urls if u in ok_pages and not self.inlinks.get(u) and u != norm(self.root)]
            for u in orphans[:8]:
                self.add("orphans", "advice", "Страницы из карты сайта без внутренних ссылок",
                         "Робот находит их только через карту, вес на них не передаётся.",
                         "Поставьте ссылки из меню, разделов или похожих страниц.", u)
            if orphans:
                self.findings["orphans"]["count"] = len(orphans)
        # Метрика: разные счётчики
        counters = Counter(p.get("metrika") for p in ok_pages.values() if p.get("metrika"))
        if len(counters) > 1:
            self.add("metrika-many", "advice", "На страницах разные счётчики Метрики",
                     "Статистика рассыпается по счётчикам.", "Проверьте, что везде стоит один счётчик сайта.", None,
                     ", ".join(f"{k}: {v} стр." for k, v in counters.most_common(4)))
        elif counters:
            self.ok(f"Счётчик Метрики {next(iter(counters))} на {sum(counters.values())} страницах")
        self.meta["metrika"] = list(counters)
        # скорость ответа
        times = sorted(p["time"] for p in ok_pages.values() if "time" in p)
        if times:
            avg = sum(times) / len(times)
            self.meta["avg_response_s"] = round(avg, 2)
            if avg > 2:
                self.add("slow", "important" if avg > 3 else "advice", f"Медленный ответ сервера: в среднем {avg:.1f} с",
                         "Яндекс отмечает медленный сайт в Вебмастере (SLOW_AVG_RESPONSE_TIME) и реже обходит его.",
                         "Включите кеширование страниц, проверьте хостинг.", None)
            else:
                self.ok(f"Сервер отвечает в среднем за {avg:.2f} с")
        # главная: подтверждение Вебмастера, большой фавикон, разметка организации
        home = self.pages.get(norm(self.root), {})
        types = set(home.get("types", []))
        if not types & {"Organization", "LocalBusiness", "Store", "OnlineStore", "WebSite"} and home.get("status") == 200:
            self.add("org-schema", "advice", "На главной нет разметки Organization / LocalBusiness",
                     "Разметка организации помогает Яндексу связать сайт с карточкой в Яндекс Бизнесе и Картах.",
                     "Добавьте JSON-LD Organization (или LocalBusiness) с названием, адресом, телефоном, логотипом.", self.root)
        self.meta["home_types"] = sorted(types)

    def favicon_check(self):
        r = fetch(self.root, timeout=self.args.timeout)
        if r["status"] != 200:
            return
        P = Page()
        try:
            P.feed(text_of(r))
        except Exception:
            pass
        icons = [l for l in P.links if "icon" in l.get("rel", "").lower()]
        big = [l for l in icons if l.get("type", "").endswith("svg+xml") or l.get("href", "").endswith(".svg") or
               any(int(x) >= 120 for x in re.findall(r"(\d+)x\d+", l.get("sizes", "")) if x.isdigit())]
        if not icons and self.meta.get("favicon_ico") != 200:
            self.add("favicon", "important", "Нет фавикона",
                     "Яндекс показывает фавикон рядом с сайтом в выдаче; без него – пустой значок (FAVICON_ERROR).",
                     "Добавьте <link rel=\"icon\" href=\"/favicon.svg\" type=\"image/svg+xml\"> и /favicon.ico.", self.root)
        elif not big:
            self.add("favicon-big", "advice", "Нет фавикона 120×120 или SVG",
                     "Яндекс рекомендует SVG или PNG от 120×120: маленький значок в выдаче выглядит размыто (BIG_FAVICON_ABSENT).",
                     "Добавьте <link rel=\"icon\" href=\"/favicon-120.png\" sizes=\"120x120\"> или SVG.", self.root)
        else:
            self.ok("Фавикон крупного размера или SVG есть")
        if not P.meta(name="yandex-verification"):
            self.add("ya-verification", "info", "На главной нет мета-тега yandex-verification",
                     "Если права в Вебмастере подтверждены файлом или DNS, это нормально.",
                     "Проверьте, что сайт добавлен и подтверждён в webmaster.yandex.ru.", self.root)

    def params_check(self):
        """Дубли с метками: адрес с utm должен склеиваться canonical или Clean-param."""
        sample = [u for u, p in self.pages.items() if p.get("status") == 200 and not p.get("redirect") and "title" in p][:3]
        cp = self.robots.clean_param_names()
        for u in sample:
            test = u + ("&" if "?" in u else "?") + "utm_source=yaudit"
            r = fetch(test, timeout=self.args.timeout)
            if r["status"] != 200:
                continue
            P = Page()
            try:
                P.feed(text_of(r))
            except Exception:
                pass
            canon = [l.get("href", "") for l in P.link_rel("canonical")]
            c = norm(urllib.parse.urljoin(u, canon[0])) if canon else None
            if c != norm(u) and "utm_source" not in cp:
                self.add("utm-dup", "important", "Адреса с метками utm – дубли страниц",
                         "Страница с ?utm_source=… отвечает 200 без canonical на чистый адрес, а Clean-param для utm нет. "
                         "Яндекс может проиндексировать копии с метками из рекламы и рассылок.",
                         "Добавьте canonical на чистый адрес и Clean-param: utm_source&utm_medium&utm_campaign в robots.txt.", test)
                break
        # слеш в конце
        for u in sample:
            p = urllib.parse.urlsplit(u)
            if p.query or p.path == "/":
                continue
            alt_path = p.path[:-1] if p.path.endswith("/") else p.path + "/"
            alt = urllib.parse.urlunsplit((p.scheme, p.netloc, alt_path, "", ""))
            r = fetch(alt, timeout=self.args.timeout, follow=False)
            if r["status"] == 200:
                P = Page()
                try:
                    P.feed(text_of(r))
                except Exception:
                    pass
                canon = [l.get("href", "") for l in P.link_rel("canonical")]
                if not canon or norm(urllib.parse.urljoin(alt, canon[0])) != norm(u):
                    self.add("slash-dup", "important", "Адрес со слешем и без слеша – две страницы",
                             f"{u} и {alt} оба отвечают 200 без canonical друг на друга – для Яндекса это дубли.",
                             "Поставьте 301 с одного варианта на другой.", alt)
                break

    def bot_vs_browser(self):
        """Робот Яндекса и обычный браузер должны получать одно и то же."""
        sample = [norm(self.root)] + [u for u, p in self.pages.items() if p.get("status") == 200][:4]
        for u in dict.fromkeys(sample):
            a = fetch(u, ua=YANDEX_UA, timeout=self.args.timeout)
            b = fetch(u, ua=BROWSER_UA, timeout=self.args.timeout)
            if a["status"] and b["status"] and a["status"] != b["status"]:
                self.add("bot-differs", "critical", "Робот Яндекса получает другой ответ, чем браузер",
                         f"Браузер: {b['status']}, YandexBot: {a['status']}. Защита от ботов или настройки сервера "
                         "отсекают робота – страницы выпадут из поиска. Это бывает с антиботами, CDN и файрволами.",
                         "Разрешите YandexBot в защите от ботов (проверка подлинности – обратный DNS на yandex.ru/.net/.com).",
                         u)

    # -- данные Вебмастера
    def webmaster(self):
        token = os.environ.get("YANDEX_WEBMASTER_TOKEN") or os.environ.get("YANDEX_OAUTH_TOKEN")
        if not token:
            self.meta["webmaster"] = "нет токена (YANDEX_WEBMASTER_TOKEN)"
            return
        api = "https://api.webmaster.yandex.net/v4"

        def get(path):
            r = fetch(api + path, ua="yaudit/" + VERSION, timeout=40, headers={"Authorization": "OAuth " + token,
                                                                                 "Accept": "application/json"})
            if r["status"] != 200:
                raise RuntimeError(f"{path}: {r['status'] or r['error']} {r['body'][:200]!r}")
            return json.loads(r["body"])
        try:
            uid = get("/user")["user_id"]
            hosts = get(f"/user/{uid}/hosts")["hosts"]
            bare = self.host[4:] if self.host.startswith("www.") else self.host
            host = next((h for h in hosts if h.get("ascii_host_url", "").rstrip("/").split("://")[-1] in (self.host, bare)
                         and h.get("verified")), None)
            if not host:
                self.meta["webmaster"] = "сайт не найден среди подтверждённых в Вебмастере"
                return
            hid = urllib.parse.quote(host["host_id"], safe=":")
            base = f"/user/{uid}/hosts/{hid}"
            wm = {"host": host["host_id"]}
            s = get(base + "/summary")
            wm.update(sqi=s.get("sqi"), searchable=s.get("searchable_pages_count"), excluded=s.get("excluded_pages_count"))
            diag = get(base + "/diagnostics").get("problems", {})
            wm["problems"] = {k: v["severity"] for k, v in diag.items() if v.get("state") == "PRESENT"}
            for code, sev in wm["problems"].items():
                title, fix = WM_PROBLEMS.get(code, (code, "Подробности – в Вебмастере: Диагностика."))
                self.add("wm-" + code, {"FATAL": "critical", "CRITICAL": "critical", "POSSIBLE_PROBLEM": "important"}.get(sev, "advice"),
                         "Вебмастер: " + title, f"Яндекс сам отметил проблему на сайте ({code}, {sev}).", fix, None)
            try:
                sm = get(base + "/sitemaps").get("sitemaps", [])
                wm["sitemaps"] = [(x["sitemap_url"], x.get("errors_count"), x.get("last_access_date", "")[:10]) for x in sm]
                for url, errs, _ in wm["sitemaps"]:
                    if errs:
                        self.add("wm-sitemap-errors", "important", "Вебмастер: ошибки в карте сайта",
                                 f"В {url} Яндекс нашёл ошибок: {errs}.", "Откройте Индексирование → Файлы Sitemap.", url)
            except Exception as e:
                wm["sitemaps_error"] = str(e)[:120]
            try:
                br = get(base + "/links/internal/broken/samples?limit=100")
                wm["broken_internal"] = br.get("count", 0)
                def shape(u):
                    segs = urllib.parse.urlsplit(u).path.strip("/").split("/")
                    return ("…/" + segs[-1] + "/") if len(segs) > 1 else "/" + segs[0]
                pat = Counter(shape(x["destination_url"]) for x in br.get("links", []))
                for x in br.get("links", [])[:8]:
                    self.add("wm-broken-links", "important", f"Вебмастер: битые внутренние ссылки ({br.get('count')})",
                             "Яндекс находит на сайте ссылки на несуществующие страницы.",
                             "Посмотрите шаблон адресов ниже – часто это ссылки, которые вставляет движок (/feed/, ?replytocom=, /page/N/).",
                             x["destination_url"], f"со страницы {x['source_url']}")
                wm["broken_patterns"] = pat.most_common(5)
                if br.get("links"):
                    self.findings["wm-broken-links"]["count"] = br.get("count", 0)
            except Exception as e:
                wm["broken_error"] = str(e)[:120]
            try:
                ev = get(base + "/search-urls/events/samples?limit=100").get("samples", [])
                reasons = Counter(x.get("excluded_url_status") or x.get("bad_http_status") for x in ev if x.get("event") == "REMOVED_FROM_SEARCH")
                wm["removed_reasons"] = dict(reasons)
                for x in ev:
                    if x.get("event") == "REMOVED_FROM_SEARCH":
                        st = x.get("excluded_url_status") or str(x.get("bad_http_status"))
                        title, fix = WM_EXCLUDED.get(st, (st, "Подробности – в Вебмастере: Страницы в поиске → Исключённые."))
                        self.add("wm-excluded-" + str(st), "important" if st in ("LOW_QUALITY", "HTTP_ERROR", "DUPLICATE") else "advice",
                                 "Вебмастер: страницы исключены из поиска – " + title,
                                 "Яндекс недавно убрал эти страницы из поиска (выборка последних событий).", fix, x.get("url"))
            except Exception as e:
                wm["events_error"] = str(e)[:120]
            try:
                to = time.strftime("%Y-%m-%d", time.gmtime(time.time() - 3 * 86400))
                fr = time.strftime("%Y-%m-%d", time.gmtime(time.time() - 33 * 86400))
                q = get(base + f"/search-queries/popular?order_by=TOTAL_SHOWS&query_indicator=TOTAL_SHOWS&query_indicator=TOTAL_CLICKS"
                               f"&query_indicator=AVG_SHOW_POSITION&date_from={fr}&date_to={to}&limit=20")
                wm["queries"] = [(x["query_text"], int(x["indicators"].get("TOTAL_SHOWS") or 0), int(x["indicators"].get("TOTAL_CLICKS") or 0),
                                  round(x["indicators"].get("AVG_SHOW_POSITION") or 0, 1)) for x in q.get("queries", [])]
                wm["queries_period"] = f"{fr} – {to}"
            except Exception as e:
                wm["queries_error"] = str(e)[:120]
            self.meta["webmaster"] = wm
        except Exception as e:
            self.meta["webmaster"] = f"ошибка API: {e}"[:300]

    # -- орфография
    def speller(self):
        lines = defaultdict(set)
        # тексты перечитываем заново: при обходе в памяти держим только хеш текста
        urls = [u for u, p in self.pages.items() if p.get("status") == 200 and "title" in p and not p.get("noindex")][: self.args.speller_pages]
        self.log(f"орфография: {len(urls)} страниц")
        for u in urls:
            r = fetch(u, timeout=self.args.timeout)
            P = Page()
            try:
                P.feed(text_of(r))
            except Exception:
                continue
            for chunk in re.split(r"[\n\r]+|(?<=[.!?])\s+", " \n".join(P.text)):
                c = " ".join(chunk.split())
                if len(CYR_WORD.findall(c)) >= 2:
                    lines[c].add(u)
        uniq = list(lines)
        found = defaultdict(lambda: {"s": set(), "pages": set(), "ex": ""})
        batch, size = [], 0
        def flush(batch):
            data = urllib.parse.urlencode([("text", t) for t in batch] + [("lang", "ru,en"), ("options", "14")]).encode()
            r = fetch("https://speller.yandex.net/services/spellservice.json/checkTexts", method="POST", data=data,
                      headers={"Content-Type": "application/x-www-form-urlencoded"}, timeout=40, ua="yaudit/" + VERSION)
            if r["status"] != 200:
                return
            for t, errs in zip(batch, json.loads(r["body"])):
                for e in errs:
                    w = e.get("word", "")
                    if not w or w[0].isupper() or re.search(r"[A-Za-z0-9]", w):
                        continue  # имена, названия, латиница
                    if e.get("s") and all(x.replace("ё", "е") == w.replace("ё", "е") for x in e["s"][:1]):
                        continue  # только ё/е
                    f = found[w]
                    f["s"].update(e.get("s", [])[:3])
                    f["pages"].update(lines[t])
                    f["ex"] = f["ex"] or t[:120]
        for t in uniq:
            if size + len(t) > 9000 or len(batch) >= 50:
                flush(batch)
                batch, size = [], 0
            batch.append(t)
            size += len(t)
        if batch:
            flush(batch)
        for w, f in sorted(found.items(), key=lambda x: -len(x[1]["pages"]))[:60]:
            self.add("spell", "advice", "Возможные опечатки (Яндекс Спеллер)",
                     "Ошибки в тексте снижают доверие посетителей; Спеллер ошибается на терминах и названиях – проверьте глазами.",
                     "Исправьте настоящие опечатки, термины оставьте.", sorted(f["pages"])[0],
                     f"«{w}» → {', '.join(sorted(f['s'])[:3]) or '?'} ({len(f['pages'])} стр.): …{f['ex'][:90]}…")
        self.meta["speller_words"] = len(found)

    # -- YML-фид
    def yml(self, url):
        r = fetch(url, timeout=60)
        if r["status"] != 200:
            self.add("yml-down", "critical", "YML-фид не открывается", f"Ответ {r['status'] or r['error']}.",
                     "Без фида товары выпадут из Яндекс Маркета и «Товаров».", url)
            return
        try:
            root = ET.fromstring(r["body"])
        except Exception as e:
            self.add("yml-xml", "critical", "YML-фид – не XML", str(e)[:150], "Проверьте фид в кабинете Маркета.", url)
            return
        offers = root.findall(".//offer")
        miss = Counter()
        foreign = 0
        for o in offers:
            for tag in ("url", "price", "currencyId", "categoryId", "picture"):
                if o.find(tag) is None or not (o.find(tag).text or "").strip():
                    miss[tag] += 1
            if o.find("name") is None and o.find("model") is None:
                miss["name"] += 1
            u = o.find("url")
            if u is not None and u.text and not self.same_host(u.text.strip()):
                foreign += 1
            p = o.find("price")
            try:
                if p is not None and float((p.text or "0").replace(",", ".")) <= 0:
                    miss["price>0"] += 1
            except ValueError:
                miss["price>0"] += 1
        self.meta["yml"] = {"offers": len(offers), "categories": len(root.findall(".//category")), "missing": dict(miss)}
        for tag, n in miss.items():
            self.add("yml-" + tag, "important" if tag in ("url", "price", "price>0", "name") else "advice",
                     f"YML: у товаров нет поля {tag}", f"{n} из {len(offers)} предложений без {tag}.",
                     "Товары без обязательных полей Маркет не принимает; без картинки – хуже показ.", url)
        if foreign:
            self.add("yml-foreign", "important", "YML: ссылки на товары другого домена",
                     f"{foreign} предложений ведут не на {self.host}.", "Ссылки должны вести на главное зеркало.", url)
        if offers and not miss:
            self.ok(f"YML-фид: {len(offers)} товаров, обязательные поля на месте")

    # -- запуск
    def run(self):
        self.site_checks()
        self.sitemaps()
        self.crawl()
        self.site_wide()
        self.favicon_check()
        self.params_check()
        self.bot_vs_browser()
        if self.args.webmaster:
            self.log("Яндекс Вебмастер…")
            self.webmaster()
        if self.args.speller:
            self.speller()
        if self.args.yml:
            self.log("YML-фид…")
            self.yml(self.args.yml)
        self.meta["seconds"] = round(time.time() - self.started)
        return self.result()

    def result(self):
        fs = sorted(self.findings.values(), key=lambda f: (SEV_ORDER[f["sev"]], -f["count"]))
        return {"tool": "yaudit", "version": VERSION, "site": self.root,
                "date": time.strftime("%Y-%m-%d %H:%M", time.localtime()), "meta": self.meta,
                "summary": dict(Counter(f["sev"] for f in fs)), "findings": fs, "passed": self.passed}


# ---------------------------------------------------------------- справочники Вебмастера

WM_PROBLEMS = {
    "DNS_ERROR": ("ошибка DNS", "Проверьте записи домена у регистратора."),
    "CONNECT_FAILED": ("сервер не отвечает", "Проверьте хостинг и защиту от ботов."),
    "MAIN_PAGE_ERROR": ("главная отдаёт ошибку", "Главная должна отвечать 200."),
    "DISALLOWED_IN_ROBOTS": ("сайт закрыт в robots.txt", "Уберите Disallow: / для Яндекса."),
    "THREATS": ("угрозы безопасности (вирус, фишинг)", "Вебмастер → Диагностика → Безопасность и нарушения."),
    "SLOW_AVG_RESPONSE_TIME": ("медленный ответ сервера", "Кеширование страниц, более быстрый хостинг."),
    "URL_ALERT_5XX": ("страницы отвечают 5xx", "Вебмастер → Мониторинг важных страниц / Статистика обхода."),
    "URL_ALERT_4XX": ("важные страницы отвечают 4xx", "Почините страницы или уберите их из важных."),
    "NO_SITEMAPS": ("нет карты сайта", "Добавьте sitemap.xml в Вебмастер и robots.txt."),
    "ERRORS_IN_SITEMAPS": ("ошибки в карте сайта", "Индексирование → Файлы Sitemap."),
    "NO_SITEMAP_MODIFICATIONS": ("карта сайта давно не менялась", "Проверьте, что карта обновляется при новых страницах."),
    "SOFT_404": ("несуществующие страницы отвечают 200", "Отдавайте код 404 на несуществующие адреса."),
    "DUPLICATE_PAGES": ("много страниц-дублей", "Склейте дубли 301 или canonical, Clean-param для параметров."),
    "DUPLICATE_CONTENT_ATTRS": ("одинаковые title и description", "Сделайте их уникальными."),
    "DOCUMENTS_MISSING_TITLE": ("страницы без title", "Добавьте title."),
    "DOCUMENTS_MISSING_DESCRIPTION": ("страницы без description", "Добавьте meta description на страницы из примеров в Вебмастере."),
    "MAIN_MIRROR_IS_NOT_HTTPS": ("главное зеркало не https", "301 с http на https и смена зеркала в Вебмастере."),
    "MAIN_PAGE_REDIRECTS": ("главная перенаправляет", "Главная должна отвечать 200."),
    "NO_ROBOTS_TXT": ("нет robots.txt", "Положите robots.txt в корень."),
    "ERROR_IN_ROBOTS_TXT": ("ошибки в robots.txt", "Инструменты → Анализ robots.txt."),
    "FAVICON_ERROR": ("фавикон не загружается", "Проверьте адрес и формат фавикона."),
    "FAVICON_PROBLEM": ("проблема с фавиконом", "Проверьте фавикон в Вебмастере."),
    "BIG_FAVICON_ABSENT": ("нет крупного фавикона", "Добавьте SVG или PNG от 120×120."),
    "NO_METRIKA_COUNTER_BINDING": ("Метрика не привязана к сайту", "Вебмастер → Настройки → Привязка к Метрике."),
    "NO_METRIKA_COUNTER_CRAWL_ENABLED": ("обход по счётчику Метрики выключен", "Индексирование → Обход по счётчикам."),
    "NOT_MOBILE_FRIENDLY": ("страницы не оптимизированы для телефона", "Инструменты → Проверка мобильных страниц."),
    "NOT_IN_SPRAV": ("сайт не связан с организацией в Яндекс Бизнесе", "Добавьте сайт в карточку организации."),
    "NO_REGIONS": ("не задан регион сайта", "Представление в поиске → Региональность."),
    "INSIGNIFICANT_CGI_PARAMETER": ("в адресах лишние параметры", "Добавьте Clean-param в robots.txt."),
    "TOO_MANY_DOMAINS_ON_SEARCH": ("в поиске много поддоменов", "Проверьте, нужны ли поддомены в поиске."),
    "VIDEOHOST_OFFER_FAILED": ("ошибка оферты видеохостинга", "Вебмастер → Видео."),
    "VIDEOHOST_OFFER_NEED_PAPER": ("нужны документы видеохостинга", "Вебмастер → Видео."),
}
WM_EXCLUDED = {
    "LOW_QUALITY": ("малоценная или маловостребованная страница", "Добавьте полезный текст, фото, цены, отзывы; пустые страницы закройте noindex."),
    "NOT_CANONICAL": ("неканоническая (canonical на другой адрес)", "Если страница нужна в поиске – canonical на себя."),
    "DUPLICATE": ("дубль другой страницы", "Сделайте страницу уникальной или склейте 301."),
    "HTTP_ERROR": ("ошибка HTTP при обходе", "Проверьте код ответа страницы."),
    "REDIRECT_NOTSEARCHABLE": ("редирект", "Нормально, если адрес переехал."),
    "META_NO_INDEX": ("закрыта noindex", "Проверьте, что это намеренно."),
    "ROBOTS_TXT_ERROR": ("закрыта в robots.txt", "Проверьте, что это намеренно."),
    "CLEAN_PARAMS": ("склеена по Clean-param", "Нормально для адресов с метками."),
}

# ---------------------------------------------------------------- отчёт


def to_markdown(res):
    m, s = res["meta"], res["summary"]
    L = [f"# Аудит под Яндекс: {res['site']}", "",
         f"{res['date']} · yaudit {res['version']} · страниц обойдено: {m.get('pages_crawled', 0)} · "
         f"в карте сайта: {m.get('sitemap_urls', 0)} · средний ответ: {m.get('avg_response_s', '?')} с · {m.get('seconds')} с", "",
         f"**Критично: {s.get('critical', 0)} · Важно: {s.get('important', 0)} · Желательно: {s.get('advice', 0)} · "
         f"К сведению: {s.get('info', 0)}**", ""]
    wm = m.get("webmaster")
    if isinstance(wm, dict):
        L += ["## Яндекс Вебмастер", "",
              f"ИКС: {wm.get('sqi')} · страниц в поиске: {wm.get('searchable')} · исключено: {wm.get('excluded')}"]
        if wm.get("problems"):
            L.append("Проблемы в диагностике: " + ", ".join(f"{WM_PROBLEMS.get(k, (k,))[0]} ({v})" for k, v in wm["problems"].items()))
        if wm.get("broken_internal"):
            L.append(f"Битых внутренних ссылок по данным Яндекса: {wm['broken_internal']}; частые адреса: "
                     + ", ".join(f"{p} ({n})" for p, n in wm.get("broken_patterns", [])))
        if wm.get("removed_reasons"):
            L.append("Причины недавних исключений: " + ", ".join(f"{WM_EXCLUDED.get(k, (k,))[0]}: {v}" for k, v in wm["removed_reasons"].items()))
        if wm.get("queries"):
            L += ["", f"Популярные запросы ({wm.get('queries_period')}):", "", "| Запрос | Показы | Клики | Позиция |", "|---|---|---|---|"]
            L += [f"| {q} | {sh} | {cl} | {pos} |" for q, sh, cl, pos in wm["queries"][:15]]
        L.append("")
    elif wm:
        L += [f"_Вебмастер: {wm}_", ""]
    for sev in ("critical", "important", "advice", "info"):
        fs = [f for f in res["findings"] if f["sev"] == sev]
        if not fs:
            continue
        L += [f"## {SEV_TITLE[sev]}", ""]
        for f in fs:
            L += [f"### {f['title']}" + (f" – {f['count']}" if f["count"] > 1 else ""), "",
                  f"**Почему:** {f['why']}", "", f"**Что сделать:** {f['fix']}", ""]
            ex = f["extra"] or []
            for i, u in enumerate(f["urls"][:5]):
                L.append(f"- {u}" + (f" – {ex[i]}" if i < len(ex) and ex[i] else ""))
            if not f["urls"] and ex:
                L += [f"- {x}" for x in ex[:5]]
            L.append("")
    if res["passed"]:
        L += ["## В порядке", ""] + [f"- {p}" for p in res["passed"]] + [""]
    if m.get("yml"):
        L += [f"YML: товаров {m['yml']['offers']}, категорий {m['yml']['categories']}", ""]
    return "\n".join(L)


def main():
    ap = argparse.ArgumentParser(description="SEO-аудит сайта под Яндекс (robots.txt, зеркала, карта сайта, страницы, "
                                             "Вебмастер, Спеллер, YML).")
    ap.add_argument("url", help="адрес сайта, например https://example.ru")
    ap.add_argument("--max-pages", type=int, default=300, help="сколько страниц обойти (300)")
    ap.add_argument("--workers", type=int, default=4, help="одновременных запросов (4)")
    ap.add_argument("--delay", type=float, default=0.0, help="пауза между пачками запросов, с")
    ap.add_argument("--timeout", type=int, default=25, help="таймаут запроса, с")
    ap.add_argument("--include", help="обходить только пути по регулярному выражению")
    ap.add_argument("--exclude", help="не обходить пути по регулярному выражению")
    ap.add_argument("--webmaster", action="store_true", help="добавить данные Яндекс Вебмастера (YANDEX_WEBMASTER_TOKEN)")
    ap.add_argument("--speller", action="store_true", help="проверить орфографию Яндекс Спеллером")
    ap.add_argument("--speller-pages", type=int, default=150, help="сколько страниц проверять Спеллером (150)")
    ap.add_argument("--yml", help="адрес YML-фида для Яндекс Маркета / «Товаров»")
    ap.add_argument("--format", choices=["md", "json"], default="md")
    ap.add_argument("-o", "--output", help="файл отчёта (по умолчанию – на экран)")
    ap.add_argument("-q", "--quiet", action="store_true", help="без хода работы")
    ap.add_argument("--version", action="version", version="yaudit " + VERSION)
    args = ap.parse_args()
    socket.setdefaulttimeout(args.timeout + 5)
    res = Audit(args.url, args).run()
    out = json.dumps(res, ensure_ascii=False, indent=1) if args.format == "json" else to_markdown(res)
    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(out)
        print(f"отчёт: {args.output} · критично {res['summary'].get('critical', 0)}, важно {res['summary'].get('important', 0)}, "
              f"желательно {res['summary'].get('advice', 0)}", file=sys.stderr)
    else:
        print(out)


if __name__ == "__main__":
    main()
