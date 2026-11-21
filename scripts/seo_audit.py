#!/usr/bin/env python3
"""seo_audit – SEO-аудит сайта для Яндекса и Google (навык seo-yandex-google).

Обходит сайт так, как его видят роботы YandexBot и Googlebot (каждый со своими правилами robots.txt),
проверяет то, что важно для обоих поисковиков и для каждого по отдельности, и пишет отчёт на русском:
что исправить, почему и как. По желанию добавляет данные Яндекс Вебмастера и Google Search Console,
скорость по Google PageSpeed Insights (Core Web Vitals), орфографию Яндекс Спеллером и проверку YML-фида.

Только стандартная библиотека Python 3.10+, ставить ничего не нужно (для Search Console с ключом
сервисного аккаунта нужен openssl – он есть в Linux и macOS).

    python3 seo_audit.py https://example.ru
    python3 seo_audit.py https://example.ru --engine yandex --webmaster --speller -o report.md
    python3 seo_audit.py https://example.ru --engine google --gsc --psi -o report.md
    python3 seo_audit.py https://example.ru --all --yml https://example.ru/feed.yml -o report.md
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

VERSION = "2.0.0"
YANDEX_UA = "Mozilla/5.0 (compatible; YandexBot/3.0; +http://yandex.com/bots)"
GOOGLE_UA = ("Mozilla/5.0 (Linux; Android 6.0.1; Nexus 5X Build/MMB29P) AppleWebKit/537.36 (KHTML, like Gecko) "
             "Chrome/128.0.0.0 Mobile Safari/537.36 (compatible; Googlebot/2.1; +http://www.google.com/bot.html)")
ENG_TITLE = {"yandex": "Яндекс", "google": "Google", "both": ""}
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
    """Разбор robots.txt так, как его читает робот: Яндекс берёт группу User-agent: Yandex, Google – группу
    Googlebot, если она есть, иначе оба берут *; Allow/Disallow с * и $, побеждает самое длинное совпадение,
    при равенстве – Allow. Clean-param, Host и Crawl-delay понимает только Яндекс (Google их пропускает)."""

    def __init__(self, text, bot="yandex"):
        self.bot = bot
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
        self.google_group = next((r for a, r in self.groups if "googlebot" in a), None)
        self.star_group = next((r for a, r in self.groups if "*" in a), None)
        own = self.yandex_group if bot == "yandex" else self.google_group
        self.own_group = own
        self.rules = own if own is not None else (self.star_group or [])

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
        eng = getattr(args, "engine", "both") or "both"
        self.engines = {"yandex", "google"} if eng == "both" else {eng}
        self.robots = Robots("")            # правила, по которым идёт обход (Яндекс, если он проверяется)
        self.robots_y, self.robots_g = Robots(""), Robots("", "google")
        self.started = time.time()

    def has(self, eng):
        return eng == "both" or eng in self.engines

    # -- учёт находок
    def add(self, fid, sev, title, why, fix, url=None, extra=None, eng="both"):
        """eng: "both" – важно для обоих поисковиков, "yandex" / "google" – только для одного (в отчёте
        с пометкой). Находка поисковика, который сейчас не проверяется, не записывается."""
        if fid.startswith(("wm-", "yml-")):
            eng = "yandex"
        if not self.has(eng):
            return
        f = self.findings[fid]
        f.update(id=fid, sev=sev, title=title, why=why, fix=fix, eng=eng)
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
                     f"Ответ {r['status'] or r['error']}. Без robots.txt роботы не знают, что не индексировать, "
                     "и не видят ссылку на карту сайта; в Яндекс Вебмастере это ошибка NO_ROBOTS_TXT. Если robots.txt "
                     "отвечает 5xx, Google вообще перестаёт обходить сайт, пока не получит ответ.",
                     "Положите robots.txt в корень сайта с кодом 200.", self.root + "robots.txt")
        else:
            body = text_of(r)
            self.robots_y, self.robots_g = Robots(body, "yandex"), Robots(body, "google")
            self.robots = self.robots_y if self.has("yandex") else self.robots_g
            rb = self.robots_y
            if len(r["body"]) > 500 * 1024:
                self.add("robots-big", "important", "robots.txt больше 500 КБ",
                         "Яндекс и Google читают robots.txt только до 500 КБ (Google – до 500 КиБ), остальное пропускают.",
                         "Сократите правила, объедините похожие через *.", self.root + "robots.txt")
            for bot, rbx, name in (("yandex", self.robots_y, "Яндекса"), ("google", self.robots_g, "Google")):
                if not self.has(bot):
                    continue
                if not rbx.allowed(self.root):
                    self.add(f"robots-blocks-site-{bot}", "critical", f"robots.txt закрывает сайт от {name}",
                             f"Для группы, которую читает робот {name}, главная страница под Disallow. Сайт выпадет из поиска.",
                             f"Уберите Disallow: / из группы User-agent: {'Yandex' if bot == 'yandex' else 'Googlebot'} (или *).",
                             self.root + "robots.txt", eng=bot)
                else:
                    self.ok(f"Главная открыта для {name} в robots.txt")
                if rbx.own_group is not None and rbx.star_group:
                    star_dis = {p for a, p in rbx.star_group if not a and p}
                    own_dis = {p for a, p in rbx.own_group if not a and p}
                    miss = sorted(star_dis - own_dis)
                    if miss:
                        grp = "Yandex" if bot == "yandex" else "Googlebot"
                        self.add(f"robots-own-group-{bot}", "important", f"В группе {grp} нет запретов из группы *",
                                 f"Если в robots.txt есть User-agent: {grp}, робот {name} читает только её и пропускает *. "
                                 f"Запреты из * для него не действуют: {', '.join(miss[:8])}.",
                                 f"Повторите нужные Disallow в группе {grp} или удалите отдельную группу.",
                                 self.root + "robots.txt", eng=bot)
                blocked_assets = [p for a, p in rbx.rules if not a and re.search(r"\.css|\.js|/wp-includes|/assets|/static|/images?/|/wp-content/?$", p)]
                if blocked_assets:
                    self.add(f"robots-assets-{bot}", "important", f"robots.txt закрывает от {name} CSS, JS или картинки",
                             "Без стилей и скриптов робот не может отрисовать страницу и оценить удобство на телефоне "
                             f"(Яндекс: NOT_MOBILE_FRIENDLY; Google оценивает сайт по мобильной версии). Закрыто: {', '.join(blocked_assets[:6])}.",
                             "Откройте папки со стилями, скриптами и картинками (Allow).",
                             self.root + "robots.txt", eng=bot)
            if not rb.sitemaps:
                self.add("robots-no-sitemap", "advice", "В robots.txt нет строки Sitemap",
                         "Яндекс и Google находят карту сайта по robots.txt; без строки её нужно добавлять вручную "
                         "в Вебмастере и Search Console.",
                         f"Добавьте: Sitemap: {self.root}sitemap.xml", self.root + "robots.txt")
            if not rb.clean_params:
                self.add("robots-no-clean-param", "advice", "Нет Clean-param для меток (utm, yclid и т. п.)",
                         "Clean-param понимает только Яндекс: он склеивает адреса с метками рекламы и рассылок, "
                         "и робот не тратит обход на дубли. Иначе в Вебмастере бывает INSIGNIFICANT_CGI_PARAMETER.",
                         "Добавьте в robots.txt: Clean-param: utm_source&utm_medium&utm_campaign&utm_content&utm_term&yclid&gclid&fbclid&ysclid&from",
                         self.root + "robots.txt", eng="yandex")
            elif self.has("yandex"):
                self.ok("Clean-param в robots.txt есть")
            if rb.hosts:
                self.add("robots-host", "info", "В robots.txt осталась директива Host",
                         "С 2018 года Яндекс её не учитывает, Google не учитывал никогда: главное зеркало задаётся 301-редиректом.",
                         "Строку можно удалить; главное зеркало – через редирект.", self.root + "robots.txt", eng="yandex")
            if rb.crawl_delay:
                self.add("robots-crawl-delay", "info", "В robots.txt есть Crawl-delay",
                         "Яндекс не учитывает Crawl-delay с 2018 года, Google не учитывает вовсе.",
                         "Скорость обхода задаётся в Яндекс Вебмастере: Индексирование → Скорость обхода.",
                         self.root + "robots.txt", eng="yandex")

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
                         f"{v} → {loc} кодом {rv['status']}. Склейку зеркал Яндекс и Google делают по постоянному 301.",
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
                     "Код 5xx для робота значит «сервер сломан», а не «страницы нет»; при частых 5xx Яндекс и Google снижают "
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
                             "Яндекс и Google пропускают адреса не с того хоста, на котором лежит карта.",
                             "Оставьте в карте только адреса главного зеркала.", url)
                    continue
                self.sitemap_urls.add(norm(url))
                lm = u.find(ns + "lastmod")
                if lm is not None and lm.text and not re.match(r"^\d{4}-\d{2}-\d{2}(T\d{2}:\d{2}(:\d{2}(\.\d+)?)?(Z|[+-]\d{2}:\d{2}))?$", lm.text.strip()):
                    bad_lastmod += 1
            if n > 50000 or len(body) > 50 * 1024 * 1024:
                self.add("sitemap-too-big", "important", "Карта сайта больше 50 000 адресов или 50 МБ",
                         "Яндекс и Google читают не больше 50 000 адресов и 50 МБ в одном файле.",
                         "Разбейте на несколько файлов и соберите их в sitemap index.", sm)
            if bad_lastmod:
                self.add("sitemap-lastmod", "advice", "Неверный формат lastmod в карте сайта",
                         f"{bad_lastmod} записей не в формате W3C Datetime; поисковики их пропускают.",
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
        # обход – как робот Яндекса; если проверяется только Google – как Googlebot
        return fetch(u, ua=YANDEX_UA if self.has("yandex") else GOOGLE_UA, timeout=self.args.timeout)

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
                         "Яндекс и Google оставляют в индексе старый адрес, пока редирект временный.",
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
                         "Карта просит проиндексировать, мета-тег запрещает – Яндекс и Google считают это ошибкой карты.",
                         "Уберите страницу из карты или снимите noindex.", u)
            else:
                self.add("noindex", "info", "Страницы закрыты от индексации (noindex)",
                         "Проверьте, что это сделано намеренно (корзина, личный кабинет, поиск).",
                         "Если страница не должна быть в поиске, всё верно.", u)
        if len(canon) > 1:
            self.add("canonical-multi", "important", "Несколько rel=canonical на странице",
                     "Яндекс и Google не учитывают canonical, если их несколько.", "Оставьте один.", u)
        if canon:
            c = urllib.parse.urljoin(u, canon[0])
            if not canon[0].startswith("http"):
                self.add("canonical-relative", "advice", "rel=canonical с относительным адресом",
                         "Яндекс и Google рекомендуют полный адрес с протоколом и доменом.", "Пишите canonical полностью.", u)
            if norm(c) != norm(u):
                info["canonical_other"] = norm(c)
                if in_sm:
                    self.add("canonical-in-sitemap", "important", "В карте сайта неканонические страницы",
                             "Страница указывает canonical на другой адрес, а в карте стоит она сама. Яндекс и Google исключат "
                             "её как NOT_CANONICAL.", "В карте должны быть только канонические адреса.", u, c)
        elif not noindex:
            self.add("canonical-missing", "advice", "Нет rel=canonical",
                     "Без canonical дубли с метками и параметрами Яндекс и Google склеивают сами и не всегда в пользу нужного адреса.",
                     "Добавьте <link rel=\"canonical\" href=\"полный адрес страницы\">.", u)

        if not noindex:
            # заголовок и описание
            if not title:
                self.add("title-missing", "critical", "Нет заголовка <title>",
                         "Без title Яндекс и Google собирают заголовок в выдаче сами (в Вебмастере – DOCUMENTS_MISSING_TITLE).",
                         "Напишите уникальный title со смыслом страницы и главным запросом.", u)
            elif len(title) > (60 if self.has("google") else 70):
                lim = 60 if self.has("google") else 70
                self.add("title-long", "advice", f"Заголовок длиннее {lim} знаков",
                         "В выдаче Google видно около 60 знаков (600 пикселей), Яндекса – 55-70; хвост обрезается.",
                         "Главное слово и запрос – в начале заголовка.", u, f"{len(title)}: {title[:90]}")
            elif len(title) < 15:
                self.add("title-short", "advice", "Заголовок короче 15 знаков",
                         "Слишком короткий title не описывает страницу и не содержит запросов.",
                         "Добавьте суть страницы и регион или тип товара.", u, title)
            if not desc:
                self.add("desc-missing", "important", "Нет meta description",
                         "Яндекс и Google берут описание для выдачи из description; без него – случайный кусок текста. "
                         "В Вебмастере это DOCUMENTS_MISSING_DESCRIPTION.",
                         "Напишите 1-2 предложения о странице, до 160 знаков.", u)
            elif len(desc) > 200:
                self.add("desc-long", "advice", "meta description длиннее 200 знаков",
                         "Яндекс и Google показывают около 160 знаков.", "Сократите, главное – в начало.", u, f"{len(desc)} знаков")
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
                         "Почти пустые страницы Яндекс исключает как малоценные (LOW_QUALITY), Google – как «просканирована, но не проиндексирована».",
                         "Добавьте полезный текст или закройте страницу от индексации.", u, f"{len(words)} слов")

        # телефон и разметка
        if not any(m.get("name", "").lower() == "viewport" for m in P.metas):
            self.add("viewport", "important", "Нет meta viewport",
                     "Без него страница не адаптирована для телефона: Яндекс отмечает NOT_MOBILE_FRIENDLY, а Google индексирует сайт по мобильной версии.",
                     'Добавьте <meta name="viewport" content="width=device-width, initial-scale=1">.', u)
        if not P.lang:
            self.add("lang", "advice", "Нет атрибута lang у <html>",
                     "Язык страницы помогает роботу и экранным читалкам.", 'Укажите <html lang="ru">.', u)
        types, objs = ld_types(P.jsonld)
        if None in types:
            self.add("jsonld-invalid", "important", "Ошибка в JSON-LD разметке",
                     "Блок с ошибкой JSON Яндекс и Google пропускают целиком.",
                     "Проверьте разметку валидатором Яндекс Вебмастера или Google Rich Results Test (search.google.com/test/rich-results).", u)
        info["types"] = sorted(set(t for t in types if t))
        for t, o in objs:
            if t == "Product":
                offers = o.get("offers")
                if not offers:
                    self.add("product-no-offer", "important", "Разметка Product без offers (цены)",
                             "Без цены и наличия Яндекс не покажет товарный сниппет и не возьмёт товар в «Товары», "
                             "а Google – цену и наличие в выдаче и в бесплатных показах Покупок.",
                             "Добавьте offers: price, priceCurrency (RUB), availability.", u)
                else:
                    off = offers[0] if isinstance(offers, list) and offers else offers
                    if isinstance(off, dict) and not (off.get("price") or off.get("lowPrice")):
                        self.add("product-no-price", "important", "В разметке Product нет цены",
                                 "Товарный сниппет Яндекса и Google требует цену.", "Заполните offers.price.", u)
                    elif isinstance(off, dict) and not off.get("availability"):
                        self.add("product-no-availability", "advice", "В разметке Product нет наличия (availability)",
                                 "Google показывает в выдаче «В наличии» / «Нет в наличии» только по availability.",
                                 "Добавьте offers.availability: https://schema.org/InStock или OutOfStock.", u, eng="google")
                if not o.get("image"):
                    self.add("product-no-image", "important", "В разметке Product нет картинки (image)",
                             "Google не показывает товар с ценой в выдаче и в Покупках без картинки в разметке.",
                             "Добавьте в Product поле image с полным адресом фото.", u, eng="google")
        if self.has("google") and u != norm(self.root) and "BreadcrumbList" not in types and not noindex \
                and urllib.parse.urlsplit(u).path.strip("/").count("/") >= 1:
            self.add("breadcrumbs", "advice", "Нет разметки хлебных крошек (BreadcrumbList)",
                     "Google показывает в выдаче путь «Сайт › Раздел › Страница» вместо адреса только по BreadcrumbList.",
                     "Добавьте JSON-LD BreadcrumbList: главная → раздел → страница.", u, eng="google")
        if not P.meta(prop="og:title") and not noindex:
            self.add("og-missing", "advice", "Нет Open Graph (og:title, og:image)",
                     "По Open Graph строятся карточки ссылок в мессенджерах, соцсетях и Дзене; Google берёт og:image и для Discover.",
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
                     "Поставьте счётчик на все страницы и свяжите его с сайтом в Вебмастере.", u, eng="yandex")
        if P.mixed and self.scheme == "https":
            self.add("mixed-content", "important", "Смешанный контент: http-ресурсы на https-странице",
                     "Браузер блокирует такие картинки и скрипты, поисковики могут посчитать страницу небезопасной.",
                     "Замените адреса на https.", u, P.mixed[0][:150])
        no_alt = [i.get("src", "")[:120] for i in P.imgs if "alt" not in i]
        if no_alt:
            self.add("img-alt", "advice", "Картинки без alt",
                     "Для поиска по картинкам Яндекса и Google и для людей с экранными читалками alt – единственное описание картинки.",
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
                         "Поисковики не передают по ним вес; внутри сайта это обычно ошибка.", "Уберите rel=nofollow с внутренних ссылок.",
                         u, full)
            out.append(full)
        return out

    # -- шаг 4: итоги по всем страницам
    def site_wide(self):
        ok_pages = {u: p for u, p in self.pages.items() if p.get("status") == 200 and not p.get("redirect") and "title" in p}
        idx = {u: p for u, p in ok_pages.items() if not p.get("noindex") and not p.get("canonical_other")}
        for field, fid, title, why in (
                ("title", "title-dup", "Одинаковые заголовки на разных страницах",
                 "Для Яндекса и Google страницы с одинаковым title похожи на дубли (в Вебмастере – DUPLICATE_CONTENT_ATTRS)."),
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
                     "Яндекс и Google оставят в поиске одну, остальные исключат как дубли (в Вебмастере – DUPLICATE_PAGES).",
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
                     ", ".join(f"{k}: {v} стр." for k, v in counters.most_common(4)), eng="yandex")
        elif counters and self.has("yandex"):
            self.ok(f"Счётчик Метрики {next(iter(counters))} на {sum(counters.values())} страницах")
        self.meta["metrika"] = list(counters)
        # скорость ответа
        times = sorted(p["time"] for p in ok_pages.values() if "time" in p)
        if times:
            avg = sum(times) / len(times)
            self.meta["avg_response_s"] = round(avg, 2)
            if avg > 2:
                self.add("slow", "important" if avg > 3 else "advice", f"Медленный ответ сервера: в среднем {avg:.1f} с",
                         "Яндекс отмечает медленный сайт в Вебмастере (SLOW_AVG_RESPONSE_TIME) и реже обходит его; "
                         "у Google медленный ответ (TTFB) портит скорость загрузки, по которой он ранжирует.",
                         "Включите кеширование страниц, проверьте хостинг.", None)
            else:
                self.ok(f"Сервер отвечает в среднем за {avg:.2f} с")
        # главная: подтверждение Вебмастера, большой фавикон, разметка организации
        home = self.pages.get(norm(self.root), {})
        types = set(home.get("types", []))
        if not types & {"Organization", "LocalBusiness", "Store", "OnlineStore", "WebSite"} and home.get("status") == 200:
            self.add("org-schema", "advice", "На главной нет разметки Organization / LocalBusiness",
                     "Разметка организации помогает Яндексу и Google связать сайт с карточкой организации "
                     "(Яндекс Бизнес, Google Business Profile) и показать логотип и контакты.",
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
                     "Яндекс и Google показывают фавикон рядом с сайтом в выдаче; без него – пустой значок (FAVICON_ERROR).",
                     "Добавьте <link rel=\"icon\" href=\"/favicon.svg\" type=\"image/svg+xml\"> и /favicon.ico.", self.root)
        elif not big:
            self.add("favicon-big", "advice", "Нет фавикона 120×120 или SVG",
                     "Яндекс рекомендует SVG или PNG от 120×120: маленький значок в выдаче выглядит размыто (BIG_FAVICON_ABSENT).",
                     "Добавьте <link rel=\"icon\" href=\"/favicon-120.png\" sizes=\"120x120\"> или SVG.", self.root, eng="yandex")
        elif self.has("yandex"):
            self.ok("Фавикон крупного размера или SVG есть")
        if not P.meta(name="yandex-verification"):
            self.add("ya-verification", "info", "На главной нет мета-тега yandex-verification",
                     "Если права в Вебмастере подтверждены файлом или DNS, это нормально.",
                     "Проверьте, что сайт добавлен и подтверждён в webmaster.yandex.ru.", self.root, eng="yandex")

    def params_check(self):
        """Дубли с метками: адрес с utm должен склеиваться canonical (Яндекс понимает ещё Clean-param, Google – нет)."""
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
                         "Добавьте canonical на чистый адрес и Clean-param: utm_source&utm_medium&utm_campaign в robots.txt.",
                         test, eng="yandex")
            if c != norm(u):
                self.add("utm-dup-google", "important", "Адреса с метками utm без canonical на чистый адрес",
                         "Google не понимает Clean-param: склеить копии с метками для него может только canonical. "
                         "Без него в индекс попадают адреса из рекламы и рассылок.",
                         "Добавьте на всех страницах <link rel=\"canonical\"> на адрес без параметров.", test, eng="google")
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
                             f"{u} и {alt} оба отвечают 200 без canonical друг на друга – для Яндекса и Google это дубли.",
                             "Поставьте 301 с одного варианта на другой.", alt)
                break

    def bot_vs_browser(self):
        """Роботы Яндекса и Google и обычный браузер должны получать одно и то же."""
        sample = [norm(self.root)] + [u for u, p in self.pages.items() if p.get("status") == 200][:4]
        bots = [("yandex", YANDEX_UA, "YandexBot", "Робот Яндекса", "yandex.ru/.net/.com"),
                ("google", GOOGLE_UA, "Googlebot", "Робот Google", "googlebot.com/google.com")]
        for u in dict.fromkeys(sample):
            b = fetch(u, ua=BROWSER_UA, timeout=self.args.timeout)
            for eng, ua, name, who, dns in bots:
                if not self.has(eng):
                    continue
                a = fetch(u, ua=ua, timeout=self.args.timeout)
                if a["status"] and b["status"] and a["status"] != b["status"]:
                    self.add(f"bot-differs-{eng}", "critical", f"{who} получает другой ответ, чем браузер",
                             f"Браузер: {b['status']}, {name}: {a['status']}. Защита от ботов или настройки сервера "
                             "отсекают робота – страницы выпадут из поиска. Это бывает с антиботами, CDN и файрволами.",
                             f"Разрешите {name} в защите от ботов (проверка подлинности – обратный DNS на {dns}).",
                             u, eng=eng)

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

    # -- Google PageSpeed Insights: Core Web Vitals
    def pagespeed(self):
        """Скорость по меркам Google: данные реальных посетителей Chrome (CrUX) и лабораторный замер Lighthouse,
        телефон. Ключ не обязателен (PAGESPEED_API_KEY – больше запросов в сутки)."""
        key = os.environ.get("PAGESPEED_API_KEY") or os.environ.get("GOOGLE_API_KEY")
        ok = [u for u, p in self.pages.items() if p.get("status") == 200 and not p.get("redirect") and "title" in p]
        kinds = [norm(self.root)]
        for rx in (r"/(product|tovar|item|catalog/[^/]+/[^/]+)/", r"/(category|product-category|catalog|shop)/", r"/(blog|news|stati|articles?)/"):
            hit = next((u for u in ok if re.search(rx, u) and u not in kinds), None)
            if hit:
                kinds.append(hit)
        for u in ok:
            if len(kinds) >= self.args.psi_pages:
                break
            if u not in kinds:
                kinds.append(u)
        rows = []
        for u in kinds[: self.args.psi_pages]:
            q = {"url": u, "strategy": "mobile", "category": "performance", "locale": "ru"}
            if key:
                q["key"] = key
            r = fetch("https://www.googleapis.com/pagespeedonline/v5/runPagespeed?" + urllib.parse.urlencode(q),
                      ua="seo-audit/" + VERSION, timeout=120, headers={"Accept": "application/json"})
            if r["status"] != 200:
                rows.append({"url": u, "error": f"{r['status'] or r['error']}"})
                if r["status"] == 429:
                    self.meta["psi_note"] = "лимит запросов без ключа – задайте PAGESPEED_API_KEY"
                    break
                continue
            d = json.loads(r["body"])
            le = (d.get("loadingExperience") or {}).get("metrics") or {}
            origin = (d.get("originLoadingExperience") or {}).get("metrics") or {}
            src = le or origin
            def pct(k):
                return (src.get(k) or {}).get("percentile")
            lcp, inp, cls = pct("LARGEST_CONTENTFUL_PAINT_MS"), pct("INTERACTION_TO_NEXT_PAINT"), pct("CUMULATIVE_LAYOUT_SHIFT_SCORE")
            lh = d.get("lighthouseResult") or {}
            score = ((lh.get("categories") or {}).get("performance") or {}).get("score")
            lab_lcp = ((lh.get("audits") or {}).get("largest-contentful-paint") or {}).get("numericValue")
            row = {"url": u, "field": "страница" if le else ("весь сайт" if origin else "нет данных"),
                   "lcp": lcp, "inp": inp, "cls": (cls / 100 if cls is not None else None),
                   "score": round(score * 100) if score is not None else None,
                   "lab_lcp": round(lab_lcp) if lab_lcp else None}
            rows.append(row)
            if lcp and lcp > 2500:
                self.add("cwv-lcp", "important" if lcp > 4000 else "advice", "Google: долгая загрузка главного блока (LCP)",
                         f"У реальных посетителей на телефоне главный блок появляется за {lcp / 1000:.1f} с; Google считает "
                         "хорошим до 2,5 с. Скорость – сигнал ранжирования Google (Core Web Vitals).",
                         "Ускорьте первую картинку (без ленивой загрузки, fetchpriority=high, WebP), уберите блокирующие скрипты, "
                         "включите сжатие и кеш.", u, f"LCP {lcp} мс", eng="google")
            if inp and inp > 200:
                self.add("cwv-inp", "important" if inp > 500 else "advice", "Google: медленный отклик на нажатия (INP)",
                         f"Страница отвечает на нажатие за {inp} мс; хорошо – до 200 мс.",
                         "Разбейте тяжёлые скрипты, отложите сторонние виджеты (чаты, счётчики).", u, f"INP {inp} мс", eng="google")
            if cls is not None and cls / 100 > 0.1:
                self.add("cwv-cls", "important" if cls / 100 > 0.25 else "advice", "Google: страница «прыгает» при загрузке (CLS)",
                         f"Сдвиг вёрстки {cls / 100:.2f}; хорошо – до 0,1.",
                         "Задайте размеры картинкам и блокам рекламы, не вставляйте баннеры над текстом после загрузки.",
                         u, f"CLS {cls / 100:.2f}", eng="google")
            if not le and not origin and score is not None and score < 0.5:
                self.add("psi-lab", "advice", "Google: низкая оценка скорости в лабораторном замере",
                         f"Оценка PageSpeed на телефоне {round(score * 100)} из 100 (данных реальных посетителей ещё нет).",
                         "Откройте отчёт pagespeed.web.dev для этой страницы – там список, что тормозит.", u, eng="google")
        self.meta["psi"] = rows

    # -- Google Search Console
    def _gsc_token(self):
        tok = os.environ.get("GSC_ACCESS_TOKEN")
        if tok:
            return tok
        path = os.environ.get("GSC_KEY") or os.environ.get("GOOGLE_APPLICATION_CREDENTIALS")
        if not path or not os.path.exists(path):
            return None
        import base64
        import subprocess
        import tempfile
        key = json.load(open(path, encoding="utf-8"))
        b64 = lambda x: base64.urlsafe_b64encode(x).rstrip(b"=")
        now = int(time.time())
        head = b64(json.dumps({"alg": "RS256", "typ": "JWT"}).encode())
        claim = b64(json.dumps({"iss": key["client_email"], "scope": "https://www.googleapis.com/auth/webmasters.readonly",
                                "aud": key["token_uri"], "iat": now, "exp": now + 3600}).encode())
        fd, pem = tempfile.mkstemp(suffix=".pem")
        try:
            os.write(fd, key["private_key"].encode())
            os.close(fd)
            sig = subprocess.run(["openssl", "dgst", "-sha256", "-sign", pem], input=head + b"." + claim,
                                 capture_output=True, check=True).stdout
        finally:
            os.remove(pem)
        jwt = (head + b"." + claim + b"." + b64(sig)).decode()
        r = fetch(key["token_uri"], method="POST", ua="seo-audit/" + VERSION, timeout=40,
                  data=urllib.parse.urlencode({"grant_type": "urn:ietf:params:oauth:grant-type:jwt-bearer",
                                               "assertion": jwt}).encode(),
                  headers={"Content-Type": "application/x-www-form-urlencoded"})
        return json.loads(r["body"]).get("access_token") if r["status"] == 200 else None

    def search_console(self):
        try:
            token = self._gsc_token()
        except Exception as e:
            self.meta["gsc"] = f"ключ не прочитан: {e}"[:200]
            return
        if not token:
            self.meta["gsc"] = "нет доступа (GSC_KEY – файл ключа сервисного аккаунта или GSC_ACCESS_TOKEN)"
            return
        H = {"Authorization": "Bearer " + token, "Accept": "application/json", "Content-Type": "application/json"}

        def call(url, body=None):
            r = fetch(url, method="POST" if body is not None else "GET", ua="seo-audit/" + VERSION, timeout=90,
                      headers=H, data=json.dumps(body).encode() if body is not None else None)
            if r["status"] != 200:
                raise RuntimeError(f"{r['status'] or r['error']} {r['body'][:200]!r}")
            return json.loads(r["body"] or b"{}")
        try:
            sites = [x["siteUrl"] for x in call("https://www.googleapis.com/webmasters/v3/sites").get("siteEntry", [])]
            bare = self.host[4:] if self.host.startswith("www.") else self.host
            site = next((x for x in (self.root, f"https://{bare}/", f"sc-domain:{bare}", f"http://{bare}/") if x in sites), None)
            if not site:
                self.meta["gsc"] = "сайта нет среди ресурсов этого доступа в Search Console"
                return
            g = {"site": site}
            enc = urllib.parse.quote(site, safe="")
            try:
                sm = call(f"https://www.googleapis.com/webmasters/v3/sites/{enc}/sitemaps").get("sitemap", [])
                g["sitemaps"] = [(x.get("path"), x.get("errors", 0), x.get("warnings", 0), (x.get("lastDownloaded") or "")[:10]) for x in sm]
                for path, errs, warns, _ in g["sitemaps"]:
                    if int(errs or 0):
                        self.add("gsc-sitemap-errors", "important", "Search Console: ошибки в карте сайта",
                                 f"Google нашёл в {path} ошибок: {errs}.", "Search Console → Файлы Sitemap.", path, eng="google")
                if not sm:
                    self.add("gsc-no-sitemap", "important", "Search Console: карта сайта не отправлена",
                             "Google не получал карту сайта через Search Console – новые страницы он находит медленнее.",
                             "Search Console → Файлы Sitemap → добавить адрес карты.", None, eng="google")
            except Exception as e:
                g["sitemaps_error"] = str(e)[:120]
            end = time.strftime("%Y-%m-%d", time.gmtime(time.time() - 3 * 86400))
            start = time.strftime("%Y-%m-%d", time.gmtime(time.time() - 31 * 86400))
            try:
                q = call(f"https://www.googleapis.com/webmasters/v3/sites/{enc}/searchAnalytics/query",
                         {"startDate": start, "endDate": end, "dimensions": ["query"], "rowLimit": 20})
                g["queries"] = [(r["keys"][0], int(r["impressions"]), int(r["clicks"]), round(r["position"], 1)) for r in q.get("rows", [])]
                g["period"] = f"{start} – {end}"
                tot = call(f"https://www.googleapis.com/webmasters/v3/sites/{enc}/searchAnalytics/query",
                           {"startDate": start, "endDate": end, "rowLimit": 1})
                if tot.get("rows"):
                    t = tot["rows"][0]
                    g["total"] = (int(t["impressions"]), int(t["clicks"]), round(t["position"], 1))
            except Exception as e:
                g["queries_error"] = str(e)[:120]
            # проверка индексации выборки страниц (URL Inspection, до 2000 в сутки на ресурс)
            sample = [norm(self.root)] + [u for u in sorted(self.sitemap_urls) if u != norm(self.root)]
            ok = {u for u, p in self.pages.items() if p.get("status") == 200 and not p.get("noindex")}
            sample = [u for u in sample if u in ok][: self.args.gsc_inspect]
            states = Counter()
            for u in sample:
                try:
                    res = call("https://searchconsole.googleapis.com/v1/urlInspection/index:inspect",
                               {"inspectionUrl": u, "siteUrl": site, "languageCode": "ru"})
                except Exception as e:
                    g["inspect_error"] = str(e)[:120]
                    break
                ir = (res.get("inspectionResult") or {}).get("indexStatusResult") or {}
                cov = ir.get("coverageState") or "?"
                states[cov] += 1
                if ir.get("verdict") not in ("PASS", None) and not re.search(r"(?i)alternate page|альтернативная", cov):
                    title, fix = gsc_reason(cov)
                    self.add("gsc-not-indexed", "important", "Search Console: страницы не в индексе Google",
                             "Google сам сообщает, что страница не в поиске, и называет причину (выборка проверенных страниц).",
                             fix, u, title, eng="google")
                gc, uc = ir.get("googleCanonical"), ir.get("userCanonical")
                if gc and uc and norm(gc) != norm(uc):
                    self.add("gsc-canonical", "important", "Search Console: Google выбрал другой канонический адрес",
                             "Вы указали один canonical, а Google считает главной другую страницу – ваша выпадает из поиска как дубль.",
                             "Сделайте страницы различимыми или поставьте 301 на ту, что выбрал Google.", u, f"Google выбрал {gc}", eng="google")
                if (ir.get("robotsTxtState") or "") == "DISALLOWED":
                    self.add("gsc-robots", "critical", "Search Console: страница закрыта robots.txt для Google", "",
                             "Откройте страницу в robots.txt для Googlebot.", u, eng="google")
            g["inspected"] = len(sample)
            g["coverage"] = dict(states)
            self.meta["gsc"] = g
        except Exception as e:
            self.meta["gsc"] = f"ошибка API: {e}"[:300]

    # -- запуск
    def run(self):
        self.site_checks()
        self.sitemaps()
        self.crawl()
        self.site_wide()
        self.favicon_check()
        self.params_check()
        self.bot_vs_browser()
        a = self.args
        if (a.webmaster or a.all) and self.has("yandex"):
            self.log("Яндекс Вебмастер…")
            self.webmaster()
        if (a.gsc or a.all) and self.has("google"):
            self.log("Google Search Console…")
            self.search_console()
        if (a.psi or a.all) and self.has("google"):
            self.log("Google PageSpeed…")
            self.pagespeed()
        if a.speller or a.all:
            self.speller()
        if a.yml and self.has("yandex"):
            self.log("YML-фид…")
            self.yml(a.yml)
        self.meta["seconds"] = round(time.time() - self.started)
        return self.result()

    def result(self):
        fs = sorted(self.findings.values(), key=lambda f: (SEV_ORDER[f["sev"]], -f["count"]))
        return {"tool": "seo-yandex-google", "version": VERSION, "site": self.root, "engines": sorted(self.engines),
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

# причины из Search Console: API отдаёт текст на языке languageCode (ru) или по-английски – узнаём по словам
GSC_REASONS = [
    (("просканирована", "crawled - currently"), "просканирована, но не проиндексирована",
     "Google счёл страницу недостаточно полезной: добавьте уникальный текст, фото, цены, ссылки на неё с других страниц."),
    (("обнаружена", "discovered - currently"), "найдена, но ещё не просканирована",
     "Мало внутренних ссылок или сервер отвечает медленно: поставьте ссылки из разделов и меню."),
    (("не совпадают", "different canonical"), "Google выбрал другой канонический адрес",
     "Сделайте страницы различимыми или поставьте 301 на выбранную Google."),
    (("копи", "duplicate"), "дубль без выбранного канонического адреса", "Укажите canonical или сделайте страницу уникальной."),
    (("noindex",), "закрыта noindex", "Если страница нужна в поиске – уберите noindex."),
    (("robots",), "закрыта robots.txt", "Если страница нужна в поиске – откройте её в robots.txt."),
    (("ложная", "soft 404"), "мягкая 404 – похожа на пустую", "Отдавайте 404 для несуществующих или наполните страницу."),
    (("404",), "404 – страница не найдена", "Верните страницу или поставьте 301 на подходящую."),
    (("5xx", "сервер"), "ошибка сервера при обходе", "Проверьте сервер и логи на дату обхода."),
    (("переадрес", "redirect"), "перенаправляет на другую", "Уберите адрес из карты сайта, ставьте ссылки на конечный адрес."),
    (("неизвест", "unknown"), "Google о странице не знает",
     "Поставьте на неё внутренние ссылки, добавьте в карту сайта, запросите индексирование."),
]


def gsc_reason(cov):
    c = (cov or "").lower()
    for words, title, fix in GSC_REASONS:
        if any(w in c for w in words):
            return title, fix
    return cov, "Search Console → Проверка URL: там причина и кнопка «Запросить индексирование»."


# ---------------------------------------------------------------- отчёт


def to_markdown(res):
    m, s = res["meta"], res["summary"]
    engines = res.get("engines") or ["google", "yandex"]
    who = " и ".join({"yandex": "Яндекса", "google": "Google"}[e] for e in sorted(engines, key=lambda e: e != "yandex"))
    L = [f"# SEO-аудит для {who}: {res['site']}", "",
         f"{res['date']} · seo-yandex-google {res['version']} · страниц обойдено: {m.get('pages_crawled', 0)} · "
         f"в карте сайта: {m.get('sitemap_urls', 0)} · средний ответ: {m.get('avg_response_s', '?')} с · {m.get('seconds')} с", "",
         f"**Критично: {s.get('critical', 0)} · Важно: {s.get('important', 0)} · Желательно: {s.get('advice', 0)} · "
         f"К сведению: {s.get('info', 0)}**", ""]
    by = Counter(f.get("eng", "both") for f in res["findings"])
    if len(engines) > 1:
        L += [f"Находок для обоих поисковиков: {by.get('both', 0)} · только Яндекс: {by.get('yandex', 0)} · "
              f"только Google: {by.get('google', 0)}", ""]
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
            L += ["", f"Популярные запросы Яндекса ({wm.get('queries_period')}):", "", "| Запрос | Показы | Клики | Позиция |", "|---|---|---|---|"]
            L += [f"| {q} | {sh} | {cl} | {pos} |" for q, sh, cl, pos in wm["queries"][:15]]
        L.append("")
    elif wm:
        L += [f"_Яндекс Вебмастер: {wm}_", ""]
    g = m.get("gsc")
    if isinstance(g, dict):
        L += ["## Google Search Console", ""]
        if g.get("total"):
            sh, cl, pos = g["total"]
            L.append(f"За {g.get('period')}: показы {sh}, клики {cl}, средняя позиция {pos}")
        if g.get("coverage"):
            L.append(f"Проверено страниц на индексацию: {g.get('inspected')} – " + ", ".join(
                f"{k}: {v}" for k, v in g["coverage"].items()))
        if g.get("sitemaps"):
            L.append("Карты сайта: " + "; ".join(f"{p} (ошибок {e}, загружена {d})" for p, e, w, d in g["sitemaps"]))
        if g.get("queries"):
            L += ["", "Популярные запросы Google:", "", "| Запрос | Показы | Клики | Позиция |", "|---|---|---|---|"]
            L += [f"| {q} | {sh} | {cl} | {pos} |" for q, sh, cl, pos in g["queries"][:15]]
        L.append("")
    elif g:
        L += [f"_Google Search Console: {g}_", ""]
    if m.get("psi"):
        L += ["## Скорость по Google (PageSpeed Insights, телефон)", "",
              "| Страница | Данные | LCP, мс | INP, мс | CLS | Оценка |", "|---|---|---|---|---|---|"]
        for r in m["psi"]:
            if r.get("error"):
                L.append(f"| {r['url']} | ошибка {r['error']} | | | | |")
            else:
                L.append(f"| {r['url']} | {r['field']} | {r['lcp'] or '–'} | {r['inp'] or '–'} | "
                         f"{'–' if r['cls'] is None else r['cls']} | {r['score'] if r['score'] is not None else '–'} |")
        L += ["", "Хорошо по Google: LCP до 2500 мс, INP до 200 мс, CLS до 0,1."
              + (f" {m['psi_note']}." if m.get("psi_note") else ""), ""]
    for sev in ("critical", "important", "advice", "info"):
        fs = [f for f in res["findings"] if f["sev"] == sev]
        if not fs:
            continue
        L += [f"## {SEV_TITLE[sev]}", ""]
        for f in fs:
            tag = ENG_TITLE.get(f.get("eng", "both"), "")
            L += [f"### {(tag + ' · ') if tag and len(engines) > 1 else ''}{f['title']}" + (f" – {f['count']}" if f["count"] > 1 else ""), "",
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
    ap = argparse.ArgumentParser(description="SEO-аудит сайта для Яндекса и Google (robots.txt, зеркала, карта сайта, "
                                             "страницы, разметка, Вебмастер, Search Console, PageSpeed, Спеллер, YML).")
    ap.add_argument("url", help="адрес сайта, например https://example.ru")
    ap.add_argument("--engine", choices=["both", "yandex", "google"], default="both",
                    help="для какого поисковика проверять (оба)")
    ap.add_argument("--max-pages", type=int, default=300, help="сколько страниц обойти (300)")
    ap.add_argument("--workers", type=int, default=4, help="одновременных запросов (4)")
    ap.add_argument("--delay", type=float, default=0.0, help="пауза между пачками запросов, с")
    ap.add_argument("--timeout", type=int, default=25, help="таймаут запроса, с")
    ap.add_argument("--include", help="обходить только пути по регулярному выражению")
    ap.add_argument("--exclude", help="не обходить пути по регулярному выражению")
    ap.add_argument("--webmaster", action="store_true", help="добавить данные Яндекс Вебмастера (YANDEX_WEBMASTER_TOKEN)")
    ap.add_argument("--gsc", action="store_true", help="добавить данные Google Search Console (GSC_KEY или GSC_ACCESS_TOKEN)")
    ap.add_argument("--gsc-inspect", type=int, default=30, help="сколько страниц проверить на индексацию в Google (30)")
    ap.add_argument("--psi", action="store_true", help="скорость по Google PageSpeed Insights (Core Web Vitals)")
    ap.add_argument("--psi-pages", type=int, default=4, help="сколько страниц мерить PageSpeed (4)")
    ap.add_argument("--all", action="store_true", help="всё сразу: Вебмастер, Search Console, PageSpeed, Спеллер")
    ap.add_argument("--speller", action="store_true", help="проверить орфографию Яндекс Спеллером")
    ap.add_argument("--speller-pages", type=int, default=150, help="сколько страниц проверять Спеллером (150)")
    ap.add_argument("--yml", help="адрес YML-фида для Яндекс Маркета / «Товаров»")
    ap.add_argument("--format", choices=["md", "json"], default="md")
    ap.add_argument("-o", "--output", help="файл отчёта (по умолчанию – на экран)")
    ap.add_argument("-q", "--quiet", action="store_true", help="без хода работы")
    ap.add_argument("--version", action="version", version="seo-yandex-google " + VERSION)
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
