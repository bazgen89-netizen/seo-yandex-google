"""Проверка seo_audit на маленьком сайте с заранее известными ошибками (поднимается локально).

    python3 -m unittest discover -s tests -v
"""
import argparse
import json
import functools
import http.server
import os
import sys
import tempfile
import threading
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))
os.environ["NO_PROXY"] = os.environ["no_proxy"] = "127.0.0.1,localhost"
import seo_audit as yaudit  # noqa: E402

HEAD = '<meta name="viewport" content="width=device-width"><script>ym(12345678, "init", {})</script>'
GOOD = ('<html lang="ru"><head><title>{t}</title><meta name="description" content="{d}">' + HEAD.replace("{", "{{").replace("}", "}}") +
        '<link rel="canonical" href="{c}"><meta property="og:title" content="x"><meta property="og:image" content="/i.png">'
        '</head><body><h1>{t}</h1><p>{body}</p>{links}</body></html>')
TEXT = " ".join(["Китайский чай собирают весной и заваривают в гайвани небольшими проливами."] * 12)


class Quiet(http.server.SimpleHTTPRequestHandler):
    def log_message(self, *a):
        pass


class Site:
    def __init__(self):
        self.dir = tempfile.TemporaryDirectory()
        d = Path(self.dir.name)
        self.port = None
        handler = functools.partial(Quiet, directory=str(d))
        self.httpd = http.server.ThreadingHTTPServer(("127.0.0.1", 0), handler)
        self.port = self.httpd.server_address[1]
        root = f"http://127.0.0.1:{self.port}"
        links = '<a href="/a.html">a</a> <a href="/b.html">b</a> <a href="/gone.html">битая</a> <a href="/product.html">товар</a>'
        links += '<template><a href="{{s.href}}">шаблон</a></template>'
        (d / "robots.txt").write_text(f"User-agent: *\nDisallow: /private/\nSitemap: {root}/sitemap.xml\n", encoding="utf-8")
        urls = ["/", "/a.html", "/b.html", "/noidx.html", "/private/x.html", "/product.html"]
        (d / "sitemap.xml").write_text('<?xml version="1.0"?><urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">' +
                                       "".join(f"<url><loc>{root}{u}</loc></url>" for u in urls) + "</urlset>", encoding="utf-8")
        (d / "index.html").write_text(GOOD.format(t="Китайский чай с доставкой по России", d="Главная", c=root + "/",
                                                  body=TEXT, links=links), encoding="utf-8")
        (d / "a.html").write_text(f"<html><head>{HEAD}</head><body><p>{TEXT}</p></body></html>", encoding="utf-8")
        (d / "b.html").write_text(GOOD.format(t="Китайский чай с доставкой по России", d="Главная", c=root + "/b.html",
                                              body=TEXT, links=""), encoding="utf-8")
        (d / "noidx.html").write_text(f'<html><head><meta name="robots" content="noindex">{HEAD}</head><body>{TEXT}</body></html>',
                                      encoding="utf-8")
        (d / "product.html").write_text(GOOD.format(t="Пуэр Шу 2015 года, блин 357 г", d="Пуэр", c=root + "/product.html",
                                                    body=TEXT, links='<img src="/p.jpg">') .replace(
            "</head>", '<script type="application/ld+json">{"@context":"https://schema.org","@type":"Product","name":"Пуэр"}</script></head>'),
            encoding="utf-8")
        (d / "private").mkdir()
        (d / "private" / "x.html").write_text("<html></html>", encoding="utf-8")
        self.root = root + "/"
        threading.Thread(target=self.httpd.serve_forever, daemon=True).start()

    def close(self):
        self.httpd.shutdown()
        self.dir.cleanup()


def run(root, engine):
    args = argparse.Namespace(max_pages=50, workers=2, delay=0, timeout=5, include=None, exclude=None, engine=engine,
                              webmaster=False, gsc=False, gsc_inspect=5, psi=False, psi_pages=2, all=False,
                              speller=False, speller_pages=10, yml=None, quiet=True)
    return yaudit.Audit(root, args).run()


class AuditTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.site = Site()
        cls.res = run(cls.site.root, "both")
        cls.ids = {f["id"] for f in cls.res["findings"]}

    @classmethod
    def tearDownClass(cls):
        cls.site.close()

    def test_found_expected_problems(self):
        for fid in ("title-missing", "desc-missing", "h1-missing", "noindex-in-sitemap", "sitemap-disallowed",
                    "broken-links", "title-dup", "product-no-offer", "img-alt", "robots-no-clean-param"):
            self.assertIn(fid, self.ids, fid)

    def test_no_false_alarms(self):
        for fid in ("robots-blocks-site", "sitemap-none", "metrika-missing", "viewport", "soft-404", "fetch-error"):
            self.assertNotIn(fid, self.ids, fid)

    def test_robots_rules(self):
        r = yaudit.Robots("User-agent: *\nDisallow: /\n\nUser-agent: Yandex\nDisallow: /cart/\nAllow: /cart/public$\n"
                          "Clean-param: utm_source&utm_medium /\n")
        self.assertTrue(r.allowed("https://x.ru/"))            # Яндекс читает только свою группу
        self.assertFalse(r.allowed("https://x.ru/cart/1"))
        self.assertTrue(r.allowed("https://x.ru/cart/public"))
        self.assertFalse(r.allowed("https://x.ru/cart/public2"))
        self.assertEqual(r.clean_param_names(), {"utm_source", "utm_medium"})

    def test_engines(self):
        eng = {f["id"]: f["eng"] for f in self.res["findings"]}
        self.assertEqual(eng.get("robots-no-clean-param"), "yandex")
        self.assertEqual(eng.get("product-no-image"), "google")
        self.assertEqual(eng.get("title-missing"), "both")
        only_y = {f["id"] for f in run(self.site.root, "yandex")["findings"]}
        only_g = {f["id"] for f in run(self.site.root, "google")["findings"]}
        self.assertIn("robots-no-clean-param", only_y)
        self.assertNotIn("product-no-image", only_y)
        self.assertIn("product-no-image", only_g)
        self.assertNotIn("robots-no-clean-param", only_g)
        self.assertIn("title-missing", only_y & only_g)

    def test_googlebot_group(self):
        txt = "User-agent: *\nDisallow: /a/\n\nUser-agent: Googlebot\nDisallow: /\n"
        self.assertFalse(yaudit.Robots(txt, "google").allowed("https://x.ru/"))
        self.assertTrue(yaudit.Robots(txt, "yandex").allowed("https://x.ru/"))
        self.assertFalse(yaudit.Robots(txt, "yandex").allowed("https://x.ru/a/1"))

    def test_gsc_reason(self):
        self.assertEqual(yaudit.gsc_reason("Обнаружена, не проиндексирована")[0], "найдена, но ещё не просканирована")
        self.assertEqual(yaudit.gsc_reason("Crawled - currently not indexed")[0], "просканирована, но не проиндексирована")
        self.assertEqual(yaudit.gsc_reason("Что-то новое")[0], "Что-то новое")

    def test_template_links_ignored(self):
        txt = json.dumps(self.res["findings"], ensure_ascii=False)
        self.assertNotIn("{{s.href}}", txt)

    def test_norm_iri(self):
        a = yaudit.norm("https://x.ru/product/put\u02ba-2016/")
        b = yaudit.norm("https://x.ru/product/put%CA%BA-2016/")
        self.assertEqual(a, b)
        self.assertTrue(yaudit.to_uri("https://x.ru/чай/?q=пуэр").isascii())

    def test_markdown(self):
        md = yaudit.to_markdown(self.res)
        self.assertIn("# SEO-аудит для Яндекса и Google", md)
        self.assertIn("Ways Digital", md)
        self.assertIn("t.me/waysgen", md)
        self.assertNotIn(chr(0x2014), md)  # длинное тире в отчёте не используется


if __name__ == "__main__":
    unittest.main()
