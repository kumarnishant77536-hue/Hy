#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
hy.py - HY OSINT TOOL
Phone number OSINT helper optimised for Termux.

Features
  * Offline telecom analysis via the `phonenumbers` library
    (validity, region, carrier, line type, timezones, formats)
  * Messaging / social footprint links for manual checking, plus a
    multi-threaded endpoint reachability probe
  * Google dork URL generator (8 targeted queries)
  * Optional JSON report export

Usage
  python hy.py +91XXXXXXXXXX
  python hy.py 9876543210 --region IN
  python hy.py +14155550123 --json report.json --no-probe
  python hy.py                      (interactive prompt)

Intended for lawful use only: your own number, numbers you have explicit
permission to investigate, or authorised security / exposure assessments.
"""

import sys

if sys.version_info < (3, 7):
    sys.stderr.write("[!] hy.py requires Python 3.7 or newer.\n")
    sys.exit(1)

import argparse
import importlib
import importlib.util
import json
import re
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone as dt_timezone
from urllib.parse import quote_plus

# --------------------------------------------------------------------------- #
# 1. Automated setup & dependency check (runs before third-party imports)
# --------------------------------------------------------------------------- #

REQUIRED = {  # import name -> pip package name
    "phonenumbers": "phonenumbers",
    "requests": "requests",
    "rich": "rich",
    "colorama": "colorama",
    "bs4": "beautifulsoup4",
}


def _missing_packages():
    return [pip for mod, pip in REQUIRED.items() if importlib.util.find_spec(mod) is None]


def ensure_dependencies():
    """Check required packages; try to install them; otherwise print exact commands."""
    missing = _missing_packages()
    if not missing:
        return

    print("[*] Missing Python packages: " + ", ".join(missing))
    print("[*] Attempting automatic installation...")
    cmd = [sys.executable, "-m", "pip", "install", "--quiet", "--disable-pip-version-check"] + missing
    try:
        subprocess.check_call(cmd)
    except (subprocess.CalledProcessError, FileNotFoundError, OSError) as exc:
        print("\n[!] Automatic installation failed: {}".format(exc))
        print("[!] Install the dependencies manually, then re-run hy.py:\n")
        print("    pkg update && pkg install python python-pip")
        print("    pip install " + " ".join(missing))
        print("\n    Or install everything at once:")
        print("    pip install phonenumbers requests rich colorama beautifulsoup4\n")
        sys.exit(1)

    importlib.invalidate_caches()
    still_missing = _missing_packages()
    if still_missing:
        print("[!] Still missing after install: " + ", ".join(still_missing))
        print("    Run: pip install " + " ".join(still_missing))
        sys.exit(1)
    print("[+] Dependencies installed.\n")


ensure_dependencies()

import phonenumbers  # noqa: E402
from phonenumbers import (  # noqa: E402
    NumberParseException,
    PhoneNumberFormat,
    PhoneNumberType,
    carrier,
    geocoder,
)
from phonenumbers import timezone as pn_timezone  # noqa: E402

try:  # ValidationResult lives at package level in current releases
    from phonenumbers import ValidationResult  # noqa: E402
except ImportError:  # pragma: no cover
    ValidationResult = None

import requests  # noqa: E402
from bs4 import BeautifulSoup  # noqa: E402
from colorama import Fore, Style, init as colorama_init  # noqa: E402
from rich import box  # noqa: E402
from rich.console import Console  # noqa: E402
from rich.markup import escape  # noqa: E402
from rich.panel import Panel  # noqa: E402
from rich.table import Table  # noqa: E402

colorama_init(autoreset=True)
console = Console(highlight=False)

VERSION = "1.0.0"

# --------------------------------------------------------------------------- #
# 2. UI helpers
# --------------------------------------------------------------------------- #

BANNER_LINES = [
    r" _   _ __   __",
    r"| | | |\ \ / /",
    r"| |_| | \ V / ",
    r"|  _  |  | |  ",
    r"|_| |_|  |_|  ",
]
BANNER_COLORS = [Fore.RED, Fore.YELLOW, Fore.GREEN, Fore.CYAN, Fore.MAGENTA]


def show_banner():
    print()
    for line, color in zip(BANNER_LINES, BANNER_COLORS):
        print("   " + color + Style.BRIGHT + line)
    print()
    print("   " + Fore.CYAN + Style.BRIGHT + "[ H Y   O S I N T   T O O L ]" + Style.RESET_ALL
          + Fore.WHITE + "  v" + VERSION)
    print("   " + Fore.YELLOW + "Phone number OSINT for Termux")
    print("   " + Fore.RED + "Lawful use only: own numbers / authorised assessments.")
    print()


def info(msg):
    console.print("[bold cyan][*][/] " + msg)


def good(msg):
    console.print("[bold green][+][/] " + msg)


def warn(msg):
    console.print("[bold yellow][!][/] " + msg)


def fail(msg):
    console.print("[bold red][x][/] " + msg)


# --------------------------------------------------------------------------- #
# 3. Core telecom analysis
# --------------------------------------------------------------------------- #

def _enum_label_map(enum_cls, labels):
    """Build {enum_value: label} safely across phonenumbers versions."""
    out = {}
    if enum_cls is None:
        return out
    for name, label in labels.items():
        if hasattr(enum_cls, name):
            out[getattr(enum_cls, name)] = label
    return out


TYPE_LABELS = _enum_label_map(PhoneNumberType, {
    "FIXED_LINE": ("Landline", "Landline"),
    "MOBILE": ("Mobile", "Mobile"),
    "FIXED_LINE_OR_MOBILE": ("Landline or Mobile", "Mobile/Landline"),
    "TOLL_FREE": ("Toll-free", "Other"),
    "PREMIUM_RATE": ("Premium rate", "Other"),
    "SHARED_COST": ("Shared cost", "Other"),
    "VOIP": ("VoIP", "VoIP"),
    "PERSONAL_NUMBER": ("Personal number", "Other"),
    "PAGER": ("Pager", "Other"),
    "UAN": ("Universal access number", "Other"),
    "VOICEMAIL": ("Voicemail", "Other"),
    "UNKNOWN": ("Unknown", "Unknown"),
})

REASON_LABELS = _enum_label_map(ValidationResult, {
    "IS_POSSIBLE": "Length is possible",
    "IS_POSSIBLE_LOCAL_ONLY": "Possible for local dialling only",
    "INVALID_COUNTRY_CODE": "Invalid country code",
    "TOO_SHORT": "Too short",
    "TOO_LONG": "Too long",
    "INVALID_LENGTH": "Invalid length",
})


def parse_number(raw, region=None):
    """Normalise user input and parse it. Raises ValueError / NumberParseException."""
    if raw is None or not raw.strip():
        raise ValueError("No phone number was provided.")

    cleaned = re.sub(r"[\s\-\.\(\)]", "", raw.strip())
    if cleaned.startswith("00"):
        cleaned = "+" + cleaned[2:]

    if not re.fullmatch(r"\+?\d{4,17}", cleaned):
        raise ValueError(
            "Invalid format. Use digits with an optional leading '+', "
            "e.g. +919876543210 (spaces, dashes and brackets are fine)."
        )
    if not cleaned.startswith("+") and not region:
        raise ValueError(
            "Missing country code. Use international format (+<country code><number>) "
            "or pass a region, e.g.  --region IN"
        )
    return phonenumbers.parse(cleaned, region.upper() if region else None)


def analyse_number(num):
    """Return a dict with all offline telecom intelligence for a parsed number."""
    valid = phonenumbers.is_valid_number(num)
    possible = phonenumbers.is_possible_number(num)

    reason = phonenumbers.is_possible_number_with_reason(num)
    reason_text = REASON_LABELS.get(reason, str(reason))

    ntype = phonenumbers.number_type(num)
    type_label, category = TYPE_LABELS.get(ntype, ("Unknown", "Unknown"))

    region_code = phonenumbers.region_code_for_number(num) or "Unknown"
    country = geocoder.country_name_for_number(num, "en") or "Unknown"
    location = geocoder.description_for_number(num, "en") or country
    carrier_name = carrier.name_for_number(num, "en") or "Unavailable"
    tzs = list(pn_timezone.time_zones_for_number(num))

    return {
        "valid": valid,
        "possible": possible,
        "possible_reason": reason_text,
        "country_code": num.country_code,
        "national_number": str(num.national_number),
        "region_code": region_code,
        "country": country,
        "location": location,
        "carrier": carrier_name,
        "line_type": type_label,
        "line_category": category,
        "timezones": tzs,
        "formats": {
            "e164": phonenumbers.format_number(num, PhoneNumberFormat.E164),
            "international": phonenumbers.format_number(num, PhoneNumberFormat.INTERNATIONAL),
            "national": phonenumbers.format_number(num, PhoneNumberFormat.NATIONAL),
            "rfc3966": phonenumbers.format_number(num, PhoneNumberFormat.RFC3966),
        },
    }


# --------------------------------------------------------------------------- #
# 4. Footprint links + threaded reachability probe
# --------------------------------------------------------------------------- #

HEADERS = {
    "User-Agent": ("Mozilla/5.0 (Linux; Android 13; Termux) AppleWebKit/537.36 "
                   "(KHTML, like Gecko) Chrome/124.0 Mobile Safari/537.36"),
    "Accept-Language": "en-US,en;q=0.8",
}


def build_footprint_links(num):
    e164 = phonenumbers.format_number(num, PhoneNumberFormat.E164)
    digits = e164[1:]
    region = (phonenumbers.region_code_for_number(num) or "").lower()
    national = str(num.national_number)

    if region:
        truecaller = "https://www.truecaller.com/search/{}/{}".format(region, national)
        truecaller_note = "Web lookup (may require login / captcha)"
    else:
        truecaller = "https://www.truecaller.com/"
        truecaller_note = "Region unknown - search the number manually"

    return [
        {"name": "WhatsApp", "url": "https://wa.me/" + digits, "kind": "http",
         "note": "Click-to-chat; opens a chat prompt if the number is on WhatsApp"},
        {"name": "Telegram", "url": "https://t.me/+" + digits, "kind": "http",
         "note": "Contact link; resolves only if the user allows phone discovery"},
        {"name": "Viber", "url": "viber://add?number=" + digits, "kind": "deeplink",
         "note": "App deep link; opens Viber (Termux: use termux-open)"},
        {"name": "Truecaller", "url": truecaller, "kind": "http", "note": truecaller_note},
        {"name": "Facebook", "url": "https://www.facebook.com/search/top/?q=" + quote_plus(e164),
         "kind": "http", "note": "Search by number (login normally required)"},
        {"name": "Google", "url": "https://www.google.com/search?q=" + quote_plus('"{}"'.format(e164)),
         "kind": "manual", "note": "Exact-match search for the E.164 number"},
        {"name": "Skype", "url": "skype:{}?chat".format(e164), "kind": "deeplink",
         "note": "App deep link; opens Skype chat if available"},
        {"name": "LinkedIn", "url": "https://www.linkedin.com/search/results/all/?keywords=" + quote_plus(e164),
         "kind": "http", "note": "Search by number (login required)"},
    ]


def _classify_status(code):
    if 200 <= code < 300:
        return "REACHABLE", "green"
    if 300 <= code < 400:
        return "REDIRECT", "cyan"
    if code in (401, 403, 429, 999):
        return "LOGIN / BOT WALL", "yellow"
    if code in (404, 410):
        return "NOT FOUND", "red"
    if code >= 500:
        return "SERVER ERROR", "red"
    return "HTTP {}".format(code), "yellow"


def probe_link(item, timeout):
    """Fetch one endpoint and report reachability + page title. Never raises."""
    result = {
        "name": item["name"], "url": item["url"], "status_code": None,
        "state": "", "color": "white", "title": "", "elapsed_ms": None, "error": None,
    }

    if item["kind"] == "deeplink":
        result.update(state="DEEP LINK", color="magenta")
        return result
    if item["kind"] == "manual":
        result.update(state="OPEN IN BROWSER", color="magenta")
        return result

    start = time.perf_counter()
    try:
        resp = requests.get(item["url"], headers=HEADERS, timeout=timeout,
                            allow_redirects=True, stream=True)
        try:
            chunk = next(resp.iter_content(chunk_size=65536), b"")
        finally:
            resp.close()
        result["elapsed_ms"] = int((time.perf_counter() - start) * 1000)
        result["status_code"] = resp.status_code
        result["state"], result["color"] = _classify_status(resp.status_code)

        try:
            html = chunk.decode(resp.encoding or "utf-8", errors="ignore")
            soup = BeautifulSoup(html, "html.parser")
            if soup.title and soup.title.string:
                result["title"] = re.sub(r"\s+", " ", soup.title.string).strip()[:70]
        except Exception:  # parsing problems must never break the run
            pass

    except requests.exceptions.Timeout:
        result.update(state="TIMEOUT", color="red", error="Request timed out")
    except requests.exceptions.SSLError:
        result.update(state="SSL ERROR", color="red", error="TLS handshake failed")
    except requests.exceptions.ConnectionError:
        result.update(state="NO CONNECTION", color="red", error="Network unreachable / DNS failure")
    except requests.exceptions.RequestException as exc:
        result.update(state="REQUEST ERROR", color="red", error=str(exc)[:120])
    except Exception as exc:  # last-resort guard
        result.update(state="ERROR", color="red", error=str(exc)[:120])
    return result


def probe_all(items, timeout, threads):
    workers = max(1, min(threads, len(items)))
    results = {}
    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = {pool.submit(probe_link, it, timeout): it["name"] for it in items}
        for fut in as_completed(futures):
            name = futures[fut]
            try:
                results[name] = fut.result()
            except Exception as exc:  # should not happen, but never crash
                results[name] = {"name": name, "url": "", "status_code": None,
                                 "state": "ERROR", "color": "red", "title": "",
                                 "elapsed_ms": None, "error": str(exc)[:120]}
    return [results[it["name"]] for it in items]


# --------------------------------------------------------------------------- #
# 5. Google dork generator
# --------------------------------------------------------------------------- #

def number_variants(num):
    e164 = phonenumbers.format_number(num, PhoneNumberFormat.E164)
    variants = [
        phonenumbers.format_number(num, PhoneNumberFormat.INTERNATIONAL),
        e164,
        e164[1:],
        phonenumbers.format_number(num, PhoneNumberFormat.NATIONAL),
        str(num.national_number),
    ]
    seen, ordered = set(), []
    for v in variants:
        if v and v not in seen:
            seen.add(v)
            ordered.append(v)
    return ordered


def build_dorks(num):
    any_fmt = " OR ".join('"{}"'.format(v) for v in number_variants(num))
    base = "({})".format(any_fmt)

    dorks = [
        ("Exact match (all formats)", any_fmt),
        ("Documents & spreadsheets",
         base + " (filetype:pdf OR filetype:doc OR filetype:docx OR filetype:xls "
                "OR filetype:xlsx OR filetype:csv OR filetype:txt)"),
        ("Paste sites",
         base + " (site:pastebin.com OR site:paste.ee OR site:ghostbin.com OR site:justpaste.it "
                "OR site:rentry.co OR site:controlc.com)"),
        ("Code repositories",
         base + " (site:github.com OR site:gist.github.com OR site:gitlab.com OR site:bitbucket.org)"),
        ("Social media posts",
         base + " (site:facebook.com OR site:instagram.com OR site:twitter.com OR site:x.com "
                "OR site:linkedin.com OR site:vk.com)"),
        ("Public directories & contact pages",
         base + ' (intitle:"contact" OR intitle:"directory" OR intitle:"phone book" '
                "OR inurl:contact OR inurl:directory)"),
        ("Classifieds & business listings",
         base + " (site:olx.com OR site:quikr.com OR site:craigslist.org OR site:gumtree.com "
                "OR site:justdial.com OR site:yellowpages.com)"),
        ("Leak / breach mentions (exposure check)",
         base + ' (intext:"leak" OR intext:"dump" OR intext:"database" OR intext:"combolist" '
                "OR inurl:forum OR inurl:thread)"),
    ]
    return [{"name": n, "query": q, "url": "https://www.google.com/search?q=" + quote_plus(q)}
            for n, q in dorks]


# --------------------------------------------------------------------------- #
# 6. Rendering
# --------------------------------------------------------------------------- #

def render_telecom(data):
    table = Table(title="Telecom Analysis", title_style="bold cyan", box=box.ROUNDED,
                  border_style="cyan", show_header=False, expand=False)
    table.add_column("Field", style="bold yellow", no_wrap=True)
    table.add_column("Value", style="white", overflow="fold")

    def yes_no(flag):
        return "[bold green]YES[/]" if flag else "[bold red]NO[/]"

    cat = data["line_category"]
    cat_style = {"Mobile": "green", "Landline": "cyan", "VoIP": "magenta"}.get(cat, "yellow")

    table.add_row("Valid number", yes_no(data["valid"]))
    table.add_row("Possible number", yes_no(data["possible"]) + "  [dim]({})[/]".format(escape(data["possible_reason"])))
    table.add_row("Country / Region", "{} ({})".format(escape(data["country"]), data["region_code"]))
    table.add_row("Country calling code", "+{}".format(data["country_code"]))
    table.add_row("Location hint", escape(data["location"]))
    table.add_row("Carrier (original)", escape(data["carrier"]))
    table.add_row("Line type", "[bold {}]{}[/]".format(cat_style, escape(data["line_type"])))
    table.add_row("Timezone(s)", escape(", ".join(data["timezones"]) or "Unknown"))
    table.add_row("E.164", data["formats"]["e164"])
    table.add_row("International", data["formats"]["international"])
    table.add_row("National", data["formats"]["national"])
    table.add_row("RFC 3966", data["formats"]["rfc3966"])
    console.print(table)
    console.print("[dim]Note: carrier data reflects the original number allocation; "
                  "ported numbers may now belong to a different carrier.[/]\n")


def render_footprint(items, results, probed):
    table = Table(title="Messaging & Social Footprint", title_style="bold magenta",
                  box=box.ROUNDED, border_style="magenta", expand=False)
    table.add_column("Platform", style="bold yellow", no_wrap=True)
    table.add_column("Endpoint state", no_wrap=True)
    table.add_column("Info", overflow="fold")

    for item, res in zip(items, results):
        if probed or res["state"] in ("DEEP LINK", "OPEN IN BROWSER"):
            state = "[bold {}]{}[/]".format(res["color"], res["state"])
        else:
            state = "[dim]SKIPPED[/]"
        extra = []
        if res["status_code"]:
            extra.append("HTTP {}".format(res["status_code"]))
        if res["elapsed_ms"] is not None:
            extra.append("{} ms".format(res["elapsed_ms"]))
        if res["title"]:
            extra.append('title: "{}"'.format(res["title"]))
        if res["error"]:
            extra.append(res["error"])
        detail = escape(item["note"])
        if extra:
            detail += "\n[dim]" + escape(" | ".join(extra)) + "[/]"
        table.add_row(item["name"], state, detail)
    console.print(table)

    console.print("\n[bold cyan]Check links[/] [dim](copy / open manually)[/]")
    for item in items:
        console.print("[bold yellow]{}[/]".format(item["name"]))
        console.print("  " + item["url"], markup=False, highlight=False, soft_wrap=True)
    console.print(
        "\n[dim]'REACHABLE' only means the endpoint answered. It is NOT proof that an account "
        "exists for this number. Platforms hide most data behind logins and privacy settings.[/]\n"
    )


def render_dorks(dorks):
    console.print(Panel.fit("[bold green]Google Dorks & Deep Web Links[/]", border_style="green"))
    for i, d in enumerate(dorks, 1):
        console.print("[bold yellow]{}. {}[/]".format(i, escape(d["name"])))
        console.print("  " + d["url"], markup=False, highlight=False, soft_wrap=True)
    console.print()


# --------------------------------------------------------------------------- #
# 7. Orchestration
# --------------------------------------------------------------------------- #

def investigate(raw, args):
    """Run a full investigation for one input. Returns True on success."""
    try:
        num = parse_number(raw, args.region)
    except ValueError as exc:
        fail(str(exc))
        return False
    except NumberParseException as exc:
        fail("Could not parse the number: {}".format(exc))
        return False

    data = analyse_number(num)
    if not data["valid"]:
        warn("This number is not valid for its region. Results below may be incomplete.")

    good("Target: [bold white]{}[/]".format(data["formats"]["international"]))
    console.print()
    render_telecom(data)

    items = build_footprint_links(num)
    if args.no_probe:
        results = [probe_link({**it, "kind": it["kind"] if it["kind"] != "http" else "manual"}, args.timeout)
                   for it in items]
        probed = False
    else:
        info("Probing {} endpoints with up to {} threads (timeout {}s)...".format(
            sum(1 for i in items if i["kind"] == "http"), args.threads, args.timeout))
        try:
            with console.status("[cyan]Running threaded checks...[/]"):
                results = probe_all(items, args.timeout, args.threads)
        except Exception as exc:
            warn("Probe step failed ({}); showing links only.".format(exc))
            results = [probe_link({**it, "kind": "manual"}, args.timeout) for it in items]
        probed = True
        console.print()

    render_footprint(items, results, probed)

    dorks = build_dorks(num)
    render_dorks(dorks)

    if args.json:
        report = {
            "tool": "hy.py",
            "version": VERSION,
            "generated_utc": datetime.now(dt_timezone.utc).isoformat(timespec="seconds"),
            "input": raw,
            "telecom": data,
            "footprint": [{**{"name": it["name"], "url": it["url"], "note": it["note"]},
                          "state": r["state"], "status_code": r["status_code"],
                          "title": r["title"], "error": r["error"]}
                          for it, r in zip(items, results)],
            "dorks": [{"name": d["name"], "query": d["query"], "url": d["url"]} for d in dorks],
        }
        try:
            with open(args.json, "w", encoding="utf-8") as fh:
                json.dump(report, fh, indent=2, ensure_ascii=False)
            good("JSON report saved to [bold]{}[/]".format(escape(args.json)))
        except OSError as exc:
            fail("Could not write JSON report: {}".format(exc))
    return True


def parse_args():
    p = argparse.ArgumentParser(
        prog="hy.py",
        description="HY OSINT TOOL - phone number OSINT helper for Termux (lawful use only).",
        epilog="Examples:  python hy.py +919876543210   |   python hy.py 9876543210 -r IN",
    )
    p.add_argument("number", nargs="?", help="Phone number, preferably in +<country code><number> format")
    p.add_argument("-r", "--region", help="Default region (ISO 3166 alpha-2, e.g. IN, US) for numbers without '+'")
    p.add_argument("-t", "--timeout", type=int, default=8, help="Per-request timeout in seconds (default: 8)")
    p.add_argument("-T", "--threads", type=int, default=8, help="Max worker threads (default: 8)")
    p.add_argument("--no-probe", action="store_true", help="Skip network probing; only generate links")
    p.add_argument("-j", "--json", metavar="FILE", help="Save the full report as JSON")
    args = p.parse_args()
    args.timeout = max(1, min(args.timeout, 60))
    args.threads = max(1, min(args.threads, 32))
    return args


def interactive_loop(args):
    info("No number supplied. Entering interactive mode (press Enter on an empty line to quit).")
    while True:
        try:
            raw = input("\n" + Fore.CYAN + Style.BRIGHT + "hy> " + Fore.WHITE
                        + "Enter phone number (e.g. +91XXXXXXXXXX): " + Style.RESET_ALL).strip()
        except EOFError:
            print()
            return 0
        if not raw or raw.lower() in ("q", "quit", "exit"):
            return 0
        console.print()
        investigate(raw, args)


def main():
    try:
        args = parse_args()
        show_banner()
        if args.number:
            return 0 if investigate(args.number, args) else 1
        return interactive_loop(args)
    except KeyboardInterrupt:
        console.print("\n[bold yellow][!] Interrupted by user. Bye.[/]")
        return 130
    except Exception as exc:  # final safety net: never show a raw traceback
        fail("Unexpected error: {}".format(exc))
        return 1


if __name__ == "__main__":
    sys.exit(main())
