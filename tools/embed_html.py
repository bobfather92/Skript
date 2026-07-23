#!/usr/bin/env python3
"""Synchronise ScriptForge.html with the compressed payload in scriptforge.py."""

import argparse
import base64
import gzip
from pathlib import Path
import re
import textwrap


ROOT = Path(__file__).resolve().parents[1]
HTML_PATH = ROOT / "ScriptForge.html"
PYTHON_PATH = ROOT / "scriptforge.py"
PAYLOAD_PATTERN = re.compile(
    r"_HTML_B64 = \(\n(?:    '[A-Za-z0-9+/=]+'\n)+\)",
    re.MULTILINE,
)


def encoded_payload(html: bytes) -> str:
    compressed = gzip.compress(html, compresslevel=9, mtime=0)
    encoded = base64.b64encode(compressed).decode("ascii")
    lines = "\n".join(f"    '{line}'" for line in textwrap.wrap(encoded, 100))
    return f"_HTML_B64 = (\n{lines}\n)"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail instead of updating when the embedded HTML is out of date",
    )
    args = parser.parse_args()

    html = HTML_PATH.read_bytes()
    source = PYTHON_PATH.read_text(encoding="utf-8")
    match = PAYLOAD_PATTERN.search(source)
    if not match:
        raise RuntimeError("Could not locate the embedded HTML payload")

    embedded = gzip.decompress(base64.b64decode("".join(
        re.findall(r"'([A-Za-z0-9+/=]+)'", match.group(0))
    )))
    if args.check:
        if embedded != html:
            raise SystemExit("Embedded HTML is out of date; run tools/embed_html.py")
        print("Embedded HTML matches ScriptForge.html.")
        return 0

    if embedded == html:
        print("Embedded HTML is already current.")
        return 0

    updated = source[:match.start()] + encoded_payload(html) + source[match.end():]
    PYTHON_PATH.write_text(updated, encoding="utf-8", newline="")
    print("Updated the embedded HTML in scriptforge.py.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
