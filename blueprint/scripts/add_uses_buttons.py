#!/usr/bin/env python3
"""Give every result whose proof has dependencies the "Uses" button in its heading.

leanblueprint puts the button, which opens the list of results a statement rests on, into
the heading only when the *statement* carries a ``\\uses``; the list then also contains
the ``\\uses`` of the proof. A result whose ``\\uses`` sit in the proof alone, the usual
case, gets no button, and its dependencies can only be read off the dependency graph.

This script reads every ``\\uses`` from the blueprint source, in the statement and in the
proof that follows it or names it with ``\\proves``, and inserts into each heading that
has no button yet, but dependencies to show, the same button and dialog that the plugin
renders, so that the page script serves it like the others. Headings that already have the
button are left alone: their list is complete.

The pages are edited in place. The script fails if a cited label has no result on the
pages, or if it finds no result headings at all, which is how an upstream template change
would show up; a second run changes nothing.

Usage::

    python blueprint/scripts/add_uses_buttons.py [--source SRC] [--web DIR]
"""

from __future__ import annotations

import argparse
import glob
import io
import os
import re
import sys

KINDS = "theorem|proposition|lemma|corollary|remark|definition|example"
BS = re.escape(chr(92))  # a backslash, kept out of the source text of this file

ICON = ('<svg  class="icon icon-{name} "><use xlink:href="symbol-defs.svg#icon-{name}">'
        '</use></svg>\n')

BUTTON = (
    "\n    <button class=\"modal\">" + ICON.format(name="mindmap") + "</button>\n"
    "        <div class=\"modal-container\">\n"
    "      <div class=\"modal-content\">\n"
    "        <header>\n"
    "          <h1>Uses</h1>\n"
    "          <button class=\"closebtn\">" + ICON.format(name="cross") + "</button>\n"
    "        </header>\n"
    "        \n"
    "        <ul class=\"uses\">\n"
    "{items}"
    "        </ul>\n"
    "    \n"
    "      </div>\n"
    "    </div>\n"
)
ITEM = "          <li><a href=\"{url}\">{caption} {ref}</a></li>\n"


def tags(block: str, name: str) -> list[str]:
    """The labels listed in every ``\\name{...}`` of ``block``, in order."""
    out: list[str] = []
    for m in re.finditer(BS + name + r"\{([^}]*)\}", block):
        out += [x.strip() for x in m.group(1).split(",") if x.strip()]
    return out


def dependencies(source: str) -> dict[str, list[str]]:
    """Map the label of every result to its ``\\uses``: those of the statement first, then
    those of its proof, without repetitions."""
    results = []
    for m in re.finditer(BS + r"begin\{(" + KINDS + r")\}(.*?)" + BS + r"end\{\1\}", source, re.S):
        label = re.search(BS + r"label\{([^}]*)\}", m.group(2))
        if label:
            results.append({"label": label.group(1), "end": m.end(), "uses": tags(m.group(2), "uses")})
    for m in re.finditer(BS + r"begin\{proof\}(.*?)" + BS + r"end\{proof\}", source, re.S):
        proves = tags(m.group(1), "proves")
        if proves:
            owners = [r for r in results if r["label"] in proves]
        else:
            owners = [r for r in results if r["end"] <= m.start()][-1:]
        for r in owners:
            r["uses"] += [u for u in tags(m.group(1), "uses") if u not in r["uses"]]
    return {r["label"]: r["uses"] for r in results}


HEADING = re.compile(
    r'<div class="(\w+)_thmwrapper[^"]*" id="([^"]+)">\s*<div class="\w+_thmheading">'
    r'\s*<span class="\w+_thmcaption">\s*([^<]*?)\s*</span>'
    r'(?:\s*<span class="\w+_thmlabel">([^<]*)</span>)?', re.S)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--source", default="blueprint/src/content.tex")
    parser.add_argument("--web", default="blueprint/web")
    args = parser.parse_args()

    deps = dependencies(io.open(args.source, encoding="utf-8").read())

    pages = [p for p in sorted(glob.glob(os.path.join(args.web, "*.html")))
             if not p.endswith("dep_graph_document.html")]
    texts = {p: io.open(p, encoding="utf-8").read() for p in pages}

    # where every result lives and how it is numbered
    where: dict[str, tuple[str, str, str]] = {}
    for p, h in texts.items():
        for m in HEADING.finditer(h):
            where[m.group(2)] = (os.path.basename(p), m.group(3), (m.group(4) or "").strip())
    if not where:
        print(f"error: no result headings found under {args.web} -- has the upstream template changed?")
        return 1

    added, present, changed_pages = 0, 0, 0
    for p, h in texts.items():
        out, pos = [], 0
        for m in HEADING.finditer(h):
            label = m.group(2)
            uses = deps.get(label, [])
            content = h.find('_thmcontent', m.end())
            head_end = h.rfind("<div class=", 0, content)  # start of the content div
            heading = h[m.end():head_end]
            if not uses:
                continue
            if "icon-mindmap" in heading:
                present += 1
                continue
            items = []
            for u in uses:
                if u not in where:
                    print(f"error: {label} uses {u}, which is no result on the pages")
                    return 1
                page, caption, ref = where[u]
                items.append(ITEM.format(url=f"{page}#{u}", caption=caption, ref=ref))
            button = BUTTON.format(items="".join(items))
            # the plugin's order: permalink, proof link, Uses, Lean declarations
            lean = heading.find('<button class="modal lean">')
            if lean >= 0:
                at = m.end() + lean
            else:
                at = m.end() + heading.rfind("</a>") + len("</a>")
            out.append(h[pos:at]); out.append(button); pos = at
            added += 1
        if out:
            out.append(h[pos:])
            io.open(p, "w", encoding="utf-8").write("".join(out))
            changed_pages += 1

    print(f"Uses buttons: {added} added on {changed_pages} pages, {present} already present")
    return 0


if __name__ == "__main__":
    sys.exit(main())
