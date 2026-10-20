#!/usr/bin/env python3
"""Navigation helper: map catalogue family numbers to pinned preprint
directories and list their TeX blobs.  Writes scratch/family-map.json."""
import json, os, re

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", ".."))
PROJECT = os.path.normpath(os.path.join(ROOT, "..", "..", "..", ".."))

text = open(os.path.join(PROJECT, "sources", "CONTENTS.md"), encoding="utf-8").read()
tree = json.load(open(os.path.join(PROJECT, "sources", "preprints-tree.json")))
items = tree["tree"] if isinstance(tree, dict) else tree
blobs = [it for it in items if it["type"] == "blob"]

fam = None
out = {}
for line in text.splitlines():
    m = re.match(r"\*\*(\d{3})\. ", line)
    if m:
        fam = m.group(1)
        out[fam] = {"title": re.sub(r"<[^>]*>", "", line.split("**")[1]), "dirs": []}
        continue
    for d in re.findall(r"\]\((preprints/[^/)]+)/", line):
        if fam and d not in out[fam]["dirs"]:
            out[fam]["dirs"].append(d)
for f, rec in out.items():
    rec["tex"] = [it["path"] for it in blobs
                  if any(it["path"].startswith(d + "/") for d in rec["dirs"])
                  and it["path"].endswith(".tex")]
json.dump(out, open(os.path.join(ROOT, "scratch", "family-map.json"), "w"), indent=1)
print(len(out))
