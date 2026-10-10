"""I163-only evidence preparation. Does not import or execute ancestor code."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path("/home/mj-kang/Documents/Dev/math/openai-proof-research")
OUT = ROOT / "frontier/sources/i163_corrected_bfss_contribution_astra"
MAP = "frontier/sources/i114_quantum_information_discovery/search-domain.json"
QUERY = (r"(?i)weyl.{0,24}(?:law|asymptotic)|"
         r"(?:eigenvalue|spectral).{0,24}(?:counting|asymptotic)|"
         r"(?:fixed.isotypic|equivariant.{0,30}weyl|matrix.{0,20}schr[oö])|"
         r"(?:weighted.{0,24}poincar|log.concav.{0,40}(?:weight|spectr))")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def record(path):
    data = (ROOT / path).read_bytes()
    return {"path": path, "bytes": len(data), "sha256": digest(data)}


def write(name, data):
    if (OUT / name).exists():
        assert json.loads((OUT / name).read_text()) == data, name
        return
    with (OUT / name).open("x", encoding="utf8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
        f.write("\n")


def main():
    assert not (OUT / "seal.json").exists(), "No preparation after seal"
    OUT.mkdir(parents=True, exist_ok=True)
    baseline = []
    for tag in ["i155_fixed_sector_bfss_counting",
                "i158_fixed_sector_bfss_counting_r2",
                "i162_fixed_sector_bfss_focused_astra"]:
        for parent in ["frontier/sources", "frontier/experiments"]:
            for p in sorted((ROOT / parent / tag).rglob("*")):
                if p.is_file():
                    baseline.append(record(str(p.relative_to(ROOT))))
    for p in [
        "AGENTS.md", "sources/upstream.json", "sources/CONTENTS.md",
        "sources/preprints-tree.json", MAP,
        "frontier/iterations/iteration155-fixed-sector-bfss-counting-task.json",
        "frontier/iterations/iteration158-fixed-sector-bfss-counting-r2-task.json",
        "frontier/iterations/i155-fixed-sector-bfss-counting.md",
        "frontier/reviews/i158-fixed-sector-bfss-counting-r2.md",
        "frontier/reviews/i162-fixed-sector-bfss-focused-astra.md",
        "frontier/iterations/i162-bfss-normalization-parent-correction.md",
        "frontier/experiments/i162-parent-verification.json",
    ]:
        baseline.append(record(p))
    write("immutable-baseline.json", sorted(baseline, key=lambda x: x["path"]))
    ledgers = []
    for p in ["frontier/README.md", "frontier/iterations/README.md",
              "frontier/TEN-FINDINGS.md"]:
        ledgers.append(record(p))
    write("live-ledger-observations.json", ledgers)
    domain = json.loads((ROOT / MAP).read_text())
    tree = json.loads((ROOT / "sources/preprints-tree.json").read_text())
    entries = tree["tree"]
    lookup = {x["path"]: x for x in entries}
    hits = []
    rx = re.compile(QUERY)
    totals = {}
    roots = set()
    for row in domain:
        kind = row["kind"]
        totals[kind] = totals.get(kind, 0) + 1
        roots.add(row["path"].split("/")[1])
        data = (ROOT / row["original_local"]).read_bytes()
        assert digest(data) == row["original_sha256"], row["path"]
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        assert blob == row["git_sha"], row["path"]
        key = row["path"]
        assert lookup[key]["sha"] == blob, key
        if kind == "outside_bytes":
            continue
        text_data = (ROOT / row["local"]).read_bytes()
        assert digest(text_data) == row["sha256"], row["local"]
        text = text_data.decode("utf8")
        for match in rx.finditer(text):
            a, b = match.span()
            hits.append({"path": row["path"], "local": row["local"],
                         "start": a, "end": b, "match": match.group(),
                         "line": text.count("\n", 0, a) + 1,
                         "context": text[max(0, a-180):min(len(text), b+350)]})
    write("manuscript-search.json", {
        "map": MAP, "query": QUERY, "flags": "case-insensitive, bounded same-line spans",
        "tree_entries": len(entries), "roots": len(roots), "kinds": totals,
        "scope": "Complete mapped text/PDF-text lexical search, not full semantic reading. Binary-only originals are hash-checked, not searched.",
        "hits": hits})
    print(json.dumps({"baseline": len(baseline), "roots": len(roots),
                      "kinds": totals, "hits": len(hits)}, indent=2))
    counts = {}
    for h in hits:
        root = h["path"].split("/")[1]
        counts[root] = counts.get(root, 0) + 1
    for root, count in sorted(counts.items()):
        print(count, root)


if __name__ == "__main__":
    main()
