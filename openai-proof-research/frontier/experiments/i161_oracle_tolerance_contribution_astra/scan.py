"""One fresh flat search of the existing original-position map; never executes it."""
import collections
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / "frontier/sources/i161_oracle_tolerance_contribution_astra"
MAP = "frontier/sources/i160_oracle_tolerance_contribution_r4/corpus.json"
PATTERNS = {
    "robust": r"(?i)(?:robust|noisy|inexact|inaccurate|adversarial|adaptive|biased|perturbation).{0,90}(?:sampl|oracle|gradient)|(?:sampl|oracle|gradient).{0,90}(?:robust|inexact|inaccurate|adversarial|biased)",
    "entropy": r"(?i)shifted.composition|log.Harnack|relative.entropy|KL.divergence",
    "compiler": r"(?i)fixed.seed|coefficient.sum|routine.height|Gaussian.reserve|reserved.noise|uncached|compiler.lipschitz|small.coefficients",
}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    mapping = json.loads((ROOT / MAP).read_bytes())
    tree_raw = (ROOT / mapping["tree_path"]).read_bytes()
    tree = json.loads(tree_raw)
    entries = tree["tree"]
    by_path = {x["path"]: x for x in entries if x["type"] == "blob"}
    paths = [x["path"] for x in mapping["bindings"]]
    # Some older GitHub trees are rooted at preprints rather than at the repo.
    if paths[0] not in by_path:
        by_path = {"preprints/" + p: x for p, x in by_path.items()}
    assert set(paths) == set(by_path)
    assert len(paths) == len(set(paths)) == 10373
    regexes = {k: re.compile(v) for k, v in PATTERNS.items()}
    results = {k: [] for k in PATTERNS}
    kinds = collections.Counter()
    for row in mapping["bindings"]:
        original = (ROOT / row["original_local"]).read_bytes()
        raw = original if row["local"] == row["original_local"] else (ROOT / row["local"]).read_bytes()
        assert sha(original) == row["original_sha256"], row["path"]
        assert sha(raw) == row["sha256"], row["path"]
        git_sha = hashlib.sha1(b"blob " + str(len(original)).encode() + b"\0" + original).hexdigest()
        assert git_sha == row["git_sha"] == by_path[row["path"]]["sha"], row["path"]
        kinds[row["kind"]] += 1
        for n, line in enumerate(raw.decode("utf-8", errors="replace").splitlines(), 1):
            for name, regex in regexes.items():
                spans = [list(m.span()) for m in regex.finditer(line)]
                if spans:
                    results[name].append({"path": row["path"], "local": row["local"], "line": n,
                                          "spans": spans, "text": line})
    output = {
        "map_path": MAP, "map_sha256": sha((ROOT / MAP).read_bytes()),
        "tree_path": mapping["tree_path"], "tree_sha256": sha(tree_raw),
        "tree_entries": len(entries), "original_positions": len(paths),
        "manuscripts": len({p.split("/")[1] for p in paths}),
        "kinds": dict(kinds), "fresh_flat_preparation_traversals": 1,
        "convention": "UTF-8 replacement decode; Python splitlines; 1-based lines; 0-based codepoint spans",
        "patterns": PATTERNS, "results": results,
        "scope": "Fresh byte/Git-blob verification and lexical coverage, not semantic reading of the corpus.",
    }
    with (OUT / "flat-search.json").open("x") as handle:
        json.dump(output, handle, ensure_ascii=False, indent=2)
        handle.write("\n")
    print(json.dumps({k: output[k] for k in ["tree_entries", "original_positions", "manuscripts", "kinds"]}))
    for name, rows in results.items():
        counts = collections.Counter(x["path"].split("/")[1] for x in rows)
        print(name, len(rows), counts.most_common(12))


if __name__ == "__main__":
    main()
