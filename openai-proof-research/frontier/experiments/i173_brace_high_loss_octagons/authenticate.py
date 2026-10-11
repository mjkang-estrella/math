"""Fresh I173 authentication. Ancestor Python is only hashed, never executed."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
EXP = "frontier/experiments/i173_brace_high_loss_octagons/"
SRC = "frontier/sources/i173_brace_high_loss_octagons/"
OLD = "frontier/experiments/i172_prescribed_square_switch/"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def authenticate():
    anchors = {
        "frontier/iterations/i172-prescribed-square-switch.md":
        "030e71d1fe49909ed5dc98eb2a3250045cc3f7d8068f701cf844e676473accbe",
        OLD + "seal.json":
        "8abdc63ae868fbbda7778e422da34194d918be99e15fc29b784cc6468140c972",
        OLD + "verify.py":
        "c7a8c1af8d767573ce16fcafa28a18e28fb373f403536d6bd93c30893b9cbe28",
    }
    for path, expected in anchors.items():
        assert digest((ROOT / path).read_bytes()) == expected, path
    seal = json.loads((ROOT / (OLD + "seal.json")).read_bytes())
    for name in ("inventory", "prevalidation"):
        assert digest((ROOT / (OLD + name + ".json")).read_bytes()) == seal[name + "_sha256"]
    inv = json.loads((ROOT / (OLD + "inventory.json")).read_bytes())
    pre = json.loads((ROOT / (OLD + "prevalidation.json")).read_bytes())
    assert pre["status"] == "PASS"
    controls = {OLD + n + ".json" for n in ("inventory", "prevalidation", "seal")}
    actual = {"frontier/iterations/i172-prescribed-square-switch.md"}
    for prefix in (OLD, "frontier/sources/i172_prescribed_square_switch/"):
        actual.update(str(p.relative_to(ROOT)) for p in (ROOT / prefix).rglob("*") if p.is_file())
    assert actual == {r["path"] for r in inv["owned"]} | controls
    rows, contexts = {}, []
    for row in inv["owned"] + inv["external"]:
        data = (ROOT / row["path"]).read_bytes()
        got = digest(data)
        if row["role"] == "context-only":
            contexts.append(dict(path=row["path"], expected=row["sha256"], actual=got,
                                 drift=got != row["sha256"]))
        else:
            assert got == row["sha256"] and len(data) == row["size"], row["path"]
            rows[row["path"]] = dict(path=row["path"], sha256=got, size=len(data))
    additions = list(controls) + [
        "sources/upstream.json", "sources/CONTENTS.md", "sources/preprints-tree.json",
        "frontier/iterations/iteration173-brace-high-loss-octagons-brief.md",
        "frontier/iterations/i172-prescribed-square-switch-parent-disposition.md",
        "frontier/experiments/i172-parent-verification.json",
        "frontier/experiments/i172-parent-certificates.json",
    ]
    for path in additions:
        data = (ROOT / path).read_bytes()
        rows[path] = dict(path=path, sha256=digest(data), size=len(data))
    return dict(status="PASS", anchors=anchors, owned=len(inv["owned"]),
                non_context_external=sum(r["role"] != "context-only" for r in inv["external"]),
                contexts=contexts, bindings=sorted(rows.values(), key=lambda r: r["path"]))


if __name__ == "__main__":
    receipt = authenticate()
    (ROOT / SRC).mkdir(parents=True, exist_ok=True)
    with (ROOT / (SRC + "authentication.json")).open("x") as out:
        json.dump(receipt, out, sort_keys=True, indent=2)
        out.write("\n")
    print(json.dumps({k: v for k, v in receipt.items() if k != "bindings"}, indent=2))
