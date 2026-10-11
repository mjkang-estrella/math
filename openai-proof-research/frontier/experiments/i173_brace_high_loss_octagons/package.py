"""Final inventory creation or exclusive seal. Not run by replay."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
EXP = "frontier/experiments/i173_brace_high_loss_octagons/"
SRC = "frontier/sources/i173_brace_high_loss_octagons/"
REPORT = "frontier/iterations/i173-brace-high-loss-octagons.md"


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def row(path):
    raw = (ROOT / path).read_bytes()
    return dict(path=path, size=len(raw), sha256=sha(raw))


def write_once(path, value):
    with (ROOT / path).open("x") as out:
        json.dump(value, out, sort_keys=True, indent=2)
        out.write("\n")


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "inventory":
        assert not (ROOT / (EXP + "seal.json")).exists()
        controls = {EXP + x + ".json" for x in ("inventory", "prevalidation", "seal")}
        paths = {REPORT}
        for prefix in (EXP, SRC):
            paths.update(str(p.relative_to(ROOT)) for p in (ROOT / prefix).rglob("*") if p.is_file())
        auth = json.loads((ROOT / (SRC + "authentication.json")).read_bytes())
        external = auth["bindings"]
        for r in external:
            assert row(r["path"]) == r
        replays = [
            ("mandatory", "01"), ("ancestor_audit", "01"), ("surgery_plan", "01"),
            ("surgeries", "01"), ("audit_refinements", "02"), ("post_analysis", "01"),
        ]
        inv = dict(iteration=173, owned=[row(p) for p in sorted(paths - controls)],
                   external=external,
                   context=[dict(path=r["path"], sha256=r["expected"]) for r in auth["contexts"]],
                   modules=["toolkit", "research"],
                   replays=[dict(function=name, payload=EXP + name + "-attempt-" + attempt + ".json")
                            for name, attempt in replays],
                   controls=sorted(controls),
                   policy="Complete immutable bytes before diagnostics; ancestor code opaque; never reseal")
        write_once(EXP + "inventory.json", inv)
        print("Inventory created", len(inv["owned"]), len(external))
    elif mode == "seal":
        invraw = (ROOT / (EXP + "inventory.json")).read_bytes()
        preraw = (ROOT / (EXP + "prevalidation.json")).read_bytes()
        pre = json.loads(preraw)
        assert pre["status"] == "PASS" and pre["inventory_sha256"] == sha(invraw)
        inv = json.loads(invraw)
        for r in inv["owned"] + inv["external"]:
            assert row(r["path"]) == r
        seal = dict(iteration=173, inventory_sha256=sha(invraw), prevalidation_sha256=sha(preraw),
                    report_sha256=row(REPORT)["sha256"], verifier_sha256=row(EXP + "verify.py")["sha256"],
                    creation="exclusive single create after successful prevalidation; no reseal")
        write_once(EXP + "seal.json", seal)
        print(json.dumps(dict(seal_sha256=row(EXP + "seal.json")["sha256"], **seal), indent=2))
    else:
        raise ValueError(mode)
