"""One-way controls: inventory, successful prevalidation, exactly one seal."""
import ast
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path("/home/mj-kang/Documents/Dev/math/openai-proof-research")
REL = "frontier/experiments/i178_five_port_annihilator/"
OWN = ROOT/REL
REPORT = "frontier/iterations/i178-five-port-annihilator.md"
SOURCE = ROOT/"frontier/sources/i178_five_port_annihilator"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def record(path):
    b = (ROOT/path).read_bytes()
    return {"path":path,"size":len(b),"sha256":sha(b)}


def write(name,value):
    with (OWN/name).open("x") as f:
        json.dump(value,f,sort_keys=True,indent=2)
        f.write("\n")


def main():
    mode = sys.argv[1]
    assert not (OWN/"seal.json").exists(), "Never reseal"
    if mode == "inventory":
        assert not (OWN/"inventory.json").exists()
        checked_json, checked_markdown = [], []
        for directory in (OWN,SOURCE):
            for path in directory.rglob("*"):
                if path.is_file() and path.suffix == ".json" and path.stat().st_size:
                    json.loads(path.read_bytes())
                    checked_json.append(str(path.relative_to(ROOT)))
        for path in [ROOT/REPORT,OWN/"failures.md",SOURCE/"literature.md"]:
            text = path.read_text()
            assert text.endswith("\n")
            assert all(line == line.rstrip() for line in text.splitlines()), str(path)
            checked_markdown.append(str(path.relative_to(ROOT)))
        source_validation = []
        for name in ("authenticate178.py","math178.py","research178.py","run178.py",
                     "verify178.py","package178.py"):
            data = (OWN/name).read_bytes()
            ast.parse(data,filename=str(OWN/name))
            source_validation.append({"name":name,"sha256":sha(data),"syntax":"PASS"})
        write("source-validation.json",{"python_syntax":source_validation,
                                       "json_parsed":checked_json,
                                       "markdown_whitespace":checked_markdown})
        old = json.loads((OWN/"inputs.json").read_bytes())
        for r in old["strict"]:
            assert record(r["path"]) == r
        # Late receipts are allowed only as newly frozen strict inputs, never replacements.
        external = {r["path"]:r for r in old["strict"]}
        for dirname,pattern in [("frontier/experiments","i177-parent-*"),
                                ("frontier/iterations","iteration178*")]:
            for path in (ROOT/dirname).glob(pattern):
                if path.is_file():
                    rel = str(path.relative_to(ROOT))
                    external.setdefault(rel,record(rel))
        controls = [REL+n for n in ("inventory.json","prevalidation.json","seal.json")]
        owned = {REPORT}
        for directory in (OWN,SOURCE):
            for path in directory.rglob("*"):
                assert not path.is_symlink()
                if path.is_file():
                    owned.add(str(path.relative_to(ROOT)))
        assert not owned & set(controls)
        inv = {"iteration":178,"owned":[record(p) for p in sorted(owned)],
               "external":[external[p] for p in sorted(external)],
               "context":old["context"],"controls":controls,
               "replays":[{"function":"mandatory","payload":REL+"mandatory-attempt-05.json"},
                          {"function":"analytic","payload":REL+"analytic-attempt-05.json"}],
               "policy":"Immutable-first strict mathematics; four current-stable context exceptions only"}
        write("inventory.json",inv)
        print(json.dumps({"owned":len(owned),"external":len(external),"contexts":4}))
    elif mode == "seal":
        assert (OWN/"inventory.json").exists() and not (OWN/"prevalidation.json").exists()
        result = subprocess.run([sys.executable,"-I","-B",str(OWN/"verify178.py"),"--prevalidate"],
                                capture_output=True)
        if result.returncode or result.stderr:
            # Retain every failed prevalidation without weakening the frozen inventory.
            # Its new files require a new development inventory before any seal.
            with (OWN/"prevalidation-failed-stdout.txt").open("xb") as f:
                f.write(result.stdout)
            with (OWN/"prevalidation-failed-stderr.txt").open("xb") as f:
                f.write(result.stderr)
            raise RuntimeError(result.stderr.decode())
        pre = json.loads(result.stdout)
        assert pre["status"] == "PASS" and pre["prevalidation"]
        with (OWN/"prevalidation.json").open("xb") as f:
            f.write(result.stdout)
        seal = {"iteration":178,"inventory_sha256":record(REL+"inventory.json")["sha256"],
                "prevalidation_sha256":record(REL+"prevalidation.json")["sha256"],
                "report_sha256":record(REPORT)["sha256"],
                "verifier_sha256":record(REL+"verify178.py")["sha256"],
                "creation":"Exactly one exclusive seal, after successful prevalidation; never reseal."}
        write("seal.json",seal)
        print(json.dumps({"status":"SEALED","seal_sha256":record(REL+"seal.json")["sha256"],
                          "prevalidation_runtime_seconds":pre["runtime_seconds"]},sort_keys=True))
    else:
        raise ValueError(mode)


if __name__ == "__main__":
    main()
