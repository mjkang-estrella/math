"""Exact I182 integration scope and post-ledger read-only replay."""
import ast
import hashlib
import json
import re
import runpy
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REPO = ROOT.parent
BASE = ROOT/"frontier/experiments/i182_controlled_extension"
SOURCE = ROOT/"frontier/sources/i182_controlled_extension"
RECEIPT = BASE.parent/"i182-parent-integration.json"
ARCHIVE = ROOT/"frontier/iterations/iteration183-cptp-survival-factory-astra-task.json"
LEDGERS = ["README.md","frontier/README.md","frontier/TEN-FINDINGS.md","frontier/iterations/README.md"]
PARENT = ["frontier/experiments/i182-parent-"+name for name in (
    "validate.py","certificates.py","integrate.py","precheck.json","replay-stdout.json",
    "replay-stderr.txt","verification.json","certificates.json")]
PARENT += ["frontier/iterations/i182-controlled-extension-parent-disposition.md",
           "frontier/iterations/iteration183-cptp-survival-brief.md"]


def git(*args):
    return subprocess.check_output(["git","-C",str(REPO),*args],text=True)


def main():
    preflight = sys.argv[1:] == ["--preflight"]
    assert preflight or not sys.argv[1:]
    assert not RECEIPT.exists()
    validator = runpy.run_path(str(BASE.parent/"i182-parent-validate.py"))
    before = validator["authenticate"]()
    inv = json.loads((BASE/"inventory.json").read_bytes())
    owned = {BASE/z["name"] for z in inv["files"]}
    owned |= {ROOT/"frontier/iterations/i182-controlled-extension.md",
              SOURCE/"literature.md"}
    controls = {BASE/n for n in ("inventory.json","prevalidation.json","seal.json")}
    paths = owned | controls | {ROOT/n for n in PARENT+LEDGERS} | {ARCHIVE}
    for name in ("verification","certificates"):
        assert json.loads((BASE.parent/("i182-parent-"+name+".json")).read_bytes())["status"] == "PASS"
    assert not git("diff","--cached","--name-only").strip()
    assert set(git("diff","--name-only").splitlines()) == {"openai-proof-research/"+n for n in LEDGERS}
    py = js = links = 0
    empty,warnings = [],[]
    for p in sorted(paths):
        if preflight and p == ARCHIVE and not p.exists():
            continue
        raw = p.read_bytes()
        if not raw:
            assert p.name.endswith(("-stderr.txt",".stdout",".stderr"))
            empty.append(str(p.relative_to(ROOT)))
        elif p.name.endswith((".py",".py.disabled")):
            ast.parse(raw,filename=str(p))
            py += 1
        elif p.suffix == ".json":
            json.loads(raw)
            js += 1
        if p.suffix == ".md":
            for target in re.findall(r"\]\(([^)\s]+)\)",raw.decode()):
                if "://" in target or target.startswith(("mailto:","#")):
                    continue
                dest = (p.parent/target.split("#",1)[0]).resolve()
                assert dest.exists() or (preflight and dest == ARCHIVE),(p,target)
                links += 1
        check = subprocess.run(["git","-C",str(REPO),"diff","--no-index","--check",
                                "--","/dev/null",str(p)],capture_output=True,text=True)
        assert not check.stderr and check.returncode in (0,1,2,3)
        if check.returncode & 2:
            assert p in owned and check.stdout,"Unexpected parent whitespace issue"
            warnings.append(dict(path=str(p.relative_to(ROOT)),output=check.stdout,preserved="sealed bytes"))
        else:
            assert not check.stdout
    subprocess.run(["git","-C",str(REPO),"diff","--check"],check=True)
    replay = subprocess.run([sys.executable,"-I","-B",str(BASE/"verify182.py")],
                            capture_output=True,cwd=ROOT,timeout=1200)
    assert replay.returncode == 0 and not replay.stderr,replay.stderr
    result = json.loads(replay.stdout)
    assert result["status"] == "PASS" and result["owned_files"] == 25
    assert len(result["blocked_probes"]) == 8 and all(z["status"] == "BLOCKED" for z in result["blocked_probes"])
    assert before == validator["authenticate"]()
    frozen = {z["path"]: z["sha256"] for z in json.loads((BASE/"inputs.json").read_bytes())["context"]}
    drift = {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() != frozen[p] for p in LEDGERS}
    assert all(drift.values())
    receipt = dict(status="PASS",scope=sorted(str(p.relative_to(REPO)) for p in paths|{RECEIPT}),
                   scope_count=len(paths)+1,python_parsed=py,json_parsed=js,
                   local_links_checked=links,preserved_empty_artifacts=empty,
                   retained_whitespace_warnings=warnings,non_context_bindings="unchanged",
                   post_integration_replay=result,post_integration_stderr="empty",
                   context_policy_test="All four ledgers differ from the freeze; verifier reads no context; strict bindings stable.",
                   clean_clone_reconstruction="not tested")
    if not preflight:
        with RECEIPT.open("x") as out:
            json.dump(receipt,out,indent=2,sort_keys=True)
            out.write("\n")
    print(json.dumps({k:v for k,v in receipt.items() if k not in ("scope","post_integration_replay")},indent=2))
    print("Post-integration replay PASS; mandatory",
          round(result["mandatory_replay_seconds"],4),"s; extension",
          round(result["extension_replay_seconds"],4),"s")


if __name__ == "__main__":
    main()
