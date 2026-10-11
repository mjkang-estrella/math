"""Exact I192 integration and inherited post-ledger replay."""
import ast
import json
import re
import runpy
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REPO = ROOT.parent
ARCHIVE = "frontier/iterations/iteration193-equality-bridge-task.json"
RECEIPT = "frontier/experiments/i192-parent-integration.json"
LEDGERS = ["README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"]
PARENT = ["frontier/experiments/i192-parent-" + p for p in
          ("validate.py", "verification.json", "verification.stdout",
           "verification.stderr", "integrate.py")]
PARENT += ["frontier/iterations/i192-exchange-residual-parent-disposition.md",
           "frontier/iterations/iteration193-equality-bridge-brief.md"]


def git(*args):
    return subprocess.check_output(["git", "-C", str(REPO), *args], text=True)


def main():
    preflight = sys.argv[1:] == ["--preflight"]
    assert preflight or not sys.argv[1:]
    assert not (ROOT / RECEIPT).exists()
    validator = runpy.run_path(str(ROOT / PARENT[0]))
    before = validator["authenticate"]()
    reference = validator["REFERENCE"]["authenticate"]()
    assert set(reference["context_drift"]) == set(LEDGERS)
    scope = set(validator["OUTPUTS"]) | set(PARENT + LEDGERS + [ARCHIVE, RECEIPT])
    assert json.loads((ROOT / PARENT[1]).read_bytes())["status"] == "PASS"
    assert not git("diff", "--cached", "--name-only").strip()
    assert set(git("diff", "--name-only").splitlines()) == {
        "openai-proof-research/" + p for p in LEDGERS}
    py = js = links = 0
    empty = []
    for name in sorted(scope - {RECEIPT}):
        p = ROOT / name
        if preflight and name == ARCHIVE and not p.exists():
            continue
        raw = p.read_bytes()
        if not raw:
            assert p.suffix in (".stdout", ".stderr")
            empty.append(name)
        elif p.suffix == ".py":
            ast.parse(raw, filename=name)
            py += 1
        elif p.suffix == ".json":
            json.loads(raw)
            js += 1
        if p.suffix == ".md":
            for target in re.findall(r"\]\(([^)\s]+)\)", raw.decode()):
                if "://" in target or target.startswith(("#", "mailto:")):
                    continue
                dest = (p.parent / target.split("#", 1)[0]).resolve()
                assert dest.exists() or (preflight and dest == ROOT / ARCHIVE), (name, target)
                links += 1
        check = subprocess.run(
            ["git", "-C", str(REPO), "diff", "--no-index", "--check", "--", "/dev/null", str(p)],
            capture_output=True, text=True)
        assert check.returncode in (0, 1) and not check.stdout and not check.stderr, name
    subprocess.run(["git", "-C", str(REPO), "diff", "--check"], check=True)
    replay, proc = validator["replay"]()
    assert not proc.stderr
    assert before == validator["authenticate"]()
    assert reference == validator["REFERENCE"]["authenticate"]()
    receipt = {
        "status": "PASS", "scope": ["openai-proof-research/" + p for p in sorted(scope)],
        "scope_count": len(scope), "python_parsed": py, "json_parsed": js,
        "local_links_checked": links, "preserved_empty_artifacts": empty,
        "post_ledger_replay": replay, "post_ledger_stderr": "empty",
        "all_four_contexts_historically_changed": True, "current_context_stable": True,
        "I192_output_bytes": "unchanged", "I191_output_bytes": "unchanged",
        "I190_output_bytes": "unchanged", "I189_output_bytes": "unchanged",
        "I188_output_bytes": "unchanged", "I187_output_bytes": "unchanged",
        "I183_sealed_bytes": "unchanged",
        "I192_computational_seal": False, "new_mathematical_acceptance": False,
        "local_ear_mechanism": "PARKED", "E183_line": "PARKED",
        "universal_exchange": "UNRESOLVED at J192",
    }
    if not preflight:
        with (ROOT / RECEIPT).open("x") as out:
            json.dump(receipt, out, indent=2, sort_keys=True)
            out.write("\n")
    print(json.dumps({k: receipt[k] for k in (
        "status", "scope_count", "python_parsed", "json_parsed",
        "local_links_checked", "current_context_stable")}))
    print("Inherited post-ledger replay:",
          replay["sealed_reference_replay"]["elapsed_seconds"], "seconds")


if __name__ == "__main__":
    main()
