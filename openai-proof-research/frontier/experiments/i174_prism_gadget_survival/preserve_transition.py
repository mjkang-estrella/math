"""Preserve a failed build and a fully authenticated parent-document update."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
SOURCE = ROOT/"frontier/sources/i174_prism_gadget_survival"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def save(path,data):
    with path.open("xb") as f:
        f.write(data)


if __name__ == "__main__":
    assert not (HERE/"inventory.json").exists()
    assert not (HERE/"seal.json").exists()
    for name in ("package.py","verify.py","authenticate.py","mathkit.py","research.py","run.py"):
        save(HERE/("build-failure-01-"+name+".disabled"),(HERE/name).read_bytes())
    report = ROOT/"frontier/iterations/i174-prism-gadget-survival.md"
    save(HERE/"build-failure-01-report.md",report.read_bytes())
    result = subprocess.run([sys.executable,"-I","-B",str(HERE/"package.py"),"build"],
                            capture_output=True)
    assert result.returncode == 1 and not result.stdout and b"AssertionError" in result.stderr
    save(HERE/"build-failure-01-stdout.txt",result.stdout)
    save(HERE/"build-failure-01-stderr.txt",result.stderr)
    auth = json.loads((SOURCE/"authentication.json").read_bytes())
    path = "frontier/iterations/i173-brace-high-loss-octagons-parent-disposition.md"
    entry = next(x for x in auth["bindings"] if x["path"] == path)
    current = (ROOT/path).read_bytes()
    start = current.index(b"The first full staged")
    end = current.index(b"## Mathematical verdicts",start)
    old = current[:start]+current[end:]
    assert len(old) == entry["size"] and sha(old) == entry["sha256"]
    oldpath = SOURCE/"parent-disposition-initial.md"
    newpath = SOURCE/"parent-disposition-reviewed-current.md"
    deltapath = SOURCE/"parent-disposition-inserted-note.txt"
    save(oldpath,old)
    save(newpath,current)
    save(deltapath,current[start:end])
    transition = dict(path=path,old_sha256=sha(old),new_sha256=sha(current),
                      old_size=len(old),new_size=len(current),
                      old_snapshot=str(oldpath.relative_to(ROOT)),
                      new_snapshot=str(newpath.relative_to(ROOT)),
                      inserted_note=str(deltapath.relative_to(ROOT)),
                      reason="Concurrent parent addition: 504-byte staged whitespace-check note; no mathematical change",
                      policy="Explicit reviewed pre-seal transition, both versions bound; not a context exemption",
                      failed_build=dict(returncode=1,stdout="empty",stderr="build-failure-01-stderr.txt"))
    save(SOURCE/"parent-disposition-transition.json",
         (json.dumps(transition,indent=2,sort_keys=True)+"\n").encode())
    print(json.dumps(transition,indent=2))
