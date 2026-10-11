"""Static source, JSON, source-snapshot and report-link checks."""
import ast
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT=Path(__file__).resolve().parents[3]
BASE=Path(__file__).resolve().parent
SOURCES=ROOT/"frontier/sources/i183_cptp_finalization"
REPORT=ROOT/"frontier/iterations/i183-cptp-finalization.md"


if __name__=="__main__":
    assert sys.flags.isolated and sys.dont_write_bytecode
    counts={"python":0,"json":0,"snapshot_rows":0,"local_links":0,"empty_captures":0}
    for path in sorted(list(BASE.rglob("*"))+list(SOURCES.rglob("*"))+[REPORT]):
        assert not path.is_symlink()
        if not path.is_file():continue
        data=path.read_bytes()
        if path.suffix==".py":
            ast.parse(data,filename=path.relative_to(ROOT).as_posix())
            counts["python"]+=1
        if path.suffix==".json":
            obj=json.loads(data)
            counts["json"]+=1
            if path.name.endswith("-invocation.json"):
                for row in obj["sources"]:
                    frozen=(ROOT/row["path"]).read_bytes()
                    assert len(frozen)==row["size"]
                    assert hashlib.sha256(frozen).hexdigest()==row["sha256"]
                    counts["snapshot_rows"]+=1
        if path.suffix==".md":
            for url in re.findall(r"\]\(([^)]+)\)",data.decode()):
                if "://" not in url:
                    assert (path.parent/url.split("#")[0]).resolve().exists(),url
                    counts["local_links"]+=1
        if path.suffix in (".stdout",".stderr") and not data:
            counts["empty_captures"]+=1
    assert not (BASE/"seal.json").exists()
    print(json.dumps({"status":"PASS_PRESEAL_STATIC",**counts},sort_keys=True))
