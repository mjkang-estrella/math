import os,json,fnmatch,re,hashlib
from pathlib import Path
ROOT=Path("frontier/campaigns/2026-10-14/fresh-structural-discovery-r160")
patterns=json.loads((ROOT/"tools/isolation.json").read_text())["patterns"]
rx=re.compile(r"sandpile|chip[ -]?firing|critical group|zero[ -]forcing|maximum nullity|minimum rank|Smith normal|Laplacian",re.I)
out={"read":[],"pruned":[],"non_utf8":[],"errors":[],"hits":[]}
def walk(p):
 with os.scandir(p) as it:
  for e in it:
   q=Path(e.path);s=q.as_posix().removeprefix("./");low=s.casefold()
   if e.is_symlink() or any(fnmatch.fnmatchcase(low,v) for v in patterns):out["pruned"].append(s);continue
   if e.is_dir(follow_symlinks=False):walk(q)
   elif e.is_file(follow_symlinks=False):
    try:
     b=q.read_bytes();t=b.decode("utf-8")
    except UnicodeDecodeError:out["non_utf8"].append(s);continue
    except OSError as ex:out["errors"].append([s,str(ex)]);continue
    out["read"].append({"path":s,"bytes":len(b),"sha256":hashlib.sha256(b).hexdigest()})
    hits=[{"line":i,"text":l} for i,l in enumerate(t.splitlines(),1) if rx.search(l)]
    if hits:out["hits"].append({"path":s,"matches":hits})
walk(Path("."))
(ROOT/"private/history-screen01.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps({k:len(v) for k,v in out.items()}))
for x in out["hits"]:
 print(x["path"])
 for m in x["matches"][:3]:print(m["line"],m["text"][:600])
