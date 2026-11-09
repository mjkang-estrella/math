import os,json,fnmatch,re,hashlib
from pathlib import Path
R=Path("frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r158")
c=json.loads((R/"packet/private/guards.json").read_text())
def forbidden(p):
 s=p.as_posix().casefold()
 return s==c["own_root"] or s.startswith(c["own_root"]+"/") or any(x in s for x in c["substrings"]) or any(fnmatch.fnmatchcase(s,x) for x in c["wildcards"])
pat=re.compile(r"zariski.{0,45}multiplicity|multiplicity.{0,45}(?:zariski|topolog)|Seifert|Brieskorn|Arnold.{0,30}corank|Milnor.{0,30}(?:fibr|link|number)|h-cobord|exotic.{0,12}sphere|Hertling|Mase|strong approximation|determinant.{0,25}(?:torus|cancell)|hermitian.{0,25}lattice",re.I)
res=[];read=0;binary=0;pruned=0
stack=[Path(".")]
while stack:
 d=stack.pop()
 for e in sorted(os.scandir(d),key=lambda x:x.name):
  p=Path(e.path)
  if forbidden(p):pruned+=1;continue
  if e.is_symlink():continue
  if e.is_dir(follow_symlinks=False):stack.append(p);continue
  if not e.is_file(follow_symlinks=False):continue
  s=p.as_posix().casefold()
  if not any(x in s.split("/") for x in ["campaigns","iterations","experiments","proposals","scouts","notes","findings"]):continue
  b=p.read_bytes()
  try:t=b.decode("utf8")
  except UnicodeDecodeError:binary+=1;continue
  read+=1
  ms=list(pat.finditer(t))
  if ms:
   res.append({"path":p.as_posix(),"bytes":len(b),"sha256":hashlib.sha256(b).hexdigest(),"matches":[{"char":m.start(),"line":t.count("\n",0,m.start())+1,"text":t[max(0,m.start()-60):min(len(t),m.end()+100)].replace("\n"," ")} for m in ms]})
(R/"packet/private/history-navigation.json").write_text(json.dumps({"eligible_utf8":read,"nonutf8":binary,"pruned_paths":pruned,"hits":res},indent=2)+"\n")
print("eligible",read,"nonutf8",binary,"hits",len(res))
for h in res:
 print(h["path"],"matches",len(h["matches"]))
 for m in h["matches"][:3]:print(" ",m["line"],m["text"])
