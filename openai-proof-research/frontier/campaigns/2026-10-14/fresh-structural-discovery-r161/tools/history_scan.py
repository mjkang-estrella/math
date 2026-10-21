import os,json,fnmatch,re,hashlib
from pathlib import Path
R=Path("frontier/campaigns/2026-10-14/fresh-structural-discovery-r161")
p=json.loads((R/"isolation-policy.json").read_text())
rx=re.compile(r"positive[ -]semidefinite.{0,35}rank|PSD.{0,25}(?:rank|factor|matching)|shifted.{0,25}matching|matching.{0,30}(?:slack|smoothing|polytope|table)|orthogonal.{0,15}splitting|fourier.{0,20}(?:smoothing|recenter)|tseitin|Grigoriev|Braun.{0,15}Pokutta",re.I)
excluded=[];admitted=[];hits=[];bad=[];errors=[]
def reject(path):
 s=path.as_posix().lower();parts=s.split("/")
 if s==str(R).lower() or s.startswith(str(R).lower()+"/"):return "own root"
 if path.name.lower()==p["shared_filename"].lower():return "shared journal"
 if any(x in p["directory_names"] for x in parts):return "dependency/git"
 for g in p["case_insensitive_full_path_globs"]:
  if fnmatch.fnmatchcase(s,g):return g
 for x in p["coarse_component_substring_exclusions"]:
  if any(x.lower() in component for component in parts):return "coarse:"+x
 if path.is_symlink():return "symlink"
 return None
for base,ds,fs in os.walk(".",topdown=True,followlinks=False):
 kept=[]
 for n in sorted(ds):
  path=Path(base)/n;reason=reject(path)
  if reason:excluded.append({"path":str(path),"reason":reason,"directory":True})
  else:kept.append(n)
 ds[:]=kept
 for n in sorted(fs):
  path=Path(base)/n;reason=reject(path)
  if reason:excluded.append({"path":str(path),"reason":reason,"directory":False});continue
  try:b=path.read_bytes()
  except OSError as e:errors.append([str(path),str(e)]);continue
  try:s=b.decode("utf-8")
  except UnicodeDecodeError:bad.append(str(path));continue
  admitted.append({"path":str(path),"size":len(b),"sha256":hashlib.sha256(b).hexdigest()})
  lines=[{"line":i,"text":line} for i,line in enumerate(s.splitlines(),1) if rx.search(line)]
  if lines:hits.append({"path":str(path),"matches":lines})
out={"query":rx.pattern,"policy":"isolation-policy.json","pruned":excluded,"admitted_utf8":admitted,"non_utf8":bad,"errors":errors,"hits":hits,"limits":"Decoded all eligible UTF8 including nonmatching files; coarse pruning and opaque aliases prevent exhaustive/authored-only certificates. No filesize cutoff."}
(R/"private/history-scan01.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps({"decoded":len(admitted),"pruned":len(excluded),"non_utf8":len(bad),"errors":len(errors),"hit_files":len(hits)}))
for h in hits:print(h["path"],len(h["matches"]))
