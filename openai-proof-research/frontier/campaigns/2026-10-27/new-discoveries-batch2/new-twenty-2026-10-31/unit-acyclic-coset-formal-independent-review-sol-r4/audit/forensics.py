from pathlib import Path, PurePosixPath
import json, hashlib, tarfile, re, collections
p=Path(__file__).resolve().parent.parent
def read(n): return json.loads((p/n).read_text())
def sha(q): return hashlib.sha256(q.read_bytes()).hexdigest()
def save(n,x): (p/n).write_text(json.dumps(x,indent=2))
pins=read("PINS.json")
binaries={k:{"path":pins[k],"actual":sha(Path(pins[k])),"expected":pins[k+"_sha256"]} for k in ["lean_binary","leanchecker_binary"]}
for v in binaries.values(): assert v["actual"]==v["expected"]
pack=Path(pins["packages_root"])/"mathlib"
head=(pack/".git/HEAD").read_text().strip()
rev=head if not head.startswith("ref: ") else (pack/".git"/head[5:]).read_text().strip()
assert rev==pins["mathlib_revision"]
hashes=[]
for x in read("inputs/author-evidence/results/postchecker-hashes.json"):
 q=p/"src"/(x["module"]+".lean"); o=p/"build"/(x["module"]+".olean")
 hashes.append({**x,"actual_source":sha(q),"actual_olean":sha(o),"source_matches":sha(q)==x["source_sha256"],"olean_matches":sha(o)==x["postchecker_olean_sha256"]})
assert all(x["source_matches"] for x in hashes)
archive=[]
with tarfile.open(p/"inputs/author-evidence/results/340110-source.tar.gz") as t:
 for m in t:
  parts=PurePosixPath(m.name)
  row={"name":m.name,"size":m.size,"safe":not parts.is_absolute() and ".." not in parts.parts and not m.issym() and not m.islnk(),"file":m.isfile()}
  assert row["safe"]
  if m.isfile():
   data=t.extractfile(m).read(); row["sha256"]=hashlib.sha256(data).hexdigest()
   if m.name.endswith(".lean") and "/src/" in "/"+m.name:
    src=p/"src"/parts.name; row["matches_own_source"]=sha(src)==row["sha256"]; assert row["matches_own_source"]
   if parts.name in ["PINS.json","generated-build-plan.json"]: row["content"]=data.decode()
  archive.append(row)
inv=read("audit/independent-inventory.json")
rows={r["name"]:r for r in inv["declarations"]}
locals_=[r for r in rows.values() if r["local"]]
assert set(inv["local_names"])=={r["name"] for r in locals_}
assert len(locals_)==len(inv["local_names"])
assert all(r["type"]!="upstream" and r["body"]!="upstream" for r in locals_)
assert not inv["forbidden"]
missing=sorted({d for r in rows.values() for d in r["dependencies"] if d not in rows})
assert not missing,missing
def closure(name):
 seen=set(); todo=[name]
 while todo:
  n=todo.pop()
  if n in seen: continue
  seen.add(n); todo.extend(rows[n]["dependencies"])
 return sorted(seen)
endpoints=["UnitCoset.refutation","UnitCoset.constant_sequence","UnitCoset.constant_acyclic","UnitCoset.identity_unit","UnitCoset.weak_existence","UnitCoset.unit_iff_replicate","UnitCoset.source_disjoint_bridge","UnitCoset.union_zero_not_subgroup"]
closures={n:closure(n) for n in endpoints}
axes={n:[k for k in ns if rows[k]["axiom"]] for n,ns in closures.items()}
save("audit/endpoint-closures.json",{"closures":closures,"axioms":axes})
# Every declaration gets a source module, explicit source anchor or generated-owner anchor.
origins=[]
for r in locals_:
 file=p/"src"/(r["origin"]+".lean")
 source=file.read_text().splitlines()
 short=r["name"].removeprefix("UnitCoset.")
 candidates=[]
 for i,line in enumerate(source,1):
  m=re.search(r"\b(?:def|abbrev|theorem)\s+(\w+)",line)
  if m and (short==m[1] or short.startswith(m[1]+".")): candidates.append((len(m[1]),i,m[1]))
 anchor=max(candidates,default=None)
 origins.append({"name":r["name"],"module":r["origin"],"source":str(file.relative_to(p)),"line":anchor[1] if anchor else None,"owner":anchor[2] if anchor else "module-generated/private; inspect full typed body","type":r["type"],"body":r["body"],"dependencies":r["dependencies"]})
save("audit/source-origin-table.json",origins)
author=[]
for d in ["inputs/author-receipt","inputs/author-cleanroom-receipt"]:
 for q in sorted((p/d).glob("*.json")):
  v=json.loads(q.read_text()); author.append({"file":str(q.relative_to(p)),"label":v.get("label"),"exit":v.get("exit"),"argv":v.get("argv"),"cwd":v.get("cwd"),"env":v.get("env"),"group_members_left":v.get("group_members_left"),"wall_ms":v.get("wall_ms"),"log_sha256":v.get("log_sha256")})
save("results/author-receipt-independent-index.json",author)
save("results/forensics.json",{"binaries":binaries,"mathlib_HEAD":head,"mathlib_revision":rev,"env_sha256":sha(p/"env.sh"),"postchecker_hashes":hashes,"archive":archive,"audit":{"locals":len(locals_),"closure":len(rows),"endpoint_closure":len(closures["UnitCoset.refutation"]),"axioms":axes,"origins":dict(collections.Counter(r["origin"] for r in locals_))},"pins_original_sha256":sha(p/"inputs/root-restoration/PINS.original-exact.json"),"pins_overwritten_sha256":sha(p/"inputs/root-restoration/PINS.overwritten.json"),"author_exit_counts":dict(collections.Counter(str(v["exit"]) for v in author))})
print(json.dumps(read("results/forensics.json"),indent=2))
