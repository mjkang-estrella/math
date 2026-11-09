import pathlib,json,hashlib,sys,tempfile,subprocess
O=pathlib.Path(__file__).resolve().parent
L=O.parent;I=L/"root-mathdb-breadth-intake-r671";R=L/"pi-mathdb-full-corpus-inventory-r301"
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get("size",e.get("bytes")),f"size {p}";assert h(b)==e["sha256"],f"hash {p}"
def payload(root,m):
 exclude={"manifest.json","final-verification-receipt.json"};assert set(m["excluded_exact_paths"])==exclude
 actual={str(p.relative_to(root)) for p in root.rglob("*") if p.is_file()};expected={e["path"] for e in m["files"]};assert len(expected)==len(m["files"]);assert actual-exclude==expected,"extra/missing payload"
 for e in m["files"]:check(root/e["path"],e)
def verify():
 m=json.loads((O/"manifest.json").read_text());payload(O,m)
 for e in json.loads((O/"flat-bindings.json").read_text()):check(pathlib.Path(e["path"]),e)
 im=json.loads((I/"manifest.json").read_text());actual={str(p.relative_to(I)) for p in I.rglob("*") if p.is_file()};assert actual=={e["path"] for e in im["files"]}|{"manifest.json","verification-receipt.json"}
 for e in im["files"]:check(I/e["path"],e)
 for e in json.loads((I/"bindings.json").read_text()):
  for k in ["original","copy"]:check(pathlib.Path(e[k]),dict(size=e["bytes"],sha256=e["sha256"]))
 rm=json.loads((R/"manifest.json").read_text());chunks=[e for e in rm["files"] if e["path"].startswith("corpus/")];assert len(chunks)==20 and len(rm["frozen_inputs"])==8
 for e in chunks+rm["frozen_inputs"]:check(R/e["path"],e)
 cov=json.loads((I/"coverage-delta.json").read_text());assert len(cov)==7683
 sets=[]
 for r in json.loads((I/"active-breadth-reservations.json").read_text()):
  s=set(r["ids"]);assert len(s)==50 and not s&set(map(int,cov)) and not s&set(r["protected_ids"])
  assert all(not s&t for t in sets);sets.append(s)
 assert len(sets)==3
 reserved=set(json.loads((I/"reserved-ids-r672.json").read_text())["ids"]);assert reserved=={e["mathdb_id"] for e in json.loads((I/"queue-r672.json").read_text())}
 ds=json.loads((O/"dispositions.json").read_text());xs=json.loads((O/"literal-records.json").read_text());assert len(ds)==len(xs)==50 and {d["mathdb_id"] for d in ds}==reserved
 by={d["mathdb_id"]:d for d in ds}
 wanted={(x["chunk"],x["line"]):x for x in xs};found=0
 for e in chunks:
  for n,line in enumerate((R/e["path"]).open(),1):
   x=wanted.get((e["path"],n))
   if x is None:continue
   rec=json.loads(line);assert rec==x["record"];d=by[rec["mathdb_id"]];digest=h(json.dumps(rec,ensure_ascii=False,sort_keys=True,separators=(",",":")).encode());assert digest==x["canonical_record_sha256"]==d["canonical_record_sha256"]
   assert d["statement"]==rec["statement"] and d["statement_utf8_sha256"]==h(rec["statement"].encode());assert d["classification"] in {"complete","definition-dependent","scope-ambiguous","incomplete"};assert d["classification_reason"] and d["technical_assessment"] and d["accepted_credit"]==0;found+=1
 assert found==50
 assert len(json.loads((O/"proposals.json").read_text()))<=3
 return dict(integrity="PASS",literal_records=50,chunks=20,frozen_inputs=8,baseline=7683,novelty="HOLD",math="No proposed result")
def negatives():
 result={}
 with tempfile.TemporaryDirectory(dir=O,prefix="negative-fixture-") as t:
  p=pathlib.Path(t);(p/"x").write_bytes(b"abc");m=dict(excluded_exact_paths=["manifest.json","final-verification-receipt.json"],files=[dict(path="x",size=3,sha256=h(b"abc"))]);payload(p,m)
  (p/"fixture-manifest").write_text(json.dumps(m))
  m["files"].append(dict(path="fixture-manifest",size=(p/"fixture-manifest").stat().st_size,sha256=h((p/"fixture-manifest").read_bytes())))
  for mode,b in [("hash",b"abd"),("size",b"abcd")]:
   (p/"x").write_bytes(b)
   try:payload(p,m)
   except AssertionError:
    run=subprocess.run([sys.executable,"-B",str(O/"verify.py"),"--reject-fixture",str(p),mode],capture_output=True,text=True);assert run.returncode!=0;result[mode]=dict(status="rejected",exit=run.returncode)
   else:raise AssertionError(mode+" accepted")
  (p/"x").write_bytes(b"abc");(p/"extra").write_bytes(b"x")
  try:payload(p,m)
  except AssertionError:
   run=subprocess.run([sys.executable,"-B",str(O/"verify.py"),"--reject-fixture",str(p),"extra-file"],capture_output=True,text=True);assert run.returncode!=0;result["extra-file"]=dict(status="rejected",exit=run.returncode)
  else:raise AssertionError("extra accepted")
 return result
if __name__=="__main__":
 try:
  if "--reject-fixture" in sys.argv:
   root=pathlib.Path(sys.argv[2]);m=dict(excluded_exact_paths=["manifest.json","final-verification-receipt.json"],files=[dict(path="x",size=3,sha256=h(b"abc")),dict(path="fixture-manifest",size=(root/"fixture-manifest").stat().st_size,sha256=h((root/"fixture-manifest").read_bytes()))]);payload(root,m)
  else:print(json.dumps(negatives() if "--negative-tests" in sys.argv else verify()))
 except Exception as e:print("FAIL: "+str(e),file=sys.stderr);sys.exit(1)
