from pathlib import Path
import hashlib,json,zipfile,io,shutil,subprocess,sys
b=Path(__file__).resolve().parent
sha=lambda x:hashlib.sha256(x).hexdigest()
names=['main.tex','paper.pdf','build_paper.py','README.md','PROOF.md','FINAL-RESULT.md','provenance.json','pins.json','pin_check.py','verify.py','build_packet.py','input-hashes-before.json','input-hashes-after.json','paper-qa.json']
for d in ['formal','inputs','evidence','failures']:
 names += [str(p.relative_to(b)) for p in (b/d).rglob('*') if p.is_file()]
assert not any(Path(n).suffix in ['.olean','.ilean','.ir','.o'] for n in names)
payload={n:(b/n).read_bytes() for n in sorted(names)}
payload['MANIFEST.json']=(json.dumps({n:sha(d) for n,d in payload.items()},indent=2,sort_keys=True)+'\n').encode()
def make():
 out=io.BytesIO()
 with zipfile.ZipFile(out,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
  for n,d in sorted(payload.items()):
   i=zipfile.ZipInfo(n,(2026,10,29,0,0,0));i.create_system=3;i.external_attr=0o100644<<16;i.compress_type=zipfile.ZIP_DEFLATED;z.writestr(i,d,compresslevel=9)
 return out.getvalue()
data=make();assert data==make();(b/'cascade-source-packet.zip').write_bytes(data)
out=b/'extracted-replay';assert not out.exists();out.mkdir()
with zipfile.ZipFile(io.BytesIO(data)) as z:
 assert z.namelist()==sorted(payload)
 for n in z.namelist():assert not Path(n).is_absolute() and '..' not in Path(n).parts
 z.extractall(out)
for n,h in json.loads((out/'MANIFEST.json').read_text()).items():assert sha((out/n).read_bytes())==h
p=subprocess.run([sys.executable,'verify.py'],cwd=out,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=1900)
(b/'extracted-replay.log').write_text(p.stdout);assert p.returncode==0,p.stdout
for n,h in json.loads((out/'MANIFEST.json').read_text()).items():assert sha((out/n).read_bytes())==h
assert (out/'verification/OriginAudit.log').read_bytes()==(b/'evidence/OriginAudit.log').read_bytes()
records=json.loads((out/'verification/replay.json').read_text());summary=json.loads((out/'verification/audit-summary.json').read_text())
r={'status':'PASS final root extracted source replay; independent review complete','zip_sha256':sha(data),'PDF_sha256':sha((b/'paper.pdf').read_bytes()),'files':len(payload),'sorted_fixed_timestamp':True,'archive_rebuild_identical':True,'extraction_hashes_before_after_pass':True,'origin_audit_byte_identical':True,'origin_declarations':summary['origin_declarations'],'compiled_modules_including_audit':len(records),'peak_group_RSS':max(x['peak_group_RSS'] for x in records),'all_group_RSS_strictly_below_3GiB':all(x['peak_group_RSS']<3*1024**3 for x in records),'scope':'one geometric-rate refutation; final root decision is external to replay','acceptance':False}
(b/'packet-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
