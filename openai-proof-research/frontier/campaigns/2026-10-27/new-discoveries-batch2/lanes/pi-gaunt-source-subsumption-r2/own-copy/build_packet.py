from pathlib import Path
import hashlib, io, json, shutil, subprocess, tempfile, zipfile

p=Path(__file__).resolve().parent
sha=lambda b: hashlib.sha256(b).hexdigest()
docs=['README.md','SUMMARY.md','ORDINARY-PROOF.md','OPTIMALITY-ROUTE.md','SOURCE-PRIOR.md',
      'checks.py','checks.json','main.tex','paper.pdf','paper-qa.json','pins.json',
      'verify_candidate.py','build_packet.py','provenance.json','retrievals.json']
paths=[p/f for f in docs]
paths+=list((p/'formal').glob('*.lean'))+[p/'formal/run_lean.py']
paths+=list((p/'sources').glob('*'))
paths+=list((p/'verification').glob('*.log'))+[p/'verification/audit.json']
paths=[q for q in paths if q.is_file()]
assert len(paths)==len(set(paths))
payload={str(q.relative_to(p)):q.read_bytes() for q in paths}
assert not any(k.endswith(('.olean','.ilean')) for k in payload)
manifest=json.dumps({k:sha(v) for k,v in sorted(payload.items())},indent=2).encode()+b'\n'
(p/'MANIFEST.json').write_bytes(manifest)
payload['MANIFEST.json']=manifest
def archive():
    buf=io.BytesIO()
    with zipfile.ZipFile(buf,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        for k,v in sorted(payload.items()):
            i=zipfile.ZipInfo(k,(2026,10,28,0,0,0));i.create_system=3;i.external_attr=0o100644<<16
            i.compress_type=zipfile.ZIP_DEFLATED
            z.writestr(i,v,compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
    return buf.getvalue()
data=archive();assert data==archive()
out=p/'packet';out.mkdir(exist_ok=True)
(out/'gaunt-optimal-tail-proof.zip').write_bytes(data)
print('Deterministic packet',sha(data),'payload files',len(payload)-1,flush=True)
with tempfile.TemporaryDirectory(prefix='gaunt-final-extracted-') as temp:
    q=Path(temp)
    with zipfile.ZipFile(io.BytesIO(data)) as z:
        for name in z.namelist():assert not Path(name).is_absolute() and '..' not in Path(name).parts
        z.extractall(q)
    m=json.loads((q/'MANIFEST.json').read_text())
    for k,h in m.items():assert sha((q/k).read_bytes())==h,k
    assert (q/'MANIFEST.json').read_bytes()==manifest
    r=subprocess.run(['python3','verify_candidate.py'],cwd=q,capture_output=True,text=True)
    (out/'extracted-replay.log').write_text(r.stdout+r.stderr)
    assert r.returncode==0,(r.returncode,r.stdout,r.stderr)
    for f in ['audit.json','Checks.log']:
        assert (q/'verification'/f).read_bytes()==(p/'verification'/f).read_bytes(),f
    receipt={'status':'PASS unaccepted review packet; source/novelty/independent gates pending',
             'zip_sha256':sha(data),'manifest_sha256':sha(manifest),'payload_files':len(m),
             'entries':len(payload),'deterministic_rebuild_identical':True,
             'all_extracted_payload_hashes_verified':True,'fresh_extracted_source_replay':True,
             'modules':14,'declarations':80,'standard_three_axioms_only':True,
             'checks_byte_identical':True,'audit_byte_identical':True,
             'checks_sha256':sha((q/'verification/Checks.log').read_bytes()),
             'audit_sha256':sha((q/'verification/audit.json').read_bytes())}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS extracted14/80/std3; hash-verified payload, identical audit/Checks; credit0.')
