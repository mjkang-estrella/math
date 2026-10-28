#!/usr/bin/env python3
"""Build deterministic final sources, then verify a genuinely fresh extraction."""
from pathlib import Path
import hashlib, io, json, shutil, subprocess, tempfile, zipfile

base=Path(__file__).resolve().parent
batch=base.parents[1]
candidate=batch/'candidates/arcsinh-positive'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paths=sorted(p for p in candidate.rglob('*') if p.is_file()
             and p.relative_to(candidate).as_posix() not in {'MANIFEST.json','acceptance.json'})
assert all(p.suffix not in {'.olean','.ilean'} for p in paths)
assert all('paper-build' not in p.parts for p in paths)
manifest={p.relative_to(candidate).as_posix():sha(p) for p in paths}
(candidate/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
paths=sorted([*paths,candidate/'MANIFEST.json'])
def zip_bytes():
    stream=io.BytesIO()
    with zipfile.ZipFile(stream,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        for p in paths:
            info=zipfile.ZipInfo('arcsinh-positive/'+p.relative_to(candidate).as_posix(),
                                 date_time=(2026,10,28,0,0,0))
            info.create_system=3;info.external_attr=0o100644<<16
            info.compress_type=zipfile.ZIP_DEFLATED
            z.writestr(info,p.read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
    return stream.getvalue()
archive=batch/'candidate-packets/2019-conjecture51-arcsinh-positive-proof.zip'
archive.parent.mkdir(exist_ok=True)
data=zip_bytes();assert data==zip_bytes(),'Non-deterministic archive build'
archive.write_bytes(data)
out=base/'extracted-replay';out.mkdir(exist_ok=True)
with tempfile.TemporaryDirectory(prefix='arcsinh-final-extracted-') as temp:
    temp=Path(temp)
    with zipfile.ZipFile(archive) as z:
        names=z.namelist()
        assert len(names)==len(set(names))==len(manifest)+1
        assert set(names)=={'arcsinh-positive/'+s for s in [*manifest,'MANIFEST.json']}
        assert all(not name.startswith('/') and '..' not in Path(name).parts for name in names)
        z.extractall(temp)
    root=temp/'arcsinh-positive'
    assert (root/'MANIFEST.json').read_bytes()==(candidate/'MANIFEST.json').read_bytes()
    for name,h in manifest.items():assert sha(root/name)==h,name
    r=subprocess.run(['python3','verify_candidate.py'],cwd=root,capture_output=True,text=True)
    (out/'run.log').write_text(r.stdout+r.stderr)
    assert r.returncode==0,(r.returncode,r.stdout,r.stderr)
    for p in (root/'verification').iterdir():shutil.copy2(p,out/p.name)
    for name,h in manifest.items():
        if not name.startswith('verification/'):assert sha(root/name)==h,name
    audit=json.loads((out/'audit.json').read_text())
    assert audit['declarations']==19 and audit['modules']==5
    assert set(audit['allowed_axioms'])=={'propext','Classical.choice','Quot.sound'}
    assert (out/'audit.json').read_bytes()==(candidate/'verification/audit.json').read_bytes()
    assert (out/'Checks.log').read_bytes()==(candidate/'verification/Checks.log').read_bytes()
    assert data==zip_bytes(),'Candidate changed during replay'
    receipt={'status':'PASS fresh final extracted strict replay; parent acceptance separate',
      'archive':str(archive.relative_to(batch)),'archive_sha256':sha(archive),
      'manifest_sha256':sha(candidate/'MANIFEST.json'),
      'payload_files':len(manifest),'zip_entries':len(paths),'deterministic_rebuild_identical':True,
      'candidate_oleans_included':False,'fresh_source_copy':True,'declarations':19,'modules':5,
      'allowed_axioms':audit['allowed_axioms'],'audit_sha256':sha(out/'audit.json'),
      'checks_sha256':sha(out/'Checks.log'),'type_axiom_reports_identical_to_reviewed':True,
      'paper_sha256':sha(candidate/'paper.pdf'),'root_acceptance_embedded':False}
    (base/'final-extracted-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
