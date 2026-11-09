from pathlib import Path
import hashlib,json,zipfile,subprocess,sys,re
L=Path('source');archive=Path('polyomino57-final-edition.zip');baseline=zipfile.ZipFile('frozen-input.zip')
def h(b):return hashlib.sha256(b).hexdigest()
assert h(Path('../root-polyomino57-final-review-freeze-r1/polyomino57-final-review.zip').read_bytes())=='e60bbdc02bf960821eb15113380db18e49d4a6f481e23a7a0719225ca344da74'
oldnames=set(baseline.namelist());report=json.loads(Path('EDIT-REPORT.json').read_text());expected=oldnames|set(report['added'])
with zipfile.ZipFile(archive) as z:
 assert z.namelist()==sorted(expected) and len(z.namelist())==4143
 for i in z.infolist():
  assert i.date_time==(2026,10,29,0,0,0) and i.external_attr==0o644<<16 and i.compress_type==8
  assert not set(Path(i.filename).parts)&{'__pycache__','.lake','dev','extracted','logs-development'}
  assert Path(i.filename).suffix not in {'.olean','.ilean','.o','.so','.a','.pyc','.zip'}
 manifest=json.loads(z.read('MANIFEST.json'));assert set(manifest)==expected-{'MANIFEST.json'}
 for n,v in manifest.items():
  b=z.read(n);assert len(b)==v['bytes'] and h(b)==v['sha256']
 changed={x['path'] for x in report['changed']}|{'MANIFEST.json'}
 assert {n for n in oldnames if z.read(n)!=baseline.read(n)}==changed
 for n in oldnames:
  if n not in changed:assert z.read(n)==baseline.read(n)
 formal=sorted(n for n in z.namelist() if n.startswith('formal/'))
 assert len(formal)==2023 and all(z.read(n)==baseline.read(n) for n in formal)
 root=Path('independent-rebuild');root.mkdir();z.extractall(root)
 for prefix in ['root-polyomino57-final-review-freeze-r1/root-fresh-replay','sol-polyomino57-full-final-review-r1/fresh-replay']:
  inv=z.read('evidence/'+prefix+'/declaration-inventory.json');assert h(inv)=='bb24a892d49115ba1538de2994a2452088cad156d091ed69fa960f09cb50e4c9'
  assert inv==baseline.read('replay-evidence/declaration-inventory.json')
  records=json.loads(inv);log=z.read('evidence/'+prefix+'/logs/FinalAudit.log').decode();found=re.findall(r'AUDIT (\S+) (\S+)\nTYPE (.*?)\nAXIOMS (.*?)\nFLAGS ([^\n]+)',log,re.S)
  assert records==[dict(origin=o,name=n,type=t,axioms=a,flags=f) for o,n,t,a,f in found]
  assert len(records)==5924
before=h((root/'paper.pdf').read_bytes());subprocess.run([sys.executable,str(root/'build_pdf.py')],check=True,timeout=230);assert h((root/'paper.pdf').read_bytes())==before
# Independent ZIP writer: does not import or invoke packet pack.py.
with zipfile.ZipFile('independently-rebuilt.zip','w',compression=8,compresslevel=9) as z:
 for n in sorted(expected):
  entry=zipfile.ZipInfo(n,(2026,10,29,0,0,0));entry.external_attr=0o644<<16;entry.compress_type=8
  z.writestr(entry,(root/n).read_bytes(),compresslevel=9)
assert Path('independently-rebuilt.zip').read_bytes()==archive.read_bytes()
result=dict(status='PASS',entries=4143,payload_entries=4142,all_2023_sources_byte_identical=True,all_5924_actual_records_byte_identical=True,original_evidence_dissent_failures_unchanged=True,exact_payload_and_manifest=True,no_prebuilt_or_nested_archives=True,PDF_byte_identical=True,ZIP_byte_identical=True,independent_zip_implementation=True,frozen_archive_unchanged=True,new_full_replay=False,credit=0,root_acceptance=False)
Path('INDEPENDENT-CHECK.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
