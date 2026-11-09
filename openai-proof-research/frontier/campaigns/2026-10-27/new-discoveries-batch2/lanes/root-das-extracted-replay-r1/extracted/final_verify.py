from pathlib import Path
import json,hashlib,tarfile,io,gzip,subprocess,sys
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'manifest.json').read_text())
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in {'manifest.json','receipt.json'}}
# Only the final root manifest/receipt are excluded; any nested files remain covered.
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p not in [L/'manifest.json',L/'receipt.json']}
assert actual==set(m),(actual-set(m),set(m)-actual)
assert all(sha(L/n)==h for n,h in m.items())
fr=json.loads((L/'freeze.json').read_text())['scientific']
for e in fr:assert sha(Path(e['original']))==e['sha256']==sha(L/e['copy'])
for base in [L,L/'fresh-replay']:
 sm=json.loads((base/'source-manifest.json').read_text())
 assert all(sha(base/n)==h for n,h in sm.items())
 r=json.loads((base/'replay-receipt.json').read_text())
 assert r['source_endpoint_status']=='PROVED_LITERAL_N5_REFUTATION'
 assert r['actual_declaration_count']==71 and not r['generated_partial_declarations']
 for mod in ['Definitions','Witness','Audit']:
  b=json.loads((base/(mod+'.guard.json')).read_text());assert b['exit_code']==0 and b['reason'] is None
 subprocess.run([sys.executable,str(base/'verify_pins.py')],check=True,stdout=subprocess.DEVNULL)
 subprocess.run([sys.executable,str(base/'audit_verify.py')],check=True,stdout=subprocess.DEVNULL)
assert not any(p.suffix in {'.olean','.ilean','.o','.c'} for p in L.rglob('*') if p.is_file())
ar=json.loads((L/'archive-receipt.json').read_text());assert sha(L/'source-only.tar.gz')==ar['sha256']
buf=io.BytesIO()
with tarfile.open(fileobj=buf,mode='w',format=tarfile.USTAR_FORMAT) as out:
 for name in ar['members']:
  data=(L/name).read_bytes();t=tarfile.TarInfo(name);t.size=len(data);t.mode=0o644;t.mtime=0;t.uid=t.gid=0;t.uname=t.gname='';out.addfile(t,io.BytesIO(data))
assert gzip.compress(buf.getvalue(),mtime=0)==(L/'source-only.tar.gz').read_bytes()
# The audit rechecker rewrites identical receipt bytes; confirm coverage again.
assert all(sha(L/n)==h for n,h in m.items())
receipt={'status':'PASS_LITERAL_FORMAL_COMPONENT_ONLY','endpoint':'Das.literal_universal_bound_false','fresh_extracted_strict_replay':True,'all_71_owned_declarations_audited':True,'partial_declarations':[],'scientific_original_copy_pairs':len(fr),'compiler_and_nine_packages_before_after':True,'manifest_files':len(m),'archive_sha256':ar['sha256'],'published_source':'HOLD','novelty':'HOLD','acceptance':False,'counts':[9,39,40]}
(L/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
