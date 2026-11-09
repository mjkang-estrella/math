from pathlib import Path
import hashlib,json,zipfile
D=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
# Final read-only recheck immediately before packaging.
for stem in ['inputs','dependency-inputs','font-inputs']:
 b=json.loads((D/f'{stem}-before.json').read_text());assert all(sha(Path(p))==h for p,h in b.items())
assert sha(D/'pdtar-source.zip')=='3a599c52f33e8fcbed9294de07b9b6a549606b7d6bd693fdfd834304a67173b4'
assert len(list((D/'qa').glob('page-*.png')))==11
assert (D/'paper.md').read_text().split('```json\n',1)[1].rsplit('```',1)[0]==(D/'evidence/replay-result.json').read_text()
for name in ['render-pins','raster-pins']:
 r=json.loads((D/f'logs/{name}.receipt.json').read_text());assert r['returncode']==0 and r['cap_reason'] is None
exclude={'pdtar-full-dossier.zip','DOSSIER-MANIFEST.json','DELIVERY-SHA256.json','package-validation.json'}
files=sorted(p for p in D.rglob('*') if p.is_file() and p.relative_to(D).parts[0]!='tmp' and p.name not in exclude and not p.name.startswith('package-final'))
man={str(p.relative_to(D)):sha(p) for p in files}
(D/'DOSSIER-MANIFEST.json').write_text(json.dumps({'algorithm':'SHA256','scope':'All ZIP files except this manifest itself. Temporary dependency cache and active packaging logs omitted. DELIVERY-SHA256.json and package-validation.json are external noncircular receipts.','files':man},indent=2)+'\n')
with zipfile.ZipFile(D/'pdtar-full-dossier.zip','w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for p in files+[D/'DOSSIER-MANIFEST.json']:z.write(p,str(p.relative_to(D)))
with zipfile.ZipFile(D/'pdtar-full-dossier.zip') as z:
 assert z.testzip() is None
 assert set(z.namelist())==set(man)|{'DOSSIER-MANIFEST.json'}
 for p,h in man.items():assert hashlib.sha256(z.read(p)).hexdigest()==h
 assert z.read('pdtar-source.zip')==(D/'pdtar-source.zip').read_bytes()
(D/'DELIVERY-SHA256.json').write_text(json.dumps({p:sha(D/p) for p in ['paper.pdf','paper.md','PROOF.md','pdtar-source.zip','pdtar-full-dossier.zip','DOSSIER-MANIFEST.json']},indent=2)+'\n')
(D/'package-validation.json').write_text(json.dumps({'status':'PASS','zip_members':len(man)+1,'all_member_hashes_match':True,'embedded_proof_packet_byte_identical':True,'all_frozen_inputs_unchanged_at_packaging':True,'lean_run':False},indent=2)+'\n')
print('PASS:',len(man)+1,'members; full dossier',sha(D/'pdtar-full-dossier.zip'))
