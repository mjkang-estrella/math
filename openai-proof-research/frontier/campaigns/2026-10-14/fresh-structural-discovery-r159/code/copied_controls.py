from pathlib import Path
import hashlib,json,os,stat,subprocess,sys
from verify import inventory,digest,ENVELOPES
ROOT=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r159')
fixture=ROOT/'controls/selected-fixture'
if fixture.exists():raise SystemExit('refusing to overwrite a distinct controls run')
fixture.mkdir()
selected=[]
for source,dest in [('notes/02-integrated-reduction-and-ending.md','calculation.md'),('code/biclique_routes.py','construction.py'),('receipts/biclique-routes.json','finite.json')]:
 b=(ROOT/source).read_bytes();(fixture/dest).write_bytes(b);selected.append({'source':source,'selected_copy':dest,'bytes':len(b),'sha256':digest(b)})
(fixture/'FINAL.md').write_text('Three-member selected-copy fixture only. Not the original research packet.\n')
(fixture/'REPORT.md').write_text('Artifact controls only. No mathematical gate. Own exact membership; no inherited manifest.\n')
f,d=inventory(fixture);m={'format':'r159-exact-payload-v1','outside_envelopes':sorted(ENVELOPES),'files':{k:v for k,v in f.items() if k not in ENVELOPES},'directories':d}
(fixture/'MANIFEST.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
anchors={k:digest((fixture/k).read_bytes()) for k in ENVELOPES}
def snapshot():
 out=[]
 for p in sorted([fixture]+list(fixture.rglob('*'))):
  st=p.lstat();out.append({'path':str(p.relative_to(fixture)),'mode':st.st_mode,'links':st.st_nlink,'size':st.st_size,'mtime_ns':st.st_mtime_ns,'sha256':digest(p.read_bytes()) if p.is_file() else None})
 return out
rows=[]
def run(name,expected,override=None):
 before=snapshot();a=dict(anchors);a.update(override or {})
 cmd=[sys.executable,str(ROOT/'code/verify.py'),str(fixture),'--final',a['FINAL.md'],'--manifest',a['MANIFEST.json'],'--report',a['REPORT.md']]
 proc=subprocess.run(cmd,capture_output=True,text=True,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
 after=snapshot();assert before==after,(name,'verifier mutated copy');assert (proc.returncode==0)==expected,(name,proc.stdout,proc.stderr)
 rows.append({'name':name,'expected_accept':expected,'exit_code':proc.returncode,'output':proc.stdout.strip(),'before':before,'after_equal':True})
run('baseline',True)
p=fixture/'calculation.md';b=p.read_bytes();p.write_bytes(b+b'changed\n');run('changed-payload',False);p.write_bytes(b)
p.unlink();run('missing-payload',False);p.write_bytes(b)
p=fixture/'.extra';p.write_text('extra\n');run('hidden-extra',False);p.unlink()
p=fixture/'empty';p.mkdir();run('extra-empty-directory',False);p.rmdir()
run('wrong-manifest-anchor',False,{'MANIFEST.json':'0'*64})
p=fixture/'REPORT.md';b=p.read_bytes();p.write_bytes(b+b'changed\n');run('changed-report',False);p.write_bytes(b)
p=fixture/'FINAL.md';b=p.read_bytes();p.write_bytes(b+b'changed\n');run('changed-final',False);p.write_bytes(b)
run('restored',True)
(ROOT/'receipts/copied-controls.json').write_text(json.dumps({'selected_membership':selected,'fixture_anchors':anchors,'controls':rows,'scope':'Copied artifact controls only; no original packet was mutated; each verifier call read-only.'},indent=2)+'\n')
print(json.dumps({'controls':len(rows),'accepted':[r['name'] for r in rows if r['exit_code']==0],'all_expected':True,'all_read_only':True}))
