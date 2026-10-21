from pathlib import Path
import json,hashlib,subprocess,shutil,os
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/fresh-analytic-discovery-r141')
C=R/'private/controls';C.mkdir(exist_ok=True);F=C/'fixture';F.mkdir(exist_ok=True)
def h(b):return hashlib.sha256(b).hexdigest()
def inv():return {str(p.relative_to(F)):h(p.read_bytes()) for p in F.rglob('*') if p.is_file()}
for name in ['verify.py','DERIVATION.md']:shutil.copyfile(R/name,F/name)
(F/'copied-source.tex').write_bytes((R/'private/source/preprints/Universal-Computation-with-Eventually-Stationary-Navier-Stokes-Forcing-September-27-2026/build/main.tex').read_bytes())
(F/'FINAL.md').write_text('Synthetic selected-copy control. No original seal inherited.\n');(F/'REPORT.md').write_text('Only artifact controls; no mathematical gate.\n')
m={'outside_envelopes':['FINAL.md','MANIFEST.json','REPORT.md'],'directories':[],'files':{p.name:{'size':p.stat().st_size,'sha256':h(p.read_bytes())} for p in F.iterdir() if p.name not in ['FINAL.md','REPORT.md','MANIFEST.json']}}
(F/'MANIFEST.json').write_text(json.dumps(m,sort_keys=True,indent=2)+'\n')
anchors={x:h((F/x).read_bytes()) for x in ['FINAL.md','MANIFEST.json','REPORT.md']};rows=[]
def run(name,expected,wrong=False):
 before=inv();cmd=['python','-B',str(F/'verify.py'),str(F),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256','0'*64 if wrong else anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']];p=subprocess.run(cmd,capture_output=True,text=True);after=inv();ok=(p.returncode==0)==expected and before==after;rows.append({'case':name,'expected_accept':expected,'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'read_only':before==after,'control_ok':ok});assert ok,name
run('baseline',True)
b=(F/'copied-source.tex').read_bytes();(F/'copied-source.tex').write_bytes(b+b'\nmutation\n');run('modified copied source',False);(F/'copied-source.tex').write_bytes(b)
b2=(F/'DERIVATION.md').read_bytes();(F/'DERIVATION.md').unlink();run('missing selected payload',False);(F/'DERIVATION.md').write_bytes(b2)
(F/'.unexpected').write_text('extra');run('extra hidden payload',False);(F/'.unexpected').unlink()
run('wrong external manifest anchor',False,True);run('restored',True)
(C/'results.json').write_text(json.dumps({'scope':'Proportionate synthetic selected-copy fixture with its OWN manifest, not a reduced copy certified by an old manifest. Each verifier invocation was read-only.','anchors':anchors,'cases':rows},indent=2)+'\n')
print('6 artifact controls met expected outcomes; no mathematical gate.')
