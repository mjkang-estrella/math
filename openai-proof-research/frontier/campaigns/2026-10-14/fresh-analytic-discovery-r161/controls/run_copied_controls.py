"""Three bounded copied-fixture controls; all mutation is under this exclusive root."""
from pathlib import Path
import hashlib,json,shutil,subprocess,sys
R=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r161')
C=R/'private/controls';C.mkdir(exist_ok=True)
def sha(b):return hashlib.sha256(b).hexdigest()
baseline=C/'baseline';baseline.mkdir()
source=R/'private/source/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/build/main.tex'
shutil.copyfile(source,baseline/'source-main.tex')
shutil.copyfile(R/'FROZEN-STATEMENT.md',baseline/'statement.md')
(baseline/'FINAL.md').write_text('Copied artifact-control fixture only. No mathematical gate.\n')
(baseline/'REPORT.md').write_text('Protected source copy and original statement copy; new exact membership, no inherited manifest.\n')
files=[]
for p in sorted([baseline/'source-main.tex',baseline/'statement.md']):
 b=p.read_bytes();files.append({'path':p.name,'bytes':len(b),'sha256':sha(b)})
(baseline/'MANIFEST.json').write_text(json.dumps({'outside_envelopes':['FINAL.md','MANIFEST.json','REPORT.md'],'files':files},indent=2)+'\n')
anchors={x:sha((baseline/x).read_bytes()) for x in ['FINAL.md','MANIFEST.json','REPORT.md']}
for name in ['changed','extra']:shutil.copytree(baseline,C/name)
with (C/'changed'/'statement.md').open('ab') as f:f.write(b'copied corruption control\n')
(C/'extra'/'unexpected.txt').write_text('copied extra membership control\n')
results=[]
for name,expected in [('baseline',0),('changed',1),('extra',1)]:
 cmd=[sys.executable,str(R/'verify_packet.py'),'--root',str(C/name),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']]
 result=subprocess.run(cmd,text=True,capture_output=True,check=False)
 assert result.returncode==expected,(name,result.stdout,result.stderr)
 results.append({'fixture':name,'expected_exit':expected,'actual_exit':result.returncode,'stdout':result.stdout,'stderr':result.stderr})
(R/'controls/results.json').write_text(json.dumps({'copied_source_original':str(source.relative_to(R)),'copied_statement_original':'FROZEN-STATEMENT.md','explicit_fixture_anchors':anchors,'results':results,'mathematical_gate':False},indent=2)+'\n')
print(json.dumps(results,indent=2))
