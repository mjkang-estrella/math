from pathlib import Path
import hashlib,json,subprocess,sys,os
r=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r146');f=r/'private/control-fixture'
f.mkdir(exist_ok=False)
def h(b):return hashlib.sha256(b).hexdigest()
b=(r/'GAPS.md').read_bytes();(f/'sample.md').write_bytes(b)
(f/'FINAL.md').write_text('Disposable selected-copy control; no mathematical claim.\n')
(f/'REPORT.md').write_text('Only sample.md is selected. No original manifest inherited.\n')
(f/'MANIFEST.json').write_text(json.dumps(dict(schema='r146-exact-payload-v1',files=[dict(path='sample.md',size=len(b),sha256=h(b))]),indent=2)+'\n')
anchors={name:h((f/name).read_bytes()) for name in ['FINAL.md','MANIFEST.json','REPORT.md']}
def snapshot():return {str(p.relative_to(f)):dict(size=p.stat().st_size,sha256=h(p.read_bytes())) for p in sorted(f.rglob('*')) if p.is_file()}
results=[]
def run(name,want,wrong=False):
 before=snapshot();a=dict(anchors)
 if wrong:a['MANIFEST.json']='0'*64
 proc=subprocess.run([sys.executable,str(r/'verify.py'),'--root',str(f),'--final-sha256',a['FINAL.md'],'--manifest-sha256',a['MANIFEST.json'],'--report-sha256',a['REPORT.md']],cwd=Path.cwd(),env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'},capture_output=True,text=True,timeout=15)
 after=snapshot();assert (proc.returncode==0)==want and before==after
 results.append(dict(name=name,expected_accept=want,returncode=proc.returncode,stdout=proc.stdout.strip(),before=before,after=after,read_only=before==after))
run('selected-copy baseline',True)
(f/'sample.md').write_bytes(b+b'altered\n');run('altered payload',False);(f/'sample.md').write_bytes(b)
(f/'sample.md').unlink();run('missing payload',False);(f/'sample.md').write_bytes(b)
(f/'.hidden-extra').write_text('extra\n');run('hidden extra',False);(f/'.hidden-extra').unlink()
run('wrong detached anchor',False,True)
run('restored selected copy',True)
(r/'CONTROL-RESULTS.json').write_text(json.dumps(dict(selection=dict(original='GAPS.md',sha256=h(b),copied='private/control-fixture/sample.md'),independent_selected_manifest=True,anchors=anchors,results=results),indent=2)+'\n')
print('6 controls matched expectations; all verifier invocations left complete fixture file snapshots unchanged')
