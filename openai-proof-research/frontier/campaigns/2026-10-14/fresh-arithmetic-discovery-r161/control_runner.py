from pathlib import Path
import hashlib,json,shutil,subprocess,sys,os
r=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r161'); c=r/'tiny-controls';p=c/'packet';p.mkdir(parents=True,exist_ok=False)
def h(b):return hashlib.sha256(b).hexdigest()
v=r/'packet/verify_packet.py';before=h(v.read_bytes());shutil.copyfile(v,p/'verify_packet.py')
(p/'FINAL.md').write_text('Tiny copied artifact control only. No mathematical claim.\n')
(p/'payload.txt').write_text('A two-divisor cycle can have a nonzero middle block.\n')
files=[{'path':x.relative_to(p).as_posix(),'bytes':len(x.read_bytes()),'sha256':h(x.read_bytes())} for x in sorted(p.rglob('*')) if x.is_file()]
m={'schema':1,'file_count':len(files),'total_bytes':sum(x['bytes'] for x in files),'files':files};(p/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
report=c/'REPORT.md';report.write_text('Tiny copied fixture; no inherited manifest.\n')
anchors={n:h(f.read_bytes()) for n,f in [('final',p/'FINAL.md'),('manifest',p/'MANIFEST.json'),('report',report)]}
base=[sys.executable,str(p/'verify_packet.py'),'--packet',str(p),'--report',str(report),'--final-sha256',anchors['final'],'--manifest-sha256',anchors['manifest'],'--report-sha256',anchors['report']]
results=[]
def run(label,expected,args=None):
 q=subprocess.run(args or base,text=True,capture_output=True,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'});ok=q.returncode==0
 assert ok==expected,(label,q.stdout,q.stderr)
 results.append({'case':label,'expected_accept':expected,'accepted':ok,'output':(q.stdout+q.stderr).strip()})
run('baseline',True)
x=p/'payload.txt';saved=x.read_bytes();x.write_bytes(saved+b'changed');run('corrupt member',False);x.write_bytes(saved)
x.unlink();run('omitted member',False);x.write_bytes(saved)
y=p/'extra.txt';y.write_text('extra');run('extra member',False);y.unlink()
a=base.copy();a[a.index('--report-sha256')+1]='0'*64;run('wrong detached report anchor',False,a)
run('restored',True)
assert before==h(v.read_bytes())
(r/'packet/private/tiny-control-results.json').write_text(json.dumps({'kind':'artifact controls only','original_verifier_unchanged':True,'results':results},indent=2)+'\n')
(c/'ANCHORS.json').write_text(json.dumps(anchors,indent=2)+'\n')
print(json.dumps({'observations':len(results),'all_expected':True,'original_unchanged':True}))
