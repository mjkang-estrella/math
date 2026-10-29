import subprocess,sys,json,hashlib,os
from pathlib import Path
r=Path(__file__).resolve().parent;s=r.parent/'sol-factorial-product-manuscript-packet-r1';d=r/'extracted'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
os.environ['PYTHONPATH']=str(s/'python-deps')
for script,args in [('certificate.py',[]),('build_paper.py',[]),('pack.py',[str(r/'rebuilt.zip')]),('portable_replay.py',[str(r/'replay')])]:
 p=subprocess.run([sys.executable,str(d/script)]+args,cwd=d,capture_output=True,text=True)
 (r/(script+'.log')).write_text(p.stdout+p.stderr)
 assert p.returncode==0,(script,p.stderr[-2000:])
assert (d/'paper.pdf').read_bytes()==(s/'paper.pdf').read_bytes()
assert (r/'rebuilt.zip').read_bytes()==(s/'packet.zip').read_bytes()
q=json.loads((r/'replay/portable-receipt.json').read_text())
assert q['actual_declarations']==31 and q['mathematical_compilelog_bytes']==0
assert (r/'replay/logs/FullAudit.log').read_bytes()==(r.parent/'sol-factorial-product-source-formal-r1/logs/FullAudit.log').read_bytes()
f=json.loads((r/'freeze.json').read_text())
for n,h in f['files'].items():assert sha(s/n)==h,n
o={'status':'ROOT_EXTRACTED_REBUILD_AND_PORTABLE_REPLAY_PASS','mathematical_modules':1,'declarations':31,'paper_sha256':sha(d/'paper.pdf'),'packet_sha256':sha(r/'rebuilt.zip'),'audit_byte_identical_to_formal_component':True,'frozen_reverified':len(f['files']),'credit':0,'counts':[8,38],'qualifications':['Legacy replay aborts on historical mutable NEXT hash; unchanged preserved. Portable replay checks shipped copies, binary/pins/upstream artifacts and exhaustive actual audit.','PDF authoring marker failed under fixed cap; root read-only review does not retry it.','Root first lookup of packet/replay.py was wrong; portable_replay.py read instead.']}
(r/'ROOT-REBUILD.json').write_text(json.dumps(o,indent=2)+'\n');print(json.dumps(o))
