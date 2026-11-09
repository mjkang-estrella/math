from pathlib import Path
import zipfile,hashlib,json,subprocess,datetime,os,time,re
p=Path(__file__).parent
names=['Spectral.lean','Semantics.lean','Endpoint.lean','lake-manifest.json','lean-toolchain','leanpath.txt','run.sh']
with zipfile.ZipFile(p/'325519-Lean-packet.zip','w',zipfile.ZIP_DEFLATED) as z:
 for n in names:z.write(p/'lean'/n,n)
fresh=p/'fresh-extracted'
if fresh.exists(): fresh=p/('fresh-extracted-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f'))
fresh.mkdir(exist_ok=False)
with zipfile.ZipFile(p/'325519-Lean-packet.zip') as z:z.extractall(fresh)
cpus=sorted(os.sched_getaffinity(0))[:2]
records=[]
for name in ['Spectral','Semantics','Endpoint']:
 start=time.monotonic();t=datetime.datetime.now(datetime.timezone.utc).isoformat()
 def limit():os.sched_setaffinity(0,cpus)
 r=subprocess.run(['bash','run.sh','-o',name+'.olean',name+'.lean'],cwd=fresh,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=600,preexec_fn=limit)
 (fresh/(name+'.log')).write_bytes(r.stdout)
 records.append(dict(module=name,status=r.returncode,utc=t,elapsed_seconds=time.monotonic()-start,log_sha256=hashlib.sha256(r.stdout).hexdigest()))
 print(name,r.returncode,flush=True)
 if r.returncode:break
bad=[]
for n in names[:3]:
 s=(fresh/n).read_text()
 for word in ['sorry','admit','axiom','unsafe','native_decide','ofReduceBool']:
  if re.search(r'\b'+word+r'\b',s.replace('#print axioms','')):bad.append((n,word))
r=dict(records=records,all_pass=len(records)==3 and all(x['status']==0 for x in records),forbidden_tokens=bad,cpus=cpus,packet_sha256=hashlib.sha256((p/'325519-Lean-packet.zip').read_bytes()).hexdigest(),lean_version=subprocess.check_output(['/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean','--version']).decode(),mathlib='d13f23b723b8a846827a245b89c10fc7d3f11612',limits='fresh extracted sources; shared prebuilt pinned dependency cache read only; no independent acceptance review')
(p/'replay-receipt.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
