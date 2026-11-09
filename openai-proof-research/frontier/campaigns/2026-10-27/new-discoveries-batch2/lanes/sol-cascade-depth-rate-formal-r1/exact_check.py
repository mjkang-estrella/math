import os,resource,pathlib,json,hashlib
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(25,)*2)
for n in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[n]='1'
b=pathlib.Path(__file__).resolve().parent
before=json.loads((b/'frozen-before.json').read_text())
assert all(hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()==h for p,h in before.items())
assert (b/'formal/DepthDefs.lean').read_bytes()==(b.parent/'root-cascade-formal-r1/formal/DepthDefs.lean').read_bytes()
assert (b/'formal/run_lean.py').read_bytes()==(b.parent/'root-cascade-formal-r1/formal/run_lean.py').read_bytes()
prev=0
for k in range(1,201):
 n=k*k*(prev+k+10)
 assert n>prev and n>=k*k*(k+10) and prev*k*k<=n
 if k>=3:
  a=2*k+2;h=prev+3;rem=n-a-h;B,t=divmod(rem,k);F=(k-2)*B;D=n-1-F
  assert rem>=0 and t<k and n==a+B*k+t+h and F<=n-1 and D+F==n-1
  assert D*k*k<=(2*k+1)*n+(3*k+5)*k*k and D*k<=4*n
 prev=n
lean=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
assert hashlib.sha256(lean.read_bytes()).hexdigest()=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
(b/'exact-check.json').write_text(json.dumps({'pass':True,'instances':200,'formal_evidence':False,'AS_MiB':512,'CPU_seconds':25,'BLAS_threads':1,'frozen_after':before},indent=2))
print('exact bookkeeping PASS; no finite evidence used in proofs')
