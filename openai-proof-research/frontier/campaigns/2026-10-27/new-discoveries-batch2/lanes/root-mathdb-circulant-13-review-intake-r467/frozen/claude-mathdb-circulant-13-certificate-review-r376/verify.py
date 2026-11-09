# r376 lane verifier. Modes: build (write manifest.json), verify [--replay] (check; write verification-receipt.json).
# Exits nonzero on any mismatch. Run: python3 -B -I verify.py verify --replay
import hashlib,json,sys,datetime,subprocess,tempfile,os
from pathlib import Path
L=Path(__file__).resolve().parent
EXCL={'manifest.json','verification-receipt.json'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def files():return sorted(str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in EXCL and '__pycache__' not in p.parts)
fail=[]
def chk(p,h,s,tag):
    p=Path(p)
    if not p.is_file(): fail.append(f'{tag}: missing {p}'); return
    if p.stat().st_size!=s or sha(p)!=h: fail.append(f'{tag}: mismatch {p}')
mode=sys.argv[1] if len(sys.argv)>1 else 'verify'
if mode=='build':
    (L/'manifest.json').write_text(json.dumps({'files':[{'path':f,'sha256':sha(L/f),'size':(L/f).stat().st_size} for f in files()]},indent=1)+'\n')
    print('BUILT',len(files())); sys.exit(0)
if mode!='verify': sys.exit('usage: build | verify [--replay]')
# 1. actual originals / intake payloads
ib=json.loads((L/'input-bindings.json').read_text())
if ib.get('status')!='PASS' or ib.get('failures'): fail.append('input-bindings recorded failure')
for e in ib['refs']: chk(e['path'],e['sha256'],e['size'],'intake')
for e in ib['r360_original_refs']: chk(e['path'],e['sha256'],e['size'],'r360-original')
I=Path(ib['intake_dir'])
if sha(I/'manifest.json')!=ib['intake_manifest_sha256']: fail.append('intake manifest.json changed')
C=I/'frozen/claude-mathdb-primary-qualified-breadth-r360'
if sha(C/'manifest.json')!=ib['r360_manifest_sha256']: fail.append('r360 manifest.json changed')
if len(ib['refs'])!=82 or len(ib['r360_original_refs'])!=72: fail.append('ref counts')
# 2. own lane manifest: exact set + hashes
man=json.loads((L/'manifest.json').read_text())['files']
if [e['path'] for e in man]!=files(): fail.append(f'lane file set differs: {sorted(set(files())^{e["path"] for e in man})}')
for e in man: chk(L/e['path'],e['sha256'],e['size'],'lane')
# 3. fixed scientific facts in stored outputs
r=json.loads((L/'runs/indep_check.json').read_text()); x=json.loads((L/'runs/extra_checks.json').read_text())
try:
    assert r['K11']=={'edges':4,'nontrivial_scc_sizes':[],'periods':[],'states':6}
    assert r['K12']['states']==152 and r['K12']['edges']==128 and r['K12']['periods']==[12,12] and r['K12']['scc_simple_cycle']==[True,True]
    assert sorted(map(int,r['witness_words']))==[12]+list(range(142,165,2))
    assert x['K12_r360_state_set_equal'] and x['K11_r360_state_set_equal'] and x['negative_tests_rejected']==40
except (AssertionError,KeyError) as ex: fail.append(f'stored facts: {ex!r}')
# 4. optional replay under the fixed guard (outputs to a temp dir outside the lane, then compared)
replay=None
if '--replay' in sys.argv:
    G=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
    if sha(G)!='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45': fail.append('guard hash')
    env=dict(os.environ,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1')
    with tempfile.TemporaryDirectory() as t:
        a=subprocess.run(['python3','-B',str(G),'python3','-B','-I',str(L/'tools/indep_check.py'),t+'/i.json'],env=env,capture_output=True,text=True)
        b=subprocess.run(['python3','-B',str(G),'python3','-B','-I',str(L/'tools/extra_checks.py'),t+'/e.json',str(C/'certificates'),t+'/i.json',str(L/'work/c372627-pdf-layout.txt')],env=env,capture_output=True,text=True)
        ok=a.returncode==0 and b.returncode==0 and json.loads(Path(t+'/i.json').read_text())==r and json.loads(Path(t+'/e.json').read_text())==x
        replay={'indep_exit':a.returncode,'extra_exit':b.returncode,'outputs_identical':ok}
        if not ok: fail.append(f'replay {replay} {a.stderr[-300:]} {b.stderr[-300:]}')
st='PASS' if not fail else 'FAIL'
(L/'verification-receipt.json').write_text(json.dumps({'status':st,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lane_files':len(man),'intake_refs':len(ib['refs']),'r360_original_refs':len(ib['r360_original_refs']),'replay':replay,'failures':fail,'accepted_credit':0},indent=1)+'\n')
print(st,len(man),'lane files',len(ib['refs']),'intake refs',len(ib['r360_original_refs']),'r360 originals','replay',replay)
for f in fail: print('FAIL',f)
sys.exit(1 if fail else 0)
