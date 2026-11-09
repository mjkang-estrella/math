import pathlib,subprocess,os,resource,time,json,hashlib,re,zipfile
L=pathlib.Path(__file__).resolve().parent;F=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal');binary='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
H=lambda b:hashlib.sha256(b).hexdigest();src=(L/'Latin.lean').read_bytes()
assert not re.search(rb'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\s',src.split(b'open Lean in')[0])
# The packet contains only reviewed source, no precompiled local oleans.
with zipfile.ZipFile(L/'lean-packet.zip','w',zipfile.ZIP_DEFLATED) as z:z.writestr('Latin.lean',src)
E=L/'extracted';E.mkdir(exist_ok=True)
with zipfile.ZipFile(L/'lean-packet.zip') as z:z.extractall(E)
assert (E/'Latin.lean').read_bytes()==src
assert not list(E.glob('*.olean'))
env=os.environ.copy();env['LEAN_PATH']=':'.join(str(p/'.lake/build/lib/lean')for p in (F/'.lake/packages').iterdir());env['LEAN_PATH']+=':'+str(F/'.lake/build/lib/lean')
def limits():
 os.sched_setaffinity(0,{0,1});resource.setrlimit(resource.RLIMIT_AS,(8*1024**3,8*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(100,100))
start=time.time()
with open(L/'strict-extracted.log','w') as log:
 r=subprocess.run([binary,'-j1','-DwarningAsError=true','Latin.lean'],cwd=E,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=110,preexec_fn=limits)
log=(L/'strict-extracted.log').read_text();assert r.returncode==0,log
assert 'sorryAx' not in log
assert 'AUDIT_TOTAL' in log
receipt={'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'exit_code':r.returncode,'elapsed_s':time.time()-start,'lean_version':subprocess.check_output([binary,'--version'],text=True).strip(),'source_sha256':H(src),'packet_sha256':H((L/'lean-packet.zip').read_bytes()),'strict_log_sha256':H(log.encode()),'local_declaration_audit_total':int(re.search(r'AUDIT_TOTAL (\d+)',log)[1]),'resource_limits':{'CPUs':[0,1],'CPU_s':100,'wall_s':110,'address_space_bytes':8*1024**3},'dependencies_read_only':True,'mathlib_revision_from_lakefile':'d13f23b723b8a846827a245b89c10fc7d3f11612','lake_manifest_sha256':H((F/'lake-manifest.json').read_bytes()),'trust_limit':'Prebuilt imported oleans trusted. No complete upstream rebuild/source-to-olean attestation. All local declarations including generated are audited in current module.'}
(L/'strict-extracted-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2))
