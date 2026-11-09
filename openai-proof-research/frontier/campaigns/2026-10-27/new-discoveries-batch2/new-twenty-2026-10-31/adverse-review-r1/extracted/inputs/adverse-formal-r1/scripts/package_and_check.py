from pathlib import Path
import hashlib,json,zipfile,subprocess,os,sys,runpy,copy,datetime
p=Path(__file__).resolve().parents[1]
# Exact-certificate controls do not write to the hash-bound inputs.
checker=runpy.run_path(str(p/'scripts/check_certificate.py'))['check']
r=json.loads((p/'inputs/outputs/latin36-certificate.json').read_text());controls=[]
for name,key,replacement in [('zero eigenvector','eigenvector',['0']*36),('zero fractional transversal','fractional_transversal',['0']*36),('wrong vector dimension','eigenvector',['1'])]:
 bad=copy.deepcopy(r);bad[key]=replacement
 try:checker(bad)
 except (AssertionError,IndexError):controls.append({'name':name,'rejected':True})
 else:raise AssertionError(name+' was not rejected')
(p/'logs/certificate-negative-controls.json').write_text(json.dumps(controls,indent=2)+'\n')
# Deliberately omit binary source bodies and output artifacts.
selected=[p/x for x in ['TASK.txt','SUMMARY.md','PRIOR-ART.md','PRIOR-ART.json','GAPS.md','results.json','REPRODUCE.md','STATEMENT-CORRESPONDENCE.md','replay.py','formal/README.md','scripts/check_certificate.py','inputs/outputs/latin36-certificate.json','inputs/outputs/LATIN36-ORDINARY-PROOF.md','logs/exact-certificate-check.json','logs/certificate-negative-controls.json','logs/audit.json','receipts/input-hashes.json','receipts/input-hashes-after.json']]
manifest={str(f.relative_to(p)):hashlib.sha256(f.read_bytes()).hexdigest() for f in selected}
(p/'PACKET-SOURCES.json').write_text(json.dumps(manifest,indent=2)+'\n');selected.append(p/'PACKET-SOURCES.json')
z=p/'adverse-381433-incomplete-source.zip'
with zipfile.ZipFile(z,'w',zipfile.ZIP_DEFLATED) as a:
 for f in selected:a.write(f,str(f.relative_to(p)))
receipt={'sha256':hashlib.sha256(z.read_bytes()).hexdigest(),'bytes':z.stat().st_size,'files':len(selected),'source_only':True,'lean_sources':0,'status':'INCOMPLETE_RESEARCH_PACKET'}
(p/'receipts/packet.json').write_text(json.dumps(receipt,indent=2)+'\n')
fresh=p/'fresh-replay'
fresh.mkdir() # Must be new and empty.
with zipfile.ZipFile(z) as a:
 assert not any(n.endswith('.olean') or n.startswith('/') or '..' in Path(n).parts for n in a.namelist());a.extractall(fresh)
env={'PATH':'/usr/bin:/bin','LANG':'C.UTF-8','MALLOC_ARENA_MAX':'2','TMPDIR':str(p/'tmp'),'LEAN_BIN':'/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean','LEAN_PACKAGES':'/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'}
def run():return subprocess.run(['/usr/bin/python3','-I','replay.py'],cwd=fresh,env=env,capture_output=True,text=True,timeout=10)
a=run();assert a.returncode==3
(p/'logs/fresh-replay.log').write_text(a.stdout+a.stderr)
fr={'packet_sha256':receipt['sha256'],'fresh_directory':str(fresh),'sanitized_environment_keys':sorted(env),'command':['python3','-I','replay.py'],'exit_code':a.returncode,'status':'HOLD_EXPECTED','strict_lean_build':'NOT_RUN','leanchecker':'NOT_RUN'}
(p/'receipts/fresh-replay.json').write_text(json.dumps(fr,indent=2)+'\n')
(fresh/'formal/control.olean').write_bytes(b'negative control, not an actual olean')
b=run();assert b.returncode==2 and 'existing oleans' in b.stdout
(fresh/'formal/control.olean').unlink()
c=fresh/'inputs/outputs/latin36-certificate.json';orig=c.read_bytes();c.write_bytes(orig+b' ')
d=run();assert d.returncode==2 and 'source hash mismatch' in d.stdout
c.write_bytes(orig)
neg={'scope':'driver and ordinary certificate controls only; NO formal controls','controls':controls+[{'name':'reject existing olean','rejected':True,'exit_code':b.returncode,'output':b.stdout},{'name':'reject source mutation','rejected':True,'exit_code':d.returncode,'output':d.stdout}]}
(p/'logs/negative-controls.json').write_text(json.dumps(neg,indent=2)+'\n')
print(json.dumps({'packet':receipt,'fresh_replay':fr,'negative_control_count':len(neg['controls'])},indent=2))
