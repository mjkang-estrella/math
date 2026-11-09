"""Clean source extraction and kernel replay. Writes only below this lane."""
from pathlib import Path
import subprocess,hashlib,json,zipfile,shutil,sys
root=Path(__file__).resolve().parent
lean=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
pin='5045d0056413266e57c625dcd7c365b10e377c52'
version=subprocess.check_output([str(lean),'--version'],text=True)
assert '4.34.1' in version and pin in version
src=root/'formal/Counterexample.lean'
text=src.read_text()
import re
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',text)
packet=root/'counterexample-source.zip'
with zipfile.ZipFile(packet,'w',zipfile.ZIP_DEFLATED) as z:
 for f in [src,root/'formal/lean-toolchain',root/'formal/lakefile.toml',root/'formal/lake-manifest.json']:
  z.write(f,'formal/'+f.name)
clean=root/'verification/extracted'
if clean.exists():shutil.rmtree(clean)
clean.mkdir(parents=True)
with zipfile.ZipFile(packet) as z:z.extractall(clean)
extracted=clean/'formal/Counterexample.lean'
assert extracted.read_bytes()==src.read_bytes()
names=['zero','star','adjoint','add','nextWins','nextWins_rule','secondWins_rule','Arrow','nimTwo','beta','first_arrow','second_arrow','missing_arrow','not_transitive']
audit=extracted.read_text()+'\n'+''.join('#print axioms Misere.'+n+'\n' for n in names)
(clean/'Audit.lean').write_text(audit)
r=subprocess.run([str(lean),'-DwarningAsError=true','-o',str(clean/'Audit.olean'),str(clean/'Audit.lean')],capture_output=True,text=True,cwd=clean)
log=r.stdout+r.stderr
(root/'verification/Replay.log').write_text(version+log)
allowed={'propext','Classical.choice','Quot.sound'}
for line in log.splitlines():
 if 'depends on axioms:' in line:
  axioms=line.split('[',1)[1].split(']',1)[0]
  assert set(x.strip() for x in axioms.split(',') if x.strip())<=allowed,line
assert r.returncode==0,log
assert all(('Misere.'+n+"'") in log for n in names),log
out=dict(status='PASS',lean_version=version.strip(),lean_binary_sha256=hashlib.sha256(lean.read_bytes()).hexdigest(),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),packet_sha256=hashlib.sha256(packet.read_bytes()).hexdigest(),clean_extracted_rebuild=True,audited_declarations=names,axioms_allowed=sorted(allowed),mathlib_dependency=None,discovery_count_credit=0)
(root/'verification/result.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
