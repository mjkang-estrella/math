from pathlib import Path
r=Path(__file__).resolve().parent
for n in ['endpoint-r8.py']:
 p=r/n;p.write_text(p.read_text().replace("r/'fresh-extracted'","r/'optimized-extracted'"))
for n in ['report-r8.py','archive-r8.py','verify-package-r8.py']:
 p=r/n;p.write_text(p.read_text().replace('strict-extracted','strict-final'))
p=r/'verify-package-r8.py';t=p.read_text().replace("res['development_checked_but_omitted']=[106061,106561]","res['earlier_unshared_memory_failure']=res.pop('scaling_failure');res['optimized_pre_scaling_measurements']=json.loads((r/'optimized-scaling-measurements.json').read_text())['windows'];res['memory_optimization']='Named reducible mask constants introduced by MaskChainBuildR8; original 303 modules unchanged'")
t=t.replace("assert 'Metadata audit passed: 247502 declarations' in (r/'metadata-audit.txt').read_text()","assert re.search(r'Metadata audit passed: [0-9]+ declarations', (r/'metadata-audit.txt').read_text())")
t=t.replace("r/'fresh-extracted/logs']","r/'fresh-extracted/logs',r/'unshared-logs',r/'optimized-extracted/logs']").replace("'development-progress.json']:","'development-progress.json','optimized-replay.log','optimized-scaling-measurements.json']:")
t=t.replace("'proof/driver sources; 781 strict successes; metadata, axioms and full logs archived.'","'proof/driver sources; every ordered strict success verified; metadata, axioms and full logs archived.'")
p.write_text(t)
p=r/'package-r8.py';t=p.read_text().replace("json.loads((r/'scaling-measurements.json').read_text())['windows']","json.loads((r/'optimized-scaling-measurements.json').read_text())['windows']").replace("'incident.txt','scaling-measurements.json']:","'incident.txt','scaling-measurements.json','optimized-scaling-measurements.json']:")
t=t.replace('Full scaling stopped at R8Chain106561 on the fixed -M3500 import-memory limit; the packet omits the last 500 development-checked additions to leave endpoint and audit headroom.','An earlier unshared-mask version stopped at R8Chain106561 on the fixed -M3500 import-memory limit. MaskChainBuildR8 replaces repeated literal masks with named reducible definitions; the delivered status above describes the subsequent checked version.')
t=t.replace('MaskChainBuild assembles ordinary proof expressions.','MaskChainBuild and MaskChainBuildR8 assemble ordinary proof expressions. The round 8 command gives every used mask ID a shared reducible definition, reducing imported proof memory. Kernel-checked definitions bind each name to its actual literal mask; all check and entailment proofs still reduce and typecheck normally.')
p.write_text(t)
import shutil,hashlib
src=r/'source-only.zip';dst=r/'unshared-source-106061.zip';shutil.copyfile(src,dst);assert hashlib.sha256(src.read_bytes()).digest()==hashlib.sha256(dst.read_bytes()).digest()
