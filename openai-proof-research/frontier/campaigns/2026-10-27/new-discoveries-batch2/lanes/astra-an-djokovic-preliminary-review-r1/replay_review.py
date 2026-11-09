"""Reproduce the helper-only audit; all writes stay in this review lane."""
from pathlib import Path
import os,subprocess,json,hashlib,re,datetime
lane=Path(__file__).resolve().parent
source=lane.parent/'root-an-djokovic-r1/formal/TwoLevel.lean'
data=source.read_bytes()
assert hashlib.sha256(data).hexdigest()=='58362b5bcd1035e74feb4f23422bff919a90195cdfb444c48c62abb8e2587eb5'
(lane/'TwoLevel-review.lean').write_bytes(data)
names=re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)',data.decode(),re.M)
audit=lane/'Audit.lean'
audit.write_text(data.decode()+'\n'+'\n'.join(f'#check AnDjokovic.{n}\n#print axioms AnDjokovic.{n}' for n in names)+'\n')
base=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal')
binary='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'
env=os.environ.copy()
env['LEAN_PATH']=':'.join(map(str,[base/'.lake/build/lib/lean',*sorted((base/'.lake/packages').glob('*/.lake/build/lib/lean'))]))
result=subprocess.run([binary,str(audit)],cwd=lane,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
(lane/'lean-review.log').write_text(result.stdout)
axioms=[x for x in result.stdout.splitlines() if 'axioms' in x]
bad=[]
for line in axioms:
    if 'depends on axioms: [' in line:
        bad.extend(x.strip() for x in line.split('depends on axioms: [')[1].rstrip(']').split(',')
                   if x.strip() not in {'propext','Classical.choice','Quot.sound'})
report={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'binary':binary,'mathlib_pin_claim':'d13f23b723b8a846827a245b89c10fc7d3f11612',
 'candidate_sha256':hashlib.sha256(data).hexdigest(),
 'audit_sha256':hashlib.sha256(audit.read_bytes()).hexdigest(),
 'returncode':result.returncode,'names':names,'axiom_lines':axioms,
 'unexpected_axioms':bad,'scope':'Only 7 definitions and 9 helper theorems. Literal endpoint absent.'}
(lane/'lean-review.json').write_text(json.dumps(report,indent=2)+'\n')
assert result.returncode==0 and not bad and not any(x in result.stdout for x in ['sorryAx','error:'])
print('Helper audit PASS; NO full literal endpoint.')
