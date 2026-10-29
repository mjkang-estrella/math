import resource,signal
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
import json,collections,re
from pathlib import Path
r=json.loads(Path('own-replay/replay-receipt.json').read_text());out=[]
for d in r['declarations']:
 t=d['actual_type'];assert t and not any(d[k] for k in ['unsafe','partial','axiom']);assert set(d['axioms'])<={'propext','Classical.choice','Quot.sound'}
 # Full types retained in receipt. Check disallowed assumptions/placeholder constants in every type.
 assert not re.search(r'sorryAx|False\.elim|ofReduceBool|native_decide|SteinerReflection\.Assumption',t)
 out.append({'name':d['name'],'origin':d['origin'],'actual_type_sha256':__import__('hashlib').sha256(t.encode()).hexdigest(),'type_chars':len(t),'flags_checked':True,'axioms_checked':d['axioms']})
 print(d['origin'],d['name'],'TYPE',t[:380].replace('\n',' '),'AX',d['axioms'])
Path('actual-report-inspection.json').write_text(json.dumps(out,indent=2))
print('PINS',json.dumps(r['pins'],indent=2));print('STAGES',[(s['peak_group_rss_kib'],s['seconds'],s['exit']) for s in r['steps']])
