from pathlib import Path
import re,json,hashlib
L=Path(__file__).resolve().parent
manifest=json.loads((L.parent/'coxeter-normal-form-r3/packet-manifest.json').read_text())['files']
verified={}
for p in (L/'original-330264').rglob('*'):
 if p.is_file():
  name=str(p.relative_to(L/'original-330264'))
  if name in manifest:
   digest=hashlib.sha256(p.read_bytes()).hexdigest()
   assert digest==manifest[name],name
   verified[name]=digest
(L/'330264-manifest-verification.json').write_text(json.dumps(verified,indent=2)+'\n')
for cid,mod in [('330264','SpectralWitness'),('324342','ConferenceMDS324342')]:
 s=(L/f'original-{cid}'/f'{mod}.lean').read_text()
 # Instrumentation only: report entry before each top-level declaration.
 # No declaration text is changed; these are diagnostic copies, not proposed packets.
 s=re.sub(r'(?m)^(?=((?:noncomputable )?def|theorem|lemma) (\w+))',lambda m:'#eval IO.println "ENTER '+m[2]+'"\n',s)
 d=L/f'profile-{cid}';d.mkdir(exist_ok=True)
 (d/f'{mod}.lean').write_text(s)
