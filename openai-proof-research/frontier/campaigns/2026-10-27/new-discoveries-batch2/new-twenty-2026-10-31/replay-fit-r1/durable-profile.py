from pathlib import Path
import re
L=Path(__file__).resolve().parent
for cid,mod in [('330264','SpectralWitness'),('324342','ConferenceMDS324342')]:
 s=(L/f'original-{cid}'/f'{mod}.lean').read_text()
 marker=str(L/'logs'/f'{cid}-declarations.log')
 def repl(m):
  return '#eval do\n  let f ← IO.FS.Handle.mk "'+marker+'" IO.FS.Mode.append\n  f.putStrLn s!"ENTER '+m[2]+' {← IO.monoMsNow}"\n  f.flush\n'
 s=re.sub(r'(?m)^(?=((?:noncomputable )?def|theorem|lemma) (\w+))',repl,s)
 (L/f'profile-{cid}'/f'{mod}.lean').write_text(s)
