from pathlib import Path
import hashlib,json,shutil
b=Path('..').resolve();o=Path('.').resolve();r=b/'nut-formal-r7q';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
selected=set()
def walk(v):
 if isinstance(v,dict):
  for x in v.values():walk(x)
 elif isinstance(v,list):
  for x in v:walk(x)
 elif isinstance(v,str):
  if v.endswith('.json') and (r/v).is_file():selected.add(r/v)
for n in ['development-validation.json','source-fixes.json','negative-controls-receipts.json']:
 walk(json.loads((r/n).read_text()))
for n in ['replay.py','modules.json','audit-modules.json']:selected.add(r/n)
fontfiles=[Path('/usr/share/fonts/google-carlito-fonts/Carlito-Regular.ttf'),Path('/usr/share/fonts/google-carlito-fonts/Carlito-Bold.ttf'),Path('/usr/share/fonts/adwaita-mono-fonts/AdwaitaMono-Regular.ttf')]
selected.update(fontfiles)
manifest={str(p):sha(p) for p in sorted(selected)}
Path('supplemental-inputs-before.json').write_text(json.dumps(manifest,indent=2)+'\n')
for p in selected:
 if p in fontfiles:dst=o/'fonts'/p.name
 else:dst=o/'evidence'/p.relative_to(b)
 dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dst);assert sha(dst)==manifest[str(p)]
print('Supplemental receipts and rendering inputs:',len(selected))
# source manifest belongs to immutable proof packet, not the paper
shutil.copyfile('safe-extracted/source-manifest.json','SOURCE-MANIFEST.json')
# remove redundant archive copy; root copy is identity checked
(o/'evidence/nut-formal-r7q/nut-r7q-source.zip').unlink()
# Render build now uses same frozen font bytes carried in dossier.
p=Path('build_paper.py');s=p.read_text().replace("'google-carlito-fonts/Carlito-Regular.ttf'","'Carlito-Regular.ttf'").replace("'google-carlito-fonts/Carlito-Bold.ttf'","'Carlito-Bold.ttf'").replace("'adwaita-mono-fonts/AdwaitaMono-Regular.ttf'","'AdwaitaMono-Regular.ttf'").replace("'/usr/share/fonts/'+f","str(Path('fonts')/f)");p.write_text(s)
# Ordinary proof with clear mathematical theorem and no abstract/evidence status interleaving.
sections=Path('paper.md').read_text().split('---PAGE---')
Path('PROOF.md').write_text('# Ordinary proof: no cubic 8-circulant nut graph\n\nDRAFT, AI-assisted; zero accepted credit. All graphs are finite and simple. A nut graph has real adjacency nullity exactly one and a full nonzero kernel vector. An 8-circulant graph admits a cyclic automorphism group with eight equal vertex orbits. See paper.md for bibliography, validation and novelty limits.\n\n**Theorem.** No graph is simultaneously cubic, nut and 8-circulant.\n\n'+'\n\n'.join(sections[1:6]))
