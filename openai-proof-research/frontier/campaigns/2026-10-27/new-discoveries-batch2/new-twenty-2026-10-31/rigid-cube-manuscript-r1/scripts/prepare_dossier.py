from pathlib import Path
import shutil,json,hashlib
D=Path(__file__).resolve().parents[1];b=D.parent
for sub in ['formal','sources','raw','review-context']: (D/sub).mkdir(exist_ok=True)
for n in ['Cube','Signed','Audit','Inventory','Safety']:shutil.copyfile(b/f'expanded-corpus-r59/formal/{n}.lean',D/f'formal/{n}.lean')
for p in (D/'supplements').glob('*.lean'):shutil.copyfile(p,D/'formal'/p.name)
for src,out in [('expanded-corpus-r59/PROOF.md','PROOF.md'),('expanded-corpus-r59/certificate.json','author-certificate.json'),('expanded-corpus-r59/raw/364205.jsonl','raw/364205.jsonl'),('expanded-corpus-r59-parent-integration.json','review-context/parent-integration.json'),('rigid-cube-source-review-r2/REVIEW.md','review-context/source-review.md'),('rigid-cube-source-review-r2/review.json','review-context/source-review.json')]:shutil.copyfile(b/src,D/out)
for n in ['rigid','rigid-v2']:
 for ext in ['body','receipt.json']:shutil.copyfile(b/f'expanded-corpus-r59/sources/{n}.{ext}',D/f'sources/{n}.{ext}')
for n in ['bezrukov-full','helly']:
 for ext in ['body','receipt.json']:shutil.copyfile(b/f'rigid-cube-source-review-r2/sources/{n}.{ext}',D/f'sources/{n}.{ext}')
for n in ['anticode-count','linear-anticode','rigid','rigid-v2']:
 shutil.copyfile(b/f'rigid-cube-source-review-r2/sources/{n}-clean.txt',D/f'sources/{n}-clean.txt')
for src in ['rigid-new1','rigid-new2']:
 for ext in ['body','receipt.json']:shutil.copyfile(b/f'expanded-corpus-r59/sources/{src}.{ext}',D/f'sources/{src}.{ext}')
# The r1 review contains the two anticode primary bodies.
for p in (b/'rigid-cube-source-review-r1').rglob('*'):
 if p.is_file() and ('anticode' in p.name) and p.suffix in ['.body','.json']:
  shutil.copyfile(p,D/'sources'/('r1-'+p.name))
pins={'Lean':'4.34.1','lean_commit':'5045d0056413266e57c625dcd7c365b10e377c52','mathlib_commit':'d13f23b723b8a846827a245b89c10fc7d3f11612','default_LEAN_BIN':'/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin','default_LEAN_PACKAGES':'/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages','trust':'External prebuilt dependency oleans; upstream not rebuilt.'}
(D/'pins.json').write_text(json.dumps(pins,indent=2)+'\n')
(D/'raw/sha256.json').write_text(json.dumps({'364205.jsonl':hashlib.sha256((D/'raw/364205.jsonl').read_bytes()).hexdigest()},indent=2)+'\n')
