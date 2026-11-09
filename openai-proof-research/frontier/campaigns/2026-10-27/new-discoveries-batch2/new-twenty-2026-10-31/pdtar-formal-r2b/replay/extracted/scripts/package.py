"""Create a source-only, hash-pinned replay archive in this lane."""
import hashlib,json,pathlib,zipfile
D=pathlib.Path(__file__).resolve().parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
mods=['Defs','Basic','FortDuality','KstFamily','Core','Remaining','ReductionTransport','ReductionFlip','ReductionCube','ReductionBasis','ReductionMetric','ReductionPaths','ReductionProof']
files=[D/'PDTAR'/f'{n}.lean' for n in mods]+sorted((D/'scripts').glob('*'))
files=[p for p in files if p.is_file() and p.suffix in ['.py','.lean']]
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib')
m={'modules':mods,'files':{str(p.relative_to(D)):sha(p) for p in files},'pins':{str(p):sha(p) for p in [L/'lean',L/'leanchecker',P/'Mathlib/Combinatorics/SimpleGraph/Basic.lean']},'mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612'}
(D/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
with zipfile.ZipFile(D/'pdtar-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in files+[D/'manifest.json']:
  info=zipfile.ZipInfo(str(p.relative_to(D)),(2026,11,3,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED
  z.writestr(info,p.read_bytes())
print(sha(D/'pdtar-source.zip'))
