import os,resource,signal,json,hashlib,re,shutil,zipfile
from pathlib import Path
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,35));signal.alarm(40)
L=Path(__file__).resolve().parent
mods=['Grid','Growth','Normalization','Bounds','Witness','Pilot','Efficient','Coverage','Existence','ListCertificate','Assembly','NumericPilot','SmallClosure','PlacementTree']
terms=json.loads((L/'terminal-modules.json').read_text())
(L/'modules.json').write_text(json.dumps(mods+terms))
p=L/'formal/OriginAudit.lean';s=p.read_text();s=s.replace('import Lean','import ListCertificate\nimport Assembly\nimport NumericPilot\nimport SmallClosure\nimport PlacementTree\nimport Lean').replace('`Existence]','`Existence, `ListCertificate, `Assembly, `NumericPilot, `SmallClosure, `PlacementTree]');p.write_text(s)
for m in terms:
 # Keep each auditor small; importing all literal data together is unnecessary.
 a=s[s.index('import Lean'):]
 a=a.replace('let mods := #[`Grid, `Growth, `Normalization, `Bounds, `Witness, `Pilot, `Efficient, `Coverage, `Existence, `ListCertificate, `Assembly, `NumericPilot, `SmallClosure, `PlacementTree]', 'let mods := #[`'+m+']')
 (L/'formal'/('Audit'+m+'.lean')).write_text('import '+m+'\n'+a)
# Static checks and all immutable input checks.
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for path,h in json.loads((L/'input-hashes.json').read_text()).items():
 original=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')/path
 assert sha(original)==h,path
pins=json.loads((L/'pins.json').read_text());assert sha(Path(pins['lean_binary']))==pins['lean_sha256']
for m in mods+terms:
 assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',(L/'formal'/(m+'.lean')).read_text()),m
files=['pins.json','run.py','modules.json','terminal-modules.json']+['formal/'+p.name for p in sorted((L/'formal').glob('*.lean'))]
manifest={p:sha(L/p) for p in files};(L/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');files.append('source-manifest.json')
archive=L/'source-only-certificate.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for f in files:
  info=zipfile.ZipInfo(f,(2026,10,29,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;z.writestr(info,(L/f).read_bytes())
x=L/'extracted';x.mkdir(exist_ok=False)
with zipfile.ZipFile(archive) as z:z.extractall(x)
for p,h in manifest.items():assert sha(x/p)==h
(L/'archive-receipt.json').write_text(json.dumps({'sha256':sha(archive),'bytes':archive.stat().st_size,'source_only':True,'modules':len(mods+terms),'extracted_sources_identical':True},indent=2))
