from pathlib import Path
import json,hashlib,zipfile,signal,resource,shutil
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
L=Path(__file__).resolve().parent
(L/'measurements.json').write_text(json.dumps([json.loads(s) for s in (L/'runs.jsonl').read_text().splitlines()],indent=2)+'\n')
(L/'provenance.json').write_text(json.dumps(dict(credit=0,additional=5,total=35,input_archive_sha256='6690b358a8a71bbde4d59face1ca1a4ea6b3a598670b2f256ed72b9a0eabcb5b',input_verified=True,frozen_sources='mathematical sources byte-identical; audit extended',candidate_olean_reuse='development only; fresh replay rebuilds all consumed candidate sources',outside_lane_incident='one error-only launcher log initially created in workspace parent, immediately moved to assigned lane; no source change outside lane',remaining_geometric_cases=33,completed_geometric_cases=37,source_endpoint=False,scope='packed soundness and largest full-mask literal-row slice'),indent=2)+'\n')
bench=L/'benchmark-sources';bench.mkdir(exist_ok=True)
for p in (L/'dev').glob('*.lean'):
 if p.stem.startswith(('Packed256','Packed1024','Packed8191','Bits')):shutil.copy2(p,bench/p.name)
files=[]
for d in ['formal','inputs','frozen','benchmark-sources']:files.extend(p for p in (L/d).rglob('*') if p.is_file())
files.extend(p for p in L.iterdir() if p.is_file() and p.suffix in ['.py','.md','.json','.jsonl','.log'] and p.name not in ['source-manifest.json','REPLAY-RECEIPT.json'])
files=sorted(set(files));assert not any(p.suffix in ['.olean','.ilean'] for p in files)
manifest={str(p.relative_to(L)):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in files};(L/'source-manifest.json').write_text(json.dumps(manifest,sort_keys=True,indent=2)+'\n')
with zipfile.ZipFile(L/'source-only-component.zip','w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for p in files+[L/'source-manifest.json']:
  i=zipfile.ZipInfo(str(p.relative_to(L)),date_time=(1980,1,1,0,0,0));i.compress_type=zipfile.ZIP_DEFLATED;i.external_attr=0o100644<<16;z.writestr(i,p.read_bytes())
print(hashlib.sha256((L/'source-only-component.zip').read_bytes()).hexdigest())
