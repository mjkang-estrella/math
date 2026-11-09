import resource,signal,json,hashlib,datetime
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
D=Path('.').resolve();root=D.parent/'root-polyomino57-final-review-freeze-r1';f=json.loads((D/'FREEZE.json').read_text());r={}
for n,v in f['files'].items():
 hs=[hashlib.sha256((p/n).read_bytes()).hexdigest() for p in [D,root]];assert hs==[v['sha256']]*2;r[n]=hs[0]
sm=json.loads((D/'extracted/source-manifest.json').read_text());assert sm==json.loads((root/'extracted/source-manifest.json').read_text());assert len(sm)==2023
for n,v in sm.items():
 hs=[hashlib.sha256((p/'extracted'/n).read_bytes()).hexdigest() for p in [D,root]];assert hs==[v['sha256']]*2
assert hashlib.sha256((D/'extracted/paper.pdf').read_bytes()).hexdigest()=='c47060d9e31973318059d3d0a3cd868b1643c67073ca32e6e7317d7666f144e3'
Path('after.json').write_text(json.dumps(dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),frozen_files=r,formal_source_count=2023,root_input_sources_identical=True,root_live_output_read=False),indent=2))
