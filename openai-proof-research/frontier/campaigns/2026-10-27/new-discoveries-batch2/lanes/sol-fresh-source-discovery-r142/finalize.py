import json,hashlib,datetime,sys
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def put(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
if len(sys.argv)>1 and sys.argv[1]=='verify':
 b=(L/'finalmanifest.json').read_bytes();j=json.loads(b);bad=[]
 for x in j['files']:
  p=L/x['path']
  if not p.exists() or sha(p.read_bytes())!=x['sha256']:bad.append(x['path'])
 put('manifest-verification.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha(b),files=len(j['files']),bad=bad,pass_all=not bad,exclusions=['finalmanifest.json (self)','manifest-verification.json (verification output)']))
 print('verified',len(j['files']),'files; failures',bad);assert not bad
else:
 http=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]
 put('provenance.json',dict(lane=str(L),utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='UNRESOLVED_ZERO',credit=0,observed_counts=dict(additional=9,total=39,next=40),source_access=http,source_limit='16MB bounded HTTP reads; all successful retained bytes below cap. No403/429/challenge or bypass in these requests.',history=['history-initial.json','history-exact.json','history-laplacian.json'],registry='registry-retained.json',guard=dict(path=str(L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),sha256=sha((L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py').read_bytes()),AS_bytes=512*1024*1024,group_RSS_bytes=512*1024*1024,CPU_seconds=210,wall_seconds=230,nominal_sampling_ms=40,limits='Sampled RSS cannot exclude transients; guard unchanged; no raised caps'),failures=[dict(kind='ModuleNotFoundError',module='bs4',exit=1,resolution='stdlib HTMLParser; no package installation'),dict(kind='screen-order failure',detail='Old boxed-mesh hit present in complete receipt but missed in truncated tool display before redundant download; full original r105 reopened, lead dropped')],public_searches=dict(date='2026-10-29 UTC',queries=['arxiv graph conjecture 2026 saturation number','arxiv conjecture 2026 domination polynomial','Coincidences and Growth of Boxed Mesh Patterns','2610.08636','Chen Guo Laplacian n(n-k) conjecture','Box(2143) conjecture proof','boxed Kitaev Qiu Xu conjecture','Nordhaus-Gaddum 14060 conjecture proof','Laplacian product Chen Guo conjecture 2026','Nordhaus-Gaddum kth conjecture proof 2026','14060 Laplacian proof conjecture','Nordhaus-Gaddum product site:github.com/Truetur/math'],limits='Indexed public web; result bodies not all retained. No exhaustive absence claim.'),not_done=['full ordinary resolution','independent clearance','current target-specific registry proof-body clearance','Lean','manuscript','acceptance']))
 files=[]
 for p in sorted(L.rglob('*')):
  if not p.is_file() or p.name in ['finalmanifest.json','manifest-verification.json']:continue
  b=p.read_bytes();files.append(dict(path=str(p.relative_to(L)),bytes=len(b),sha256=sha(b)))
 put('finalmanifest.json',dict(schema=1,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=files,self_excluded=True,verification_output_excluded=True))
 print('manifest',len(files))
