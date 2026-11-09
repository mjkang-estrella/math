import resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
resource.setrlimit(resource.RLIMIT_CPU,(50,50))
import pathlib,json,hashlib,datetime
out=pathlib.Path(__file__).resolve().parent;b=out.parent.parent; inv=b/'lanes/pi-mathdb-full-corpus-inventory-r301';r=json.loads((out/'reservation.json').read_text());H=lambda x:hashlib.sha256(x).hexdigest()
checks={p:{'expected':h,'actual':H(pathlib.Path(p).read_bytes())} for p,h in r['input_hashes'].items()};(out/'input-verification.json').write_text(json.dumps(checks,indent=2))
m=json.loads((inv/'manifest.json').read_text());found={}
for f in m['files']:
 if not f['path'].startswith('corpus/'):continue
 p=inv/f['path'];raw=p.read_bytes();assert H(raw)==f['sha256']
 for n,line in enumerate(raw.splitlines(keepends=True),1):
  d=json.loads(line);i=d.get('id',d.get('mathdb_id'))
  if i in r['ids']:
   (out/'raw'/f'{i}.jsonl').write_bytes(line);found[str(i)]={'chunk':str(p.resolve()),'one_based_line':n,'chunk_sha256':H(raw),'raw_sha256':H(line),'record':d}
assert len(found)==40
(out/'extracted.json').write_text(json.dumps(found,indent=2,ensure_ascii=False))
for i,x in found.items():print(i,json.dumps(x['record'],ensure_ascii=False))
