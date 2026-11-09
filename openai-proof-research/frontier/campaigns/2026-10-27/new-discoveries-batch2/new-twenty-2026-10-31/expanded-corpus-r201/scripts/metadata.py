import pathlib,json,re,hashlib,difflib
D=pathlib.Path(__file__).resolve().parents[1];out={}
for r in json.loads((D/'outputs/source-receipts.json').read_text()):
 aid=r['url'].rsplit('/',1)[-1];s=pathlib.Path(r['body']).read_text();vs=sorted(set(re.findall('/abs/'+re.escape(aid)+r'v(\d+)',s)),key=int) or ['1']
 out[aid]={'versions':vs,'abstract_receipt':r,'version_texts':{},'version_diffs':{}}
 prev=None
 for v in vs:
  p=D/f'outputs/{aid}v{v}.txt'
  if not p.exists():continue
  b=p.read_bytes();out[aid]['version_texts'][v]={'path':str(p),'sha256':hashlib.sha256(b).hexdigest()}
  if prev:
   diff=''.join(difflib.unified_diff(prev[1].splitlines(True),b.decode().splitlines(True),fromfile=prev[0],tofile=v));(D/f'outputs/diff-{aid}-{prev[0]}-{v}.txt').write_text(diff);out[aid]['version_diffs'][v]=len(diff)
  prev=(v,b.decode())
(D/'outputs/version-audit.json').write_text(json.dumps(out,indent=2))
for aid,r in out.items():print(aid,r['versions'],r['version_diffs'])
for p in ['primary-5.txt','2404.01973v3.txt','2601.09551v1.txt','2609.08816v1.txt']:
 print('PRIMARY',p,(D/'outputs'/p).exists())
reg=json.loads((D/'outputs/registry-screen.json').read_text());print('registry receipt statuses',[(r['url'],r.get('status')) for r in reg['receipts'] if 'primary-' in r.get('body','')])
