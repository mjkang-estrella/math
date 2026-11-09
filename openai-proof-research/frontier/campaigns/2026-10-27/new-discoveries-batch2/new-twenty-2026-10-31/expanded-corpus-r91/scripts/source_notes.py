import pathlib,json,hashlib,re,datetime
D=pathlib.Path(__file__).resolve().parents[1];x=json.loads((D/'extracted.json').read_text());out={}
for i,o in x.items():
 a=o['source_url'].rsplit('/',1)[-1];p=D/'sources'/f'{a}.txt';t=p.read_text() if p.exists() else '';lines=t.splitlines();chunks=[]
 for k,l in enumerate(lines):
  if re.search(r'Conjecture|Invariant.Set.Conjecture|Definition 1[5 ]',l,re.I):chunks.append({'line_1based':k+1,'text':'\n'.join(lines[max(0,k-2):k+17])})
 out[i]={'source':str(p),'text_sha256':hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None,'excerpts':chunks}
(D/'outputs/source-excerpts.json').write_text(json.dumps(out,indent=2)+'\n')
files=[D.parent/'ledger.json',D.parent.parent/'ledger.json',D.parent.parent/'prior-campaign-context.json']
r={}
for p in files:
 b=p.read_bytes();o=json.loads(b);r[str(p)]={'sha256':hashlib.sha256(b).hexdigest(),'keys':list(o),'families':{k:v for k,v in o.items() if any(a in k.lower() for a in ['accept','exclud','protect','candidate'])}}
(D/'outputs/inherited-family-review.json').write_text(json.dumps(r,indent=2)+'\n')
