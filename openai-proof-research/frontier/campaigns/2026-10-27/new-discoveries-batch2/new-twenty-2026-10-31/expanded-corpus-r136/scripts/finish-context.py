import pathlib,json,hashlib,re
D=pathlib.Path(__file__).resolve().parents[1]
heads={}
for p in D.glob('sources/*-HEAD.json'):
 o=json.loads(p.read_text());heads[p.name]={'head':o['sha'],'tree':o['commit']['tree']['sha'],'receipt':str(p.relative_to(D))+'.receipt.json'}
ver={}
for p in D.glob('sources/*.abs.html'):
 text=p.read_text(); versions=re.findall(r'\[v(\d+)\]',text);ver[p.name]={'current':re.search(r'og:url" content="([^"]+)',text).group(1),'versions':sorted(set(versions),key=int)}
(D/'outputs/versions.json').write_text(json.dumps(ver,indent=2)+'\n')
paths={}
for s in ['D5','Problems']:
 p=D/f'sources/omega-{s}.json';o=json.loads(p.read_text());paths[s]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'tree_sha':o['sha'],'truncated':o['truncated'],'entries':len(o['tree'])}
(D/'outputs/registry-screen.json').write_text(json.dumps({'heads':heads,'omega_scopes':paths,'screen':'ID/title/source and filename keywords; no exhaustive proof-body clearance','OpenAI_scope':'current head verified; inherited preprints scope not live full-body reviewed'},indent=2)+'\n')
# Retain precise labeled primary paragraphs for reproducible human review, not a claim every proof was read.
keys=['Conjecture','nontrivial uniquely','Proof of Conjecture','Definition 3.12','Theorem 1.4','viable if','closed under permutations']
out=[]
for p in sorted(D.glob('sources/*.txt')):
 ls=p.read_text().splitlines()
 for i,l in enumerate(ls):
  if any(k in l for k in keys):out.append({'source':str(p.relative_to(D)),'line':i+1,'context':'\n'.join(ls[max(0,i-2):i+9])})
(D/'outputs/source-passages.json').write_text(json.dumps(out,indent=2)+'\n')
print('versions',len(ver),'registry scopes',paths)
