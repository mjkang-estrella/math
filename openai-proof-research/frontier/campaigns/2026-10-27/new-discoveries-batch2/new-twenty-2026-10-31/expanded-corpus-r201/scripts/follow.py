import pathlib,sys,json,re,subprocess,hashlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import fetch,D
out=json.loads((D/'outputs/registry-screen.json').read_text()); sha=out['heads']['the-omega-institute/trureturing']; repo='the-omega-institute/trureturing'
r=next(r for r in out['receipts'] if '/'+repo+'/git/trees/' in r['url']); tree=json.loads(pathlib.Path(r['body']).read_text());paths=[]
for scope in ['D5','Problems']:
 x=next((x for x in tree['tree'] if x['path']==scope),None)
 if x is None:
  z=fetch(f'https://api.github.com/repos/{repo}/git/trees/{sha}','omega-root');out['receipts'].append(z);x=next(x for x in json.loads(pathlib.Path(z['body']).read_text())['tree'] if x['path']==scope)
 z=fetch(f'https://api.github.com/repos/{repo}/git/trees/{x["sha"]}?recursive=1','omega-'+scope);out['receipts'].append(z)
 t=json.loads(pathlib.Path(z['body']).read_text());print(scope,'truncated',t.get('truncated'),len(t.get('tree',[])))
 paths += [scope+'/'+x['path'] for x in t.get('tree',[]) if x['type']=='blob']
pat=re.compile('bruhat|popstack|hard.?square|panyushev|symplectic|quadrangul|speyer|boone|theta|zcurve|z-curve|uncu|extremalprime|pons|batle|quasitransitive',re.I)
match=[p for p in paths if pat.search(p)];(D/'outputs/registry-path-matches.json').write_text(json.dumps(match,indent=2));print('\n'.join(match))
for n,p in enumerate(p for p in match if p.endswith('.lean') and ('PopStackSimple' in p or 'Bruhat' in p)):
 out['receipts'].append(fetch(f'https://raw.githubusercontent.com/{repo}/{sha}/{p}','omega-proof-'+str(n)))
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2))
extra=['2404.01973','2609.08816','2601.09551']
receipts=[]
for aid in extra:
 z=fetch('https://arxiv.org/abs/'+aid,'follow-abs-'+aid);receipts.append(z)
 if z['status']!=200:continue
 s=pathlib.Path(z['body']).read_text();vs=sorted(set(re.findall('/abs/'+re.escape(aid)+r'v(\d+)',s)),key=int) or ['1']
 for v in vs:
  r=fetch(f'https://arxiv.org/pdf/{aid}v{v}','follow-pdf-'+aid+'v'+v);receipts.append(r)
  if r['status']==200:subprocess.run(['pdftotext','-layout',r['body'],str(D/f'outputs/{aid}v{v}.txt')])
(D/'outputs/follow-receipts.json').write_text(json.dumps(receipts,indent=2))
# Honest compact prior context: parse complete JSONs, retain disposition summaries, no shared writes.
ctx={}
for p in [D.parent/'ledger.json',D.parent.parent/'prior-campaign-context.json']:
 b=p.read_bytes();o=json.loads(b);ctx[str(p)]={'sha256':hashlib.sha256(b).hexdigest(),'keys':list(o),'accepted':o.get('accepted'),'excluded':o.get('excluded')}
(D/'outputs/inherited-context.json').write_text(json.dumps(ctx,indent=2))
