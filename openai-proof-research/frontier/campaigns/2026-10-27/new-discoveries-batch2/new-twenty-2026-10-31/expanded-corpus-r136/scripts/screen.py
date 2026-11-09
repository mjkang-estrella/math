import json,pathlib,re,hashlib,sys,subprocess
D=pathlib.Path(__file__).resolve().parents[1]; P=json.loads((D/'outputs/provenance.json').read_text())
if sys.argv[1]=='context':
 out={}
 for p in [D.parent/'ledger.json',D.parent.parent/'ledger.json',D.parent.parent/'prior-campaign-context.json']:
  o=json.loads(p.read_text());out[str(p)]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'top_keys':list(o),'accepted':o.get('accepted',[]),'excluded':o.get('excluded',[])}
 (D/'outputs/ledger-screen.json').write_text(json.dumps(out,indent=2)+'\n')
 for i in P:
  hits=[]
  for f in (D/'outputs/history-files.txt').read_text().splitlines():
   p=pathlib.Path(f)
   for n,l in enumerate(p.open(),1):
    if re.search(r'(?<![0-9a-f])'+i+r'(?![0-9a-f])',l):hits.append({'file':f,'line':n,'text':l[:1200]})
  print(i,json.dumps(hits))
 for p in D.glob('sources/*-HEAD.json'):
  o=json.loads(p.read_text());print(p.name,o['sha'],o['commit']['tree']['sha'])
 print('networkx');import networkx;print(networkx.__version__)
