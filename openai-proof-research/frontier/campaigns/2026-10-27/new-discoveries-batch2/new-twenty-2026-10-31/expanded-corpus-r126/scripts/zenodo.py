import pathlib,json,sys
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'scripts'));from fetch import get
print(get(('betzer-record.json','https://zenodo.org/api/records/22065778')),flush=True)
p=D/'sources/betzer-record.json'
if p.exists():
 o=json.loads(p.read_text())
 for i,f in enumerate(o.get('files',[])):
  if f.get('key','').endswith('.pdf'):print(get((f'betzer-{i}.pdf',f['links']['self'])),flush=True)
