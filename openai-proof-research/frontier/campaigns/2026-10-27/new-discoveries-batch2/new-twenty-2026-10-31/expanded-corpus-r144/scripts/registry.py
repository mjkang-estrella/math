import pathlib,json,urllib.request,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1]
def fetch(u,name):
 try:
  with urllib.request.urlopen(u,timeout=20) as r:b=r.read();status=r.status
  (D/'sources'/name).write_bytes(b)
  rec=dict(url=u,file=name,status=status,sha256=hashlib.sha256(b).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
  with (D/'sources/receipts.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  return json.loads(b)
 except Exception as e:print(u,str(e));return {}
head=json.loads((D/'sources/omega-head.json').read_text())['sha']
tree=fetch(f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{head}?recursive=1','omega-tree.json')
print('omega',head,'truncated',tree.get('truncated'))
words=['350736','351456','352364','352367','364485','345184','345351','345827','346167','346763','346921','346984','347033','347489','347559','347594','347961','347962','348055','348349','alder','seurat','paired','rainbow','gao','berkovich','sidon','ternary','vertically','ptmc']
matches=[x['path'] for x in tree.get('tree',[]) if any(w in x['path'].lower() for w in words)]
print(json.dumps(matches,indent=2))
head2=json.loads((D/'sources/openai-head.json').read_text())['sha']
print('openai',head2)
tree2=fetch(f'https://api.github.com/repos/openai/math/git/trees/{head2}?recursive=1','openai-tree.json')
print('openai tree truncated',tree2.get('truncated'))
matches2=[x['path'] for x in tree2.get('tree',[]) if any(w in x['path'].lower() for w in words)]
print(json.dumps(matches2,indent=2))
