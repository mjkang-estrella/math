import pathlib,json,hashlib,re,itertools,urllib.request,datetime
L=pathlib.Path(__file__).resolve().parents[1]
# Independent positional checker, different from adjacent-filter predicate used by Lean.
w=json.loads((L/'outputs/grid-3-5-witness.json').read_text())['word']
p=[[i for i,a in enumerate(w) if a==v] for v in range(15)]
rows=[]
for a,b in itertools.combinations(range(15),2):
 x,y=p[a],p[b]
 alternating=(x[0]<y[0]<x[1]<y[1]<x[2]<y[2]) or (y[0]<x[0]<y[1]<x[1]<y[2]<x[2])
 ar,ac=divmod(a,5);br,bc=divmod(b,5)
 adjacent=(ar==br and (abs(ac-bc)==1 or abs(ac-bc)==4)) or (ac==bc and ar!=br)
 assert alternating==adjacent
 rows.append(dict(a=a,b=b,positions_a=x,positions_b=y,adjacent=adjacent,alternating=alternating))
assert all(len(x)==3 for x in p)
(L/'outputs/pair-certificate.json').write_text(json.dumps(rows,indent=2))
print('independent positional verification: 105 pairs, 30 edges, 75 nonedges, every count 3')
t=json.loads((L/'sources/openai-tree.json').read_text())
print('OpenAI root truncated:',t.get('truncated'))
relevant=[x for x in t['tree'] if re.search('word.?represent|toroidal.?grid|cylindric',x['path'],re.I)]
print('OpenAI relevant paths:',relevant)
# The complete preprints subtree, independent of root recursive truncation.
x=next((x for x in t['tree'] if x['path']=='preprints'),None)
if x:
 url='https://api.github.com/repos/openai/math/git/trees/'+x['sha']+'?recursive=1'
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research evidence'}),timeout=20) as s:d=s.read();status=s.status
  (L/'sources/openai-preprints.json').write_bytes(d)
  receipt=dict(url=url,status=status,sha256=hashlib.sha256(d).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
  (L/'outputs/openai-preprints-receipt.json').write_text(json.dumps(receipt,indent=2))
  q=json.loads(d);print('OpenAI preprints truncated:',q.get('truncated'),'entries',len(q['tree']))
  for x in q['tree']:
   if re.search('word.?represent|toroidal.?grid|cylindric',x['path'],re.I):print(x)
 except Exception as e:print('preprints fetch',repr(e))
# Exact statement hashes supplement raw line hashes.
d=json.loads((L/'outputs/intake.json').read_text())
for k,x in d.items():
 x['statement_sha256']=hashlib.sha256(x['record']['statement'].encode()).hexdigest()
(L/'outputs/intake.json').write_text(json.dumps(d,indent=2))
