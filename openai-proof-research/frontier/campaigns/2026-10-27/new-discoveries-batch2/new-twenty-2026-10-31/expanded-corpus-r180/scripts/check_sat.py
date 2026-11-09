import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];log=(D/'logs/torus-sat-exact.log').read_text();assert 's SATISFIABLE' in log
true={int(v) for l in log.splitlines() if l.startswith('v ') for v in l[2:].split() if int(v)>0};model=json.loads((D/'outputs/torus-3-5-model.json').read_text());labels=[]
for row in model['X']:
 hits=[i+1 for i,x in enumerate(row) if x in true];assert len(hits)==1;labels+=hits
q=len(labels);assert sorted(labels)==list(range(1,q+1));weights=[sum(l for e,l in zip(model['edges'],labels) if v in e) for v in range(15)];assert weights==[62]*15
out={'n':3,'m':5,'labels':labels,'edges':model['edges'],'weights':weights,'verified':'direct independent integer sums and bijectivity','status':'finite existence only, no universal solution or novelty claim'};(D/'outputs/torus-sat-certificate.json').write_text(json.dumps(out,indent=2));print(out)
