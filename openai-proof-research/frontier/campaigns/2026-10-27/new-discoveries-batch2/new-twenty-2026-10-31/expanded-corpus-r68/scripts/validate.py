import pathlib,json,hashlib,random,contextlib,io,runpy,collections
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
x=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert set(x)==set(map(str,ids)) and len(x)==40
for i,o in x.items():
 b=(D/'raw'/f'{i}.jsonl').read_bytes();assert b.endswith(b'\n');assert sha(b)==o['provenance']['raw_sha256'];q=json.loads(b);assert q['statement']==o['statement'];assert sha(o['statement'].encode())==o['provenance']['statement_utf8_sha256'];assert o['credit']==0 and o['formal_endpoint'] is None
for p in (D/'sources').glob('*.receipt.json'):
 r=json.loads(p.read_text())
 if r.get('status')==200:assert sha(pathlib.Path(r['path']).read_bytes())==r['sha256']
with contextlib.redirect_stdout(io.StringIO()):v=runpy.run_path(str(D/'scripts/extremal.py'))
nx=v['nx'];random.seed(68068)
for _ in range(100):
 h=random.choice(v['bases']);w=[random.randint(1,4) for i in h];cl=[bool(random.getrandbits(1)) for i in h];g=nx.Graph();clusters=[[(i,j) for j in range(w[i])] for i in h]
 for c in clusters:g.add_nodes_from(c)
 for i in h:
  if cl[i]:g.add_edges_from(__import__('itertools').combinations(clusters[i],2))
 for i,j in h.edges():g.add_edges_from((a,b) for a in clusters[i] for b in clusters[j])
 assert v['mostar'](g)==v['blow_score'](h,w,cl)
checks={'utc':__import__('datetime').datetime.now(__import__('datetime').timezone.utc).isoformat(),'exact_reserved_entries':40,'raw_bytes_and_statement_hashes':'pass','source_HTTP_hashes':'pass','expanded_distance_crosschecks':100,'Lean_endpoint':False,'Lean_checks':'not applicable; no endpoint proposed','no_credit_claim':True}
(D/'outputs/validation.json').write_text(json.dumps(checks,indent=2)+'\n');print(json.dumps(checks,indent=2))
