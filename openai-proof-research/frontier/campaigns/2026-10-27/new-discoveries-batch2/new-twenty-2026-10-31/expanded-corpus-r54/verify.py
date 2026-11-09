import pathlib,json,itertools,hashlib,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
D=pathlib.Path(__file__).resolve().parent
r=json.load(open(D/'results.json'));res=json.load(open(D/'reservation.json'));assert len(r)==40 and set(r)==set(map(str,res['ids']))
for i,v in r.items():
 b=(D/v['raw_file']).read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==v['raw_provenance']['raw_sha256'];assert json.loads(b)['statement']==v['literal_statement'];assert hashlib.sha256(v['literal_statement'].encode()).hexdigest()==v['statement_sha256_utf8']
# Independent affine span by explicit XOR closure, not Gaussian elimination.
rows=json.loads((D/'sustained-r2.log').read_text().splitlines()[1])['results']
for v in rows:
 S=v['set'];assert len(S)==v['l'] and len(set(S))==len(S)
 T={0}
 for a in S:
  z=a^S[0];T |= {b^z for b in list(T)}
 assert len(T)>1<<(v['l']-1).bit_length()
 q=sum(a^b^c^d==0 for a,b,c,d in itertools.combinations(S,4));assert q==v['best_outside_quads']
 L=range(v['l']-1);q0=sum(a^b^c^d==0 for a,b,c,d in itertools.combinations(L,4));assert q0==v['lex_lower_bound_for_Q_lminus1']
print(json.dumps({'results_count':len(r),'raw_line_and_statement_integrity':'PASS','independent_local_search_rank_and_quad_count_checks':len(rows),'status':'PASS','scope':'diagnostic verification only; no theorem or novelty clearance'}))
