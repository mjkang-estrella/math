import pathlib,json,hashlib,itertools,sys,collections,os,datetime
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();R=json.loads((D/'results.json').read_text());res=json.loads((D/'reservation.json').read_text());assert len(R)==20 and set(R)==set(map(str,res['ids']))
for i,r in R.items():
 raw=(D/f'raw/{i}.jsonl').read_bytes();assert raw.endswith(b'\n');o=json.loads(raw);assert r['statement']==o['statement'];assert sha(raw)==r['provenance']['raw_sha256'];assert sha(o['statement'].encode())==r['provenance']['statement_utf8_sha256'];assert sha((D/r['source_local']).read_bytes())==r['source_sha256']
 for a in r['artifacts']:assert (D/a).is_file(),a
assert all(not r['formal_endpoint_complete'] and r['credit']==0 for r in R.values())
sys.path.insert(0,str(D/'scripts'));from cnsf_source import compositions_with_ones
# Import only definitions; do not re-run driver.
s=(D/'scripts/cnsf_search.py').read_text().split('mode=sys.argv[1]')[0];env={'__file__':str(D/'scripts/cnsf_search.py')};exec(s,env);sig=env['sig'];ct=0
for n in range(3,10):
 for p in itertools.product([-1,1],repeat=n-1):
  expected=[]
  for k,comps in enumerate(compositions_with_ones(p),2):
   counts=[0]*(n-k+1)
   for c in comps:counts[c.index(k)]+=1
   expected+=counts
  assert sig(p)==bytes(expected);ct+=1
# Three-state domination DP independently checked by full subset enumeration.
s=(D/'scripts/tree_band.py').read_text().split('out=[]')[0];env={'__file__':str(D/'scripts/tree_band.py')};exec(s,env);calc=env['calc'];random=env['random'];tct=0
for n in range(2,11):
 for t in range(50):
  adj=[[]for _ in range(n)]
  for v in range(1,n):p=random.randrange(v);adj[p].append(v);adj[v].append(p)
  _,_,a,b,_=calc(adj);exact=n
  for mask in range(1<<n):
   if any((mask>>u&1)and(mask>>v&1) for u in range(n)for v in adj[u]):continue
   if all(mask>>u&1 or any(mask>>v&1 for v in adj[u])for u in range(n)):exact=min(exact,mask.bit_count())
  assert min(a,b)==exact,(n,t,a,b,exact);tct+=1
pids=[]
for p in pathlib.Path('/proc').iterdir():
 if not p.name.isdigit() or int(p.name) in {os.getpid(),os.getppid()}:continue
 try:
  if p.joinpath('cwd').resolve()!=D:continue
  args=p.joinpath('cmdline').read_bytes().split(b'\0')
  if args and b'python' in pathlib.Path(os.fsdecode(args[0])).name.encode() and any(a.startswith(b'scripts/')for a in args[1:]):pids.append(dict(pid=int(p.name),argv=list(map(os.fsdecode,args))))
 except (OSError,RuntimeError):pass
(D/'outputs/process-audit.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),remaining_lane_search_processes=pids),indent=2));assert not pids,pids
out=dict(ids=20,raw_statement_source_hash_bindings=True,all_named_artifacts_exist=True,cnsf_signatures_against_source=ct,tree_domination_dp_against_exhaustive_subsets=tct,background_lane_searches=0,Lean_calls=0,qualified_endpoints=0)
(D/'outputs/validation.json').write_text(json.dumps(out,indent=2));print(out)
