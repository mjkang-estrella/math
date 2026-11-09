import pathlib,json,time,random,sys,itertools
D=pathlib.Path(__file__).resolve().parents[1]; rng=random.Random(239); start=time.monotonic(); rows=[]; totalnodes=0
begin=int(sys.argv[1]);tag=sys.argv[2]
N=144;n=12;full=(1<<N)-1
for k in [3]:
 tested=0;skipped=0;nodes=0;timeouts=0
 for sample,extra in enumerate(itertools.islice(itertools.combinations(range(n-k,N),k),begin,None),begin):
  if time.monotonic()-start>105:break
  A=list(range(n-k))+sorted(extra)
  if len({x%n for x in A})==n:skipped+=1;continue
  masks=[]
  for b in range(N):masks.append(sum(1<<((a+b)%N) for a in A))
  bypoint=[[(x-a)%N for a in A] for x in range(N)]
  deadline=time.monotonic()+.15; localnodes=[0]
  def dfs(covered,bs):
   localnodes[0]+=1
   if localnodes[0]%128==0 and time.monotonic()>deadline:raise TimeoutError
   if covered==full:return bs
   best=None;remain=full^covered
   while remain:
    bit=remain&-remain;x=bit.bit_length()-1;remain^=bit
    opts=[b for b in bypoint[x] if not masks[b]&covered]
    if not opts:return None
    if best is None or len(opts)<len(best):best=opts
    if len(best)==1:break
   for b in best:
    ans=dfs(covered|masks[b],bs+[b])
    if ans is not None:return ans
   return None
  try:ans=dfs(masks[0],[0]);tested+=1
  except TimeoutError:timeouts+=1;ans=None
  nodes+=localnodes[0]
  if ans is not None:
   assert len(ans)==N//n
   counts=[sum((x-a)%N in ans for a in A) for x in range(N)];assert set(counts)=={1}
   (D/'cyclic-exhaustive-witness.json').write_text(json.dumps({'A':A,'B':ans,'omega':N,'n':n,'k':k},indent=2));print('WITNESS',A,ans,flush=True);sys.exit()
 rows.append({'omega':N,'n':n,'k':k,'begin_index':begin,'last_loop_index':sample,'actually_assessed':tested+skipped+timeouts,'next_index':begin+tested+skipped+timeouts,'completed_negative_exact_cover_tests':tested,'already_complete_residue_samples_skipped':skipped,'indeterminate_per_sample_timeouts':timeouts,'nodes':nodes});print(rows[-1],flush=True)
(D/('cyclic-prefix-'+tag+'.json')).write_text(json.dumps({'seed':239,'rows':rows,'seconds':time.monotonic()-start,'claim':'Diagnostic only; each finished test is an exhaustive complement search with 0 in B; Lexicographic A prefix; see samples_attempted for exact prefix endpoint (last iteration may be untested at wall cutoff).'},indent=2)+'\n')
