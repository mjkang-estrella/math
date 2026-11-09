import pathlib,json,sys
D=pathlib.Path(__file__).resolve().parents[1];N=int(sys.argv[1]);L=4096
# Standard regular paperfolding: odd part 1 mod 4 is opening; complement also tested.
res=[]
for orient in (1,-1):
 starts={0:[0]};h=0;lengths=set();witness={};count=0
 for t in range(1,N+1):
  odd=t//(t&-t);h+=orient*(1 if odd%4==1 else -1)
  starts.pop(h+1,None)
  for i in starts.get(h,[]):
   length=t-i
   if length<=L:lengths.add(length);witness.setdefault(length,i);count+=1
  starts.setdefault(h,[]).append(t)
 allowed={2**k-2**i for k in range(1,14) for i in range(k) if 2**k-2**i<=L}
 bad=sorted(lengths-allowed);missing=sorted(allowed-lengths)
 o=dict(prefix_length=N,max_tested_length=L,orientation=orient,number_of_Dyck_intervals=count,lengths=sorted(lengths),unexpected_lengths=bad,unseen_formula_lengths=missing,witness_starts=witness);res.append(o);print(json.dumps(o),flush=True)
(D/f'paperfold-{N}.json').write_text(json.dumps(res,indent=2)+'\n')
