import pathlib,json,runpy
D=pathlib.Path(__file__).resolve().parents[1]
# independent literal subset check, no threshold DP
w=json.loads((D/'outputs/replication-sa-16-194.json').read_text())['witness'];n=len(w)
def check(w,cycle):
 bad=[];hist={}
 for m in range(1,1<<n):
  k=m.bit_count();val=max([w[i] for i in range(n) if m>>i&1]+[w[i]+w[(i+1)%n] for i in range(n if cycle else n-1) if m>>i&1 and m>>((i+1)%n)&1]);hist[val-k]=hist.get(val-k,0)+1
  if val<k:bad.append(m)
 return {'bad_count':len(bad),'first_bad':bad[:10],'slack_histogram':hist}
out={'w':w,'total':sum(w),'cycle':check(w,True),'path_cuts':[check(w[i:]+w[:i],False) for i in range(n)]}
(D/'outputs/replication-witness-check.json').write_text(json.dumps(out,indent=2));print('total',sum(w),'cycle bad',out['cycle']['bad_count'],'path cut bad counts',[v['bad_count'] for v in out['path_cuts']])
