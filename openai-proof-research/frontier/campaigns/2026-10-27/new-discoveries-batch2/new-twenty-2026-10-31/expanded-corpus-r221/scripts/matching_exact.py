import pathlib,sys,json,time,runpy
D=pathlib.Path(__file__).resolve().parents[1]
# Import definitions without executing the sampling driver.
s=(D/'scripts/matching_search.py').read_text().split('stats={};hit=None')[0];ns={'__file__':str(D/'scripts/matching_search.py')};exec(compile(s,str(D/'scripts/matching_search.py'),'exec'),ns);run=ns['run']
N=int(sys.argv[1]);n=N//2;start=time.monotonic()
def parts(n,lo=2):
 if n==0:yield []
 for k in range(lo,n+1):
  for p in parts(n-k,k):yield [k]+p
M1=[(2*i,2*i+1) for i in range(n)];stats=[];hit=None;complete=True
for partition in parts(n):
 M2=[];off=0
 for k in partition:
  M2 += [(2*(off+i)+1,2*(off+(i+1)%k)) for i in range(k)];off+=k
 forbidden={tuple(sorted(e)) for e in M1+M2}
 def pms(s,es):
  if not s:yield es;return
  a=s[0]
  for k in range(1,len(s)):
   b=s[k]
   if (a,b) not in forbidden:yield from pms(s[1:k]+s[k+1:],es+[(a,b)])
 tested=connected=0
 for m3 in pms(list(range(N)),[]):
  if time.monotonic()-start>100:complete=False;break
  tested+=1;bad=run([M1,M2,m3],N)
  if bad is not None:connected+=1
  if bad:hit={'matchings':[M1,M2,m3],'missing':bad};break
 stats.append({'two_colour_cycle_half_lengths':partition,'third_matchings_tested':tested,'connected_unions_tested':connected});print(stats[-1],flush=True)
 if hit or not complete:break
out={'N':N,'complete':complete,'hit':hit,'stats':stats,'seconds':time.monotonic()-start,'coverage':'M1 fixed; M2 all disjoint perfect matchings up to stabilizer of M1, parametrized by even cycle lengths; every disjoint M3 enumerated; only connected simple unions checked'}
(D/f'outputs/matching-exact-{N}.json').write_text(json.dumps(out,indent=2));print('FINAL',out,flush=True)
