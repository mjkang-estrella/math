import pathlib,json,itertools,bisect,time,sys
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r174')
def contains(s,u):
 pos={}
 for i,x in enumerate(s):pos.setdefault(x,[]).append(i)
 def rec(j,start,mapping):
  if j==len(u):return True
  x=u[j]
  if x<len(mapping):
   ps=pos[mapping[x]];z=bisect.bisect_left(ps,start)
   return z<len(ps) and rec(j+1,ps[z]+1,mapping)
  for y,ps in pos.items():
   if y in mapping:continue
   z=bisect.bisect_left(ps,start)
   if z<len(ps) and rec(j+1,ps[z]+1,mapping+(y,)):return True
  return False
 return rec(0,0,())
def produce(u,N):
 r=max(u)+1;s=list(range(r-1));lens={}
 for n in range(r-1,N+1):
  while True:
   found=False
   for x in range(n):
    for p in range(len(s)+1):
     if x in s[max(0,p-r+1):min(len(s),p+r-1)]:continue
     cand=s[:p]+[x]+s[p:]
     if not contains(cand,u):s=cand;found=True;break
    if found:break
   if not found:break
  lens[n]=len(s)
 return lens,s
if __name__ == '__main__':
 patterns=['abcacbc','abbacac','abcacba','abacaba','abcabca','abcbabc','abacbcac','abcbacbc','abacbabc','abcabacbc','abcbacab','abcdabcd']
 if len(sys.argv)>1:patterns=patterns[int(sys.argv[1]):int(sys.argv[2])]
 t=time.monotonic()
 for pat in patterns:
  u=tuple(ord(x)-97 for x in pat);lens,s=produce(u,18)
  d={'pattern':pat,'through_n':18,'lengths':lens,'final_word':s,'increments':[lens[n]-lens[n-1] for n in range(max(u)+2,19)],'seconds':time.monotonic()-t}
  print(json.dumps(d),flush=True)
  with (L/'outputs/sequence-search.jsonl').open('a') as f:f.write(json.dumps(d)+'\n')
