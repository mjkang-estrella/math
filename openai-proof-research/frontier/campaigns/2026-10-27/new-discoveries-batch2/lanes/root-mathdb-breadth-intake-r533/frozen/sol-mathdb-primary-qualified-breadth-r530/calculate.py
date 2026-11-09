import json,pathlib,collections
D=pathlib.Path(__file__).resolve().parent
hits=[];max_seen=0
for a in range(2,101):
 for c in range(2,101):
  diff=collections.defaultdict(list)
  for x in range(1,25):
   for y in range(1,25):
    b=c**y-a**x
    if 1<=b<=1000000:diff[b].append([x,y])
  for b,sol in diff.items():
   max_seen=max(max_seen,len(sol))
   if len(sol)>=3:hits.append({'a':a,'b':b,'c':c,'solutions':sol})
(D/'bounded-calculation.json').write_text(json.dumps({'target':370942,'executed':True,'scope':{'a':[2,100],'c':[2,100],'x':[1,24],'y':[1,24],'b':[1,1000000]},'arithmetic':'exact Python integers','three_solution_hits':hits,'largest_observed_solution_count':max_seen,'limit':'No completeness for any fixed equation and no universal bound; no novelty inference.'},indent=2)+'\n')
print('three-solution hits',len(hits),'max',max_seen)
