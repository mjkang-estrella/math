from rebatch import *
cases=json.loads((L/'reduced-cases.json').read_text());mods=[]
for a,b,e in cases:
 if (a,b,e)==(9,6,0):continue
 mods+=rebatch(a,b,e)
(L/'rebatched-plan.txt').write_text('\n'.join(mods)+'\n');print(len(mods))
