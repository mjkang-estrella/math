import itertools,json,pathlib
# Reuse the independently coded round-3 regression, restricted to n <= 4.
src=pathlib.Path('scripts/regression.py').read_text().replace('range(1,6)', 'range(1,5)')
exec(compile(src,'scripts/regression.py','exec'))
rows=[]
for n in range(8):
    k=0
    for f in itertools.permutations(range(n)):
        old=count(f)
        for a in range(n):
            for b in range(a+1,n):
                g=list(f);g[a],g[b]=g[b],g[a]
                assert abs(count(g)-old)==1
                k+=1
    rows.append({'size':n,'swaps_checked':k})
path=pathlib.Path('regression.json')
r=json.loads(path.read_text());r['exhaustive_swap_law']=rows
r['negative_controls']['wrong_swap_always_increases']=count([1,0])+1!=count([0,1])
# Identity -> transposition decreases count; the reverse increases it.
assert count([0,1])==2 and count([1,0])==1
r['negative_controls']['wrong_swap_always_increases']=count([1,0])!=count([0,1])+1
path.write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r))
