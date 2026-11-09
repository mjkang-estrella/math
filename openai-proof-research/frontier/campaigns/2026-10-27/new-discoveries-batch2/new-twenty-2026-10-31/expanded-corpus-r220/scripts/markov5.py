import pathlib
p=pathlib.Path(__file__).resolve().parent/'markov.py'
# Reuse only this lane's checker definitions, before its experiment driver.
exec(compile(p.read_text().split('for n in range(2,5):')[0],str(p),'exec'))
n=5;pairs=list(itertools.permutations(range(n),2));ct={}
for bits in range(1<<len(pairs)):
 result=test(n,[e for k,e in enumerate(pairs) if bits>>k&1]);key=result if isinstance(result,str) else 'COUNTEREXAMPLE';ct[key]=ct.get(key,0)+1
 if isinstance(result,dict):print(result,flush=True);(L/'outputs/markov5-candidate.json').write_text(json.dumps(result));break
 if bits%65536==65535:print(bits+1,ct,flush=True);(L/'outputs/markov5-progress.json').write_text(json.dumps({'graphs':bits+1,'counts':ct}))
print(ct,flush=True);(L/'outputs/markov5-data.json').write_text(json.dumps({'graphs':bits+1,'counts':ct}))
