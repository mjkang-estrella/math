import pathlib,importlib.util,json,itertools,time,sys
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r174')
s=importlib.util.spec_from_file_location('seq',L/'scripts/sequence_search.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
def words(n,r,p=(0,)):
 if len(p)==n:
  if max(p)==r-1:yield p
 else:
  for a in range(min(r,max(p)+2)):
   yield from words(n,r,p+(a,))
patterns=list(words(7,3))+list(words(8,3))
start=int(sys.argv[1]);end=int(sys.argv[2]);t=time.monotonic()
for j in range(start,min(end,len(patterns))):
 if time.monotonic()-t>90:print('voluntary 90s stop at',j,flush=True);break
 u=patterns[j];lens,word=m.produce(u,10);inc=[lens[n]-lens[n-1] for n in range(4,11)]
 d=dict(index=j,pattern=''.join(chr(97+a) for a in u),lengths=lens,increments=inc,final_word=word)
 with (L/'outputs/sequence-broad.jsonl').open('a') as f:f.write(json.dumps(d)+'\n')
 print(j,d['pattern'],lens[10],inc,flush=True)
