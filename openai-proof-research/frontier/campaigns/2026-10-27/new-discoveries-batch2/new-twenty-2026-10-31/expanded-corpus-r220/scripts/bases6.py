import pathlib
p=pathlib.Path(__file__).resolve().parent/'bases5.py';s=p.read_text().split('for c in (4,3,2):')[0].replace('r=5;','r=6;');exec(compile(s,str(p),'exec'))
for c in (2,3,4,5):
 removed=1<<(r-c);target=full^((1<<removed)-1);baseline=score(target);best=baseline;checked=0;cur=target;value=baseline
 # Ten random restarts, each followed by 500 one-exchange proposals.
 for restart in range(10):
  cur=full^sum(1<<x for x in rng.sample(range(N),removed));value=score(cur)
  for step in range(500):
   inside=[x for x in range(N) if cur>>x&1];outside=[x for x in range(N) if not cur>>x&1];T=cur^(1<<rng.choice(inside))^(1<<rng.choice(outside));v=score(T);checked+=1
   if v>=value:cur=T;value=v
   if v>best:best=v;print('new max',c,best,baseline,flush=True)
 out.append({'r':r,'c':c,'mode':'10 random restarts x 500 exchange proposals, seed 220','checked':checked,'proposed_bases':baseline,'best':best});print(out[-1],flush=True);(L/'outputs/bases6-data.json').write_text(json.dumps(out,indent=2))
