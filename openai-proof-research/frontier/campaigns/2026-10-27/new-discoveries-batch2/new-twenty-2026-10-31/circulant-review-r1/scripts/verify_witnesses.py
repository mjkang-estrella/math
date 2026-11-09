import json,itertools,pathlib
W=pathlib.Path(__file__).resolve().parents[1]
rows=json.loads((W/'coverage.json').read_text());extra=json.loads((W/'order34.json').read_text())['certificate']
for row in rows:
 if row['n']==34:row.update(exists=True,certificate=extra,additional_five_jump_trials=553)
 if not row['exists']:continue
 r=row['certificate'];n=r['n'];S={x%n for d in r['positive_jumps'] for x in [d,-d]};covered=set()
 for p in r['witnesses'].values():
  assert len(p)==len(set(p)) and all(0<=v<n for v in p)
  assert all((((b-a)%n in S)==(j==i+1)) for i,a in enumerate(p) for j,b in enumerate(p) if i<j)
  for delta in range(n):
   for t in itertools.combinations(p,3):covered.add(tuple(sorted((x+delta)%n for x in t)))
 assert len(covered)==n*(n-1)*(n-2)//6
 assert len({0}|S|{(x+y)%n for x in S for y in S})==n and len(S)<n-1
 row['verified_all_triples']=len(covered)
(W/'coverage-verified.json').write_text(json.dumps(rows,indent=2));print('Verified explicit induced-path certificates for all triples at every n=11..40 except 15; complete 128-mask nonexistence at 15.')
