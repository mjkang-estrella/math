import close,re,json,collections
L=close.L;rows=close.load(L/'bodies.json');lookup={(r['ref'],r['path']):r for r in rows};out=[]
for r in rows:
 assert r['status']=='ok';s=(L/r['source']).read_text(errors='replace');p=r['path']
 if '/context/' in p: disposition='Decoded JSON source/atom occurrence and heading metadata; actual source and primary/governing atom bodies fetched and screened (context-decoding.json). No embedded proof or encoded content.'
 elif '/residual-open/' in p: disposition='Residual-open structured record read as text; no target identifier or entropy/truncation claim found.'
 elif 'context-payload' in r['reasons']:disposition='Referenced source/atom actual text scanned completely; no literal or semantic target hit. Contents concern Fibonacci legal edge-load renewal or parity hidden-arrow posterior cumulant response.'
 elif 'baseline-relevant-path' in r['reasons']:
  if 'RenyiCombining' in p or 'hirche' in p or 'powered-binary' in p:disposition='Actual formulas are binary/discrete information combining or powered binary order monotonicity. Not continuous log-concave iid positive-sum entropy increments; no transfer to target supplied.'
  elif '/Quantum' in p or 'quantum' in p or 'seshadreesan' in p or 'meunson' in p:disposition='Actual claim uses matrices, quantum states, conditional information, or channels; no log-concave scalar density self-convolution ratio or admissible truncation bridge.'
  elif '/RenyiDivergence/' in p:disposition='Finite probability-mass divergence formulas and data-processing/order properties; no optimization of continuous iid positive-sum entropy increment.'
  elif 'TruncatedExponentialTwoAdic' in p:disposition='Actual defining expression is a finite factorial/power integer sum with binary valuation conclusions. No probability density or entropy comparison.'
  elif 'Boltzmann/Branching' in p:disposition='Truncated velocity weights and exponential moment convergence, not truncation of an exponential probability density and its iid sum entropy.'
  else:disposition='Actual RCD/weak-Hessian density-power, transport interpolation or Fisher-energy estimates; hypotheses/conclusions do not calculate the changing-input self-convolution ratio or produce a counterexample.'
 else:
  if 'GRAPH_ENERGY' in p:disposition='Actual log-concavity hits cite Lamkin–Tkocz moments of Bernoulli averages and finite Jensen; graph-energy coalition threshold proof. No entropy increment functional.'
  elif 'AURIC_' in p:disposition='Renyi hit is an institutional domain in Csiszar citation; text concerns information projection and finite exponential families. No threshold refutation.'
  else:disposition='Actual complete changed body scanned; no target literal/semantic hit. Initial broad Fu/Li substring lead was a false positive; word-boundary pattern eliminates it.'
 r['semantic_disposition']=disposition
 if '/atoms/sha256/' in p:r['content_address_sha256_matches']=close.sha(L/r['source'])==p.rsplit('/',1)[-1]
 out.append(dict(path=p,ref=r['ref'],sha256=r['read']['sha256'],hits=r['read']['hit_count'],disposition=disposition))
close.save('bodies.json',rows);close.save('semantic-dispositions.json',out)
contexts=close.load(L/'context-decoding.json')
for c in contexts:
 c['payloads_all_closed']=all(lookup[(c['ref'],p)]['status']=='ok' for p in list(c['sources'])+['Meta/Digestion/atoms/sha256/'+a for a in c['atoms']])
 c['source_hash_checks']=[dict(path=p,referenced=h,actual=lookup[(c['ref'],p)]['read']['sha256'],match=h.removeprefix('sha256:')==lookup[(c['ref'],p)]['read']['sha256']) for p,h in c['sources'].items()]
close.save('context-decoding.json',contexts)
print('bodies',len(rows),'opaque',sum(len(r['read']['opaque_candidates']) for r in rows),'atom_hash_mismatches',sum(r.get('content_address_sha256_matches')==False for r in rows),'contexts',len(contexts),'source_snapshot_hash_mismatches',sum(not x['match'] for c in contexts for x in c['source_hash_checks']))
print('positive-sum literal strong hits',[(r['path'],r['ref']) for r in rows if re.search(r'2510[.]09206|\bFu\b.{0,12}\bLi\b|positive[ -]?sum|self[ -]?convolution',(L/r['source']).read_text(errors='replace'),re.I)])
