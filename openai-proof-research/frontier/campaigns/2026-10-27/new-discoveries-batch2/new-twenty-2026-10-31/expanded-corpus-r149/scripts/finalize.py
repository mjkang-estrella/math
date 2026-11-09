import pathlib,json
L=pathlib.Path(__file__).resolve().parents[1];p=L/'results.json';d=json.loads(p.read_text())
v=d['368808'];v['outcome']='parked_historical_alias_do_not_repeat'
v['historical_check']='Title-based search found the identical conjecture parked under ID 354609 in expanded-corpus-r142. Read r142 SUMMARY.md and corresponding results.json disposition. Protected prior route retained; no further BHR investigation. Initial order-11 diagnostic was redundant.'
v['mathematical_attempts']+=' Historical alias 354609, r142, subsequently found and route stopped.'
v=d['382034']
v['mathematical_attempts']+=' Final second dimension-8 run skips the facet-containing root branch: 9682944 nodes, zero completed partitions, 100.097 seconds, not exhaustive. This is limited branch search, not a verified n=8 lower bound.'
v['remaining_lemma_or_gap']+=' Two capped n=8 traversals did not complete even one root branch; a SAT/ILP or canonical generation method is needed to make the beyond-range search effective.'
p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
s=L/'SUMMARY.md'
s.write_text(s.read_text()+'\nFinal second dimension-8 log: 9,682,944 nodes, no completed partition, 100.097 seconds, not exhaustive. Neither capped dimension-8 run is counted as completed object coverage.\n')
# Full reserved-title search patterns retained for reproducibility.
(L/'outputs/reserved-title-patterns.txt').write_text('\n'.join(v['title'] for v in d.values())+'\n')
