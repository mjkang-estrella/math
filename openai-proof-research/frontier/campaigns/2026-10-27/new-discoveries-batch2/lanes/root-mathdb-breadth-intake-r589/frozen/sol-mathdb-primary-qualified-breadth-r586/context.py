from pathlib import Path
import json
D=Path(__file__).parent;L=D.parent;B=L.parent
ld=lambda p:json.loads(p.read_text())
ids=set(ld(L/'root-mathdb-breadth-intake-r585/reserved-ids.json')['ids']);protected={337963,338290,339564,372627,372628,368940,404067,364119,366370,365437,365439}
c585=ld(L/'root-mathdb-breadth-intake-r585/coverage-delta.json');c587=ld(L/'root-mathdb-breadth-intake-r587/coverage-delta.json');assert len(c585)==5583 and len(c587)==5633
seen=set()
for r in ld(L/'root-mathdb-breadth-intake-r587/active-breadth-reservations.json'):
 s=set(r['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,c587)) and not s&protected;seen|=s
assert ids<=seen
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 a=ld(L/'root-mathdb-accepted-exclusions-r304'/name);txt=json.dumps(a);print(name,'keys',list(a),'assigned ID references',[i for i in sorted(ids) if str(i) in txt])
for name in ['ledger.json','prior-campaign-context.json']:
 a=ld(B/name);print(name,'top-level',list(a)[:15])
print('old incomplete preserved', {k:c587[k].get('statement_completeness',c587[k].get('scope')) for k in ['344924','386396','387650']})
(D/'prior-context-check.json').write_text(json.dumps({'baseline_record_reviews':5583,'latest_record_reviews':5633,'all_current_reservation_sets_disjoint':True,'r586_exact50_disjoint_current_coverage':True,'protected_disjoint':True,'r304_assigned_id_hits':[],'no_promotion':True},indent=2)+'\n')
