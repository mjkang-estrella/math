import json,sys,os
L=sys.argv[1];I=L+'/root-mathdb-breadth-intake-r479'
ids=json.load(open(I+'/reserved-ids.json'))['ids']
oth=set(json.load(open(I+'/reserved-ids.json'))['other_active_reservations'])
forbid={372627,372628,368940,404067,364119}
S=set(ids)
print('n',len(ids),len(S),'overlap_other',S&oth,'forbid',S&forbid)
q=json.load(open(I+'/queue.json'));print('queue ids == reserved',[e['mathdb_id'] for e in q]==ids)
cov=json.load(open(I+'/coverage-delta.json'));print('coverage keys',len(cov),'overlap',[i for i in ids if str(i) in cov])
def scan(p):
    t=open(p).read();return [i for i in ids if str(i) in t]
for p in [L+'/root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L+'/root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L+'/root-mathdb-cayley-review-intake-r363/coverage-delta.json',L+'/root-mathdb-cayley-review-intake-r363/disposition.json']:
    print(os.path.basename(os.path.dirname(p)),os.path.basename(p),'textual hits',scan(p))
ae=json.load(open(L+'/root-mathdb-accepted-exclusions-r304/accepted-exclusions.json'))
print(type(ae), list(ae)[:5] if isinstance(ae,dict) else json.dumps(ae[0])[:400])
for e in q: print(e['mathdb_id'],e['post_type'],e['statement_completeness'],e['status'],e['review_priority_score'],e['screening_tags'],e['title'][:70])
