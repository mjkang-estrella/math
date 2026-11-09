import json,pathlib,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
ex=json.loads((D/'extracted.json').read_text()); disp=json.loads((D/'scripts/dispositions.json').read_text())
ids=json.loads((D/'reservation.json').read_text())['ids']
out={}
for i in ids:
    o=ex[str(i)]; a=o['source_url'].rsplit('/',1)[-1]
    absf=D/'sources'/f'{a}.abs.html'; rec=json.loads((D/'sources'/f'{a}.abs.html.receipt.json').read_text())
    html=absf.read_text(errors='replace'); versions=sorted(set(re.findall(r'\[(v\d+)\]',html)))
    e={'mathdb_id':i,'title':o['title'],'canonical_url':o['canonical_url'],'source_url':o['source_url'],
       'first_stated_year':o['first_stated_year'],'solution_count':o.get('solution_count'),
       'provenance':o['provenance'],
       'arxiv_abs_receipt':{k:rec.get(k) for k in ('url','utc','status','sha256')},'arxiv_versions_listed':versions}
    ep=D/'downloads'/a/'receipt.json'
    if ep.exists():
        r=json.loads(ep.read_text()); e['eprint_receipt']={k:r.get(k) for k in ('url','utc','status','sha256','bytes','kind')}
    e.update(disp[str(i)])
    e['accepted_credit']=False
    out[str(i)]=e
assert len(out)==20
(D/'results.json').write_text(json.dumps(out,indent=1,ensure_ascii=False)+'\n')
print({k:v['outcome'] for k,v in out.items()})
