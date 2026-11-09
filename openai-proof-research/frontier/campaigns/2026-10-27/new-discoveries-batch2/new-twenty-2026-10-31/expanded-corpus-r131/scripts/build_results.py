import json,pathlib,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
ex=json.loads((D/'extracted.json').read_text()); disp=json.loads((D/'scripts/dispositions.json').read_text())
res=json.loads((D/'reservation.json').read_text()); ids=[str(i) for i in res['ids']]
vers=json.loads((D/'outputs/arxiv-versions.json').read_text())
out={}
for i in ids:
    o=ex[i]; a=o['source_url'].rsplit('/',1)[-1]
    out[i]={'mathdb_id':int(i),'title':o['title'],'canonical_url':o.get('canonical_url'),'source_url':o['source_url'],
            'arxiv_versions':vers.get(a,{}).get('versions'),'arxiv_comments':vers.get(a,{}).get('comments'),
            'provenance':o['provenance'],**disp[i],'self_accepted':False,'credit':'none unless root accepts'}
assert len(out)==20 and set(out)==set(ids)
(D/'results.json').write_text(json.dumps(out,indent=1)+'\n')
man={}
for p in sorted(D.rglob('*')):
    if p.is_file() and p.name!='MANIFEST.json': man[str(p.relative_to(D))]=hashlib.sha256(p.read_bytes()).hexdigest()
(D/'MANIFEST.json').write_text(json.dumps(man,indent=1)+'\n')
print(len(out),'results;',len(man),'files in manifest')
for i in ids: print(i,out[i]['outcome'])
