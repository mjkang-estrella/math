from research import *
import xml.etree.ElementTree as E
access=[json.loads(x) for x in (L/'access.jsonl').read_text().splitlines()]
for a in access:
 if 'sha256' in a:assert sha(L/'primary'/a['key'])==a['sha256']
bindings=json.loads((L/'freeze-bindings.json').read_text())
for b in bindings:
 if 'missing' in b:continue
 assert sha(pathlib.Path(b['copy']))==b['sha256']
 if b['kind'].startswith('scientific'):assert sha(pathlib.Path(b['original']))==b['sha256']
provenance=dict(date='2026-10-30',lane=L.name,counts=dict(additional=9,total=39,next=40,authority='root only'),status='PARK; no full endpoint or nomination',guard='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',limits=dict(AS_bytes=512*1024**2,group_RSS_bytes=512*1024**2,CPU_seconds=210,wall_seconds=230,cap_raises=False),environment=dict(OPENBLAS_NUM_THREADS=1,OMP_NUM_THREADS=1,PYTHONDONTWRITEBYTECODE=1),helpers='all executed via designated guard; native bounded reads/apply_patch also used',network='arXiv export API and exact PDF URLs; one irrelevant Bing response; no Google or prohibited host routes',source_discipline='see failures.md; freeze before scientific body extraction; original/copy and body hashes checked before/after; administrative snapshots only; successor-body-first ordering not fully satisfied',unique_controls=dict(nonchain_orders=46,n_range=[2,4],relation_splits=2,fiber_examples=1,earlier_r289_206_controls_recounted=False),external_writes=False,children=False,scientific_full_proof=False,prior_art_clearance=False)
(L/'provenance.json').write_text(json.dumps(provenance,indent=2))
ns={'a':'http://www.w3.org/2005/Atom'};chron=[]
for key in ['shuffle-current','breadth-current','last-current','magnitude-successor','stanleydepth-successor','bunkbed-successor']:
 for e in E.parse(L/'primary'/(key+'.atom')).findall('a:entry',ns):
  row={k:e.findtext('a:'+k,namespaces=ns) for k in ['id','title','published','updated']};row['metadata_source']=key+'.atom';chron.append(row)
(L/'chronology.json').write_text(json.dumps(chron,indent=2))
coverage={'1412.7488v4':[[42,145],[285,340],[425,515]],'1509.08580v3':[[155,170],[435,460],[660,675]],'2503.17580v4':[[30,85],[342,365]],'0908.1582v2':[[145,205]],'1507.02502v2':[[440,465],[1835,1870]],'0811.0949v2':[[56,66],[93,114]],'2410.02545v1':[[25,75],[108,160]],'0712.2308v1':[[20,48]],'1504.04279v3':[[380,425],[470,482]],'1509.07058v4':[[85,103],[171,199]],'2011.11467v1':[[27,56],[390,425]],'math-0408312v2':[[35,42],[90,155]],'cs-0608021v1':[[45,100]],'1008.4707v1':[[100,130],[480,505]],'1210.4605v1':[[25,110]],'1002.4384v2':[[1,110]],'math-9803030v2':[[15,65],[204,235]],'math-0512299v2':[[25,95]],'1107.4875v3':[[1,95]]}
(L/'body-coverage.json').write_text(json.dumps(dict(note='selected bounded passage coverage only, not complete proof audits; extra duplicate probes excluded from eight tally',ranges=coverage),indent=2))
manifest={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
(L/'manifest.json').write_text(json.dumps(manifest,indent=2));print(json.dumps(dict(manifest_files=len(manifest),frozen_bindings=len(bindings),access_records=len(access))))
