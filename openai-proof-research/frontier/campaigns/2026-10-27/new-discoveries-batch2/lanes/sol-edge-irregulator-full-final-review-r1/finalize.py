from pathlib import Path
import json,hashlib,re,collections,datetime,shutil,zipfile
r=Path(__file__).resolve().parent;b=r.parent.parent;root=b/'lanes/root-edge-irregulator-final-freeze-r1';src=b/'lanes/sol-edge-irregulator-manuscript-packet-r1'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();utc=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
f=json.loads((r/'before.json').read_text())['files']
for n,h in f.items():
 assert sha(src/n)==h,n
 assert sha(r/'input'/n)==h,n
with zipfile.ZipFile(r/'input/edge-irregulator-manuscript-packet.zip') as z:
 assert len(z.namelist())==142; assert not any(n.endswith(('.olean','.ilean','.o','.so','.ir')) for n in z.namelist())
receipt=json.loads((r/'extracted/verification-receipt.json').read_text());assert receipt['declaration_count']==167
assert len(json.loads((r/'extracted/dependency-hashes.json').read_text()))==1132
names=set();counts=collections.Counter()
pat=r'^AUDIT (\S+) (\S+)\nTYPE (.*?)\nAXIOMS \[([^\]]*)\]\nFLAGS unsafe=(\w+) partial=(\w+) axiom=(\w+)$'
rows=re.findall(pat,(r/'extracted/logs/ReadAudit.log').read_text(),re.M|re.S);assert len(rows)==167
for mod,n,typ,axs,u,p,a in rows:
 assert n not in names;names.add(n);counts[mod]+=1
 assert typ and set(re.findall(r'[\w.]+',axs))<={'propext','Classical.choice','Quot.sound'}
 assert (u,p,a)==('false','false','false')
assert names=={d['name'] for d in receipt['declarations']}
for m in receipt['proof_modules']:assert (r/'extracted/logs'/f'{m}.log').stat().st_size==0
(r/'audit-review.json').write_text(json.dumps({'utc':utc(),'readable_and_explicit_name_sets_equal':True,'total':len(names),'per_origin':dict(counts),'readable_audit_sha256':sha(r/'extracted/logs/ReadAudit.log'),'explicit_audit_sha256':sha(r/'extracted/logs/OriginAudit.log'),'module_peak_sampled_rss_kib':max(s['peak_group_rss_kib'] for s in receipt['steps'])},indent=2))
regex=r'irregula|bensmail|catherinot|fioravantes|marcille|oijid|2511[._-]?14514|edge.?delet|neighbor.?degree|locally.?irreg|degree.?conflict|degree.?constrain|diamond|gadget|decompos'
screen={}
for reg in ['omega','openai']:
 lines=(root/(reg+'-tree.txt')).read_text().splitlines();screen[reg]=[x for x in lines if re.search(regex,x,re.I)]
 rows={x.split('\t',1)[1]:x.split('\t',1)[0].split()[2] for x in lines}
 if reg=='omega':
  for p in (r/'fresh-bodies').rglob('*'):
   if p.is_file():
    data=p.read_bytes();name=p.relative_to(r/'fresh-bodies').as_posix();assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==rows[name]
(r/'path-screen.json').write_text(json.dumps({'regex':regex,'coverage':'complete paths; selected bodies only','matches':screen},indent=2))
print('path matches', {k:len(v) for k,v in screen.items()});print('max Lean RSS KiB',max(s['peak_group_rss_kib'] for s in receipt['steps']))
# Preserve exactly the contexts/evidence consulted; no reads of Git caches.
external=[b/'AGENTS.md',b/'NEXT.md',b/'ledger.json',b/'prior-campaign-context.json',b.parents[3]/'AGENTS.md',root/'CURRENT-REGISTRIES.json',root/'review-freeze.json']
prior=b/'lanes/sol-edge-irregulator-preliminary-review-r1';current=b/'lanes/sol-edge-irregulator-current-prior-review-r2'
external += [prior/'review.md',current/'review.md',prior/'frozen/provenance.json',prior/'frozen/http.jsonl',current/'provenance.json',current/'live/http.json',current/'live/publisher-pdf-http.json']
external += [prior/'frozen/sources'/x for x in ['prior-dmtcs','prior-dmtcs.txt','bensmail-ones','bensmail-ones.txt']]
external += [current/'live'/x for x in ['publisher-chapter','arxiv-current','omega-order','omega-response','omega-beluhov','omega-harder','openai-neighbor','openai-378']]
ev=[]
for i,p in enumerate(external):
 if p.is_file():
  dest=r/'consulted'/str(i)/p.name;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest)
  ev.append({'source':str(p.resolve()),'copy':str(dest.relative_to(r)),'sha256':sha(p)})
(r/'after.json').write_text(json.dumps({'utc':utc(),'original_bound_files_verified':145,'private_bound_files_verified':145,'files':f,'archive_entries':142},indent=2))
provenance={'utc':utc(),'role':'solo independent final reviewer; no acceptance/count action','frozen_files':f,'freeze_sha256':sha(root/'review-freeze.json'),'before':sha(r/'before.json'),'after':sha(r/'after.json'),'consulted':ev,'registry_observation':json.loads((root/'CURRENT-REGISTRIES.json').read_text()),'registry_body_checks':json.loads((r/'registry-checks.json').read_text()),'fresh_http':json.loads((r/'http.json').read_text()),'source_urls':{'publisher':'https://doi.org/10.1007/978-981-95-7127-7_24','publisher_pdf':'https://link.springer.com/content/pdf/10.1007/978-981-95-7127-7_24.pdf?pdf=inline%20link','arxiv':'https://arxiv.org/abs/2511.14514','DMTCS':'https://dmtcs.episciences.org/17071/pdf','DMGT':'https://bibliotekanauki.pl/articles/59945820.pdf','omega':'https://github.com/the-omega-institute/trureturing','openai':'https://github.com/openai/math'},'coverage':'publisher definition/conjecture visually; all four candidate pages visually; fourteen mathematical sources; all167 actual declaration types/axioms/flags in independent readable audit; source-only fresh replay; closest DMTCS4.1-4.3/DMGT9,19 bodies; complete dated registry paths/deltas, selected actual bodies only. Not worldwide absence or a new remote-head acquisition.','resource_limits':'Copied current self-supervision; no cap raise; nominal40/45ms sampled monitoring not absolute peak proof; inherited receipt-overwrite/helper-supervision/early supervisor-self-limit omissions retained.','artifacts':{}}
for p in r.rglob('*'):
 if p.is_file() and 'input' not in p.relative_to(r).parts and not p.suffix in ['.olean','.ilean','.o','.ir'] and p.name!='provenance.json':
  provenance['artifacts'][p.relative_to(r).as_posix()]=sha(p)
(r/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
print('All final checks PASS',utc())
