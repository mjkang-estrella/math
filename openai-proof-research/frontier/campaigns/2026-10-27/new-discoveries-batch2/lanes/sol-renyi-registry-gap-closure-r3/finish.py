import close,re,sys,json,collections,hashlib
L=close.L;B=close.B;rows=close.load(L/'bodies.json')
if sys.argv[1]=='read':
 receipts=[]
 for r in rows:
  if r['status']!='ok':continue
  s=(L/r['source']).read_text(errors='replace');lines=s.splitlines()
  sel=[(i+1,x[:900]) for i,x in enumerate(lines) if re.search(r'^#{1,4} |^\*\*(?:Theorem|Definition|Lemma|Proposition)|^theorem |^def |2510[.]09206|\bFu\b.{0,12}\bLi\b|positive.sum|self.convolution',x,re.I)]
  receipts.append(dict(path=r['path'],ref=r['ref'],source=r['source'],sha256=r['read']['sha256'],lines=len(lines),selected=sel[:22],full_text_scanned=True,read_chars=r['read']['semantic_scan_chars'],opaque_candidates=r['read']['opaque_candidates']))
 close.save('semantic-read-receipts.json',receipts)
 for r in receipts:
  if 'baseline-relevant-path' in next(x for x in rows if x['source']==r['source'])['reasons']:
   print(r['path'],r['source']);print('\n'.join(str(x) for x in r['selected'][:5]))
elif sys.argv[1]=='finish':
 intervals=close.load(L/'intervals.json');baseline=close.load(L/'baseline.json');missing=close.load(B/'sol-renyi-threshold-current-prior-review-r2/registry-audit.json')['delta']['missing_patches']
 old=close.load(B/'sol-fresh-source-discovery-r100/sources/registry-delta-0.json')
 assert {c['sha'] for c in old['commits']}=={c['sha'] for r in intervals[:2] for c in r['commits']}
 assert sum(len(r['commits']) for r in intervals[:2])==88
 exact=[]
 for p in missing:
  rr=[r for r in rows if r['path']==p and r['ref']==intervals[-1]['end']]
  # Removed bodies are sourced from the interval base.
  if not rr:rr=[r for r in rows if r['path']==p and r['ref']==intervals[-1]['base']]
  exact.append(dict(path=p,bodies=rr,status='ok' if rr and all(r['status']=='ok' for r in rr) else 'missing'))
 paths={};end=intervals[-1]['end']
 for i,r in enumerate(intervals):
  for f in r['files']:
   paths.setdefault(f['filename'],[]).append(dict(interval=i,status=f['status'],previous_filename=f.get('previous_filename'),sha=f.get('sha'),patch_present='patch' in f))
   if f.get('previous_filename'):paths.setdefault(f['previous_filename'],[]).append(dict(interval=i,status='rename-source',new_filename=f['filename']))
 close.save('changed-path-manifest.json',paths)
 # Reconstruct exact terminal tree by applying each complete interval's statuses to baseline objects.
 tree={}
 with (B/'root-edge-irregulator-final-freeze-r1/omega-tree.txt').open() as f:
  for line in f:
   meta,p=line.rstrip('\n').split('\t',1);tree[p]=meta.split()[-1]
 original=tree.copy()
 for r in intervals:
  for f in r['files']:
   if f['status']=='renamed':tree.pop(f['previous_filename'],None)
   if f['status']=='removed':tree.pop(f['filename'],None)
   else:tree[f['filename']]=f['sha']
 net=[dict(path=p,old=original.get(p),new=tree.get(p),status='removed' if p not in tree else 'added' if p not in original else 'modified') for p in sorted(set(original)|set(tree)) if original.get(p)!=tree.get(p)]
 close.save('net-changed-paths.json',net)
 close.audit('after')
 coverage=dict(utc=close.datetime.datetime.now(close.datetime.timezone.utc).isoformat(),recommendation='CLEAR_BOUNDED',base=intervals[0]['base'],end=end,intervals=[{k:v for k,v in r.items() if k!='files'} for r in intervals],baseline=baseline,missing_patch_required=exact,bodies=rows,net_changed_paths=len(net),changed_path_union=len(paths),commits_total=sum(len(r['commits']) for r in intervals),all_final_comparisons_below300=all(r['file_count']<300 for r in intervals),all_required_missing_bodies_closed=all(r['status']=='ok' for r in exact),all_selected_bodies_closed=all(r['status']=='ok' and r.get('blob_matches') for r in rows),opaque_candidates=sum(len(r.get('read',{}).get('opaque_candidates',[])) for r in rows),remaining_concrete_gap=[],limits='Baseline semantic review bounded to38 selected actual bodies, full delta patches plus missing bodies and contexts; not all baseline proof bodies or worldwide priority. Reconstructed tree derived from complete interval net diffs, not new independent end-tree retrieval.')
 assert coverage['all_required_missing_bodies_closed'] and coverage['all_selected_bodies_closed']
 close.save('exactcoverage.json',coverage)
 files={str(p.relative_to(L)):dict(sha256=close.sha(p),bytes=p.stat().st_size) for p in L.rglob('*') if p.is_file() and p.name!='provenance.json'}
 close.save('provenance.json',dict(utc=coverage['utc'],recommendation='CLEAR_BOUNDED',acceptance=False,credit=0,counts=[8,38],candidate_proof_sha256='ca72b385e83d919fbaa97af4d55f0e7d00e949c01c8c4af07fd93ef30fef977a',candidate_sealed_utc='2026-10-29T20:42:37Z',guard=dict(path=str(B/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),sha256=close.sha(B/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),AS=536870912,groupRSS=536870912,CPU=210,wall=230,nominal_sample_ms=40,BLAS_threads=1),scope='SOLO; assigned lane writes only; no git commands, children, browser, external messages, posts, uploads, accounts, Lean, paper, or bulk source copies.',files=files))
 print(json.dumps({k:coverage[k] for k in ['commits_total','net_changed_paths','changed_path_union','all_required_missing_bodies_closed','all_selected_bodies_closed','opaque_candidates']}))
