from work import *
post=[]
for line in (L/'bindings.jsonl').read_text().splitlines():
    r=json.loads(line)
    if r['administrative']:continue
    post.append(dict(original=r['original'],copy=r['copy'],sha256=r['sha256'],original_matches=sha(r['original'])==r['sha256'],copy_matches=sha(r['copy'])==r['sha256']))
assert all(r['original_matches'] and r['copy_matches'] for r in post)
save(L/'source-postcheck.json',post)
acc=[json.loads(l) for l in (L/'access.jsonl').read_text().splitlines()]
for r in acc:
    if 'sha256' in r: assert sha(L/'primary'/r['name'])==r['sha256'],r['name']
derived=[]
for t in sorted((L/'derived').glob('*.txt')):
    p=L/'primary'/(t.stem+'.pdf')
    if p.exists(): derived.append(dict(pdf=str(p.relative_to(L)),pdf_sha256=sha(p),text=str(t.relative_to(L)),text_sha256=sha(t),command='pdftotext -layout'))
save(L/'derived-text-bindings.json',derived)
hc=json.loads((L/'history-coverage.json').read_text())
save(L/'provenance.json',dict(lane=str(L),utc=now(),counts=dict(additional=9,total=39,next=40,root_alone_counts=True),
  primary_source=dict(arxiv='1801.07238v1',sha256=sha(L/'primary/1801.07238v1-refetch.pdf'),published='Period. Math. Hung. 79 (2019) 78-85, doi 10.1007/s10998-018-0263-y'),
  access_records=len(acc),access_errors=[r for r in acc if 'error' in r],scientific_bindings=len(post),derived_texts=len(derived),
  history=dict(mode='876 immutable references from r268 index verified in place by sha256, contents term-screened; no copies',index=hc['index'],index_sha256=hc['index_sha256'],verified=hc['verified'],failed=hc['failed']),
  guard='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',
  caps=dict(AS_MiB=512,groupRSS_MiB=512,CPU_seconds=210,wall_seconds=230,raised=False),
  scope='solo; lane only; no children; no Lean/manuscript/git/shared/public/browser/MathDB changes',
  protocol_deviations='see FAILURES.md (r268 files read before lane freeze)'))
manifest={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['final-manifest.json','verification-receipt.json'] and '__pycache__' not in p.parts}
save(L/'final-manifest.json',manifest)
print('finalized',len(manifest),'files;',len(post),'scientific bindings;',len(derived),'derived texts')
