from work import *
# Correct the normalization explicitly rather than conflate the two source conventions.
p=L/'SCOUTING.md';s=p.read_text();s=s.replace('Berg–Szwarc1509.06540v2 §1, Valent type question for indeterminate polynomial birth–death rates degree p≥3, leading coefficients1 and coefficient gap1<C−D<p−1: type equals p∫_0^1(1−x^p)^(−2/p)dx.','Berg–Szwarc1509.06540v2 p4 Eq11, Valent type question: integer p≥3, λ_n=∏_(i=1)^p(pn+e_i), μ_n=∏_(i=1)^p(pn+d_i), 0<e1≤…≤ep, −p<d1≤…≤dp, ∏d_i=0 and1<(Σe_i−Σd_i)/p<p−1; type at order1/p equals ∫_0^1(1−x^p)^(−2/p)dx.').replace('gives the exact alternating weak/strict multizeta asymptotic and hence the type.','gives the exact alternating weak/strict multizeta asymptotic and hence the type. Its rates have leading coefficient1; dividing the original rates by p^p multiplies type by p at order1/p, explaining its p-times-integral convention.').replace('sup_i Uᵀ(∂A/∂x_i)U','sup_i ||Uᵀ(∂A/∂x_i)U||')
p.write_text(s)
freeze(L/'primary/older.xml')
post=[]
for line in (L/'bindings.jsonl').read_text().splitlines():
 r=json.loads(line)
 if r['administrative']:continue
 a=sha(pathlib.Path(r['original']));b=sha(pathlib.Path(r['copy']))
 post.append(dict(original=r['original'],copy=r['copy'],sha256=r['sha256'],original_matches=a==r['sha256'],copy_matches=b==r['sha256']))
assert all(r['original_matches'] and r['copy_matches'] for r in post)
save(L/'source-postcheck.json',post)
derived=[]
for p in (L/'primary').glob('*.pdf'):
 t=L/'science'/(p.stem+'.txt');assert t.exists()
 derived.append(dict(pdf=str(p.relative_to(L)),pdf_sha256=sha(p),text=str(t.relative_to(L)),text_sha256=sha(t),command='pdftotext -layout frozen-pdf derived-text; run through prescribed helper_guard'))
save(L/'derived-text-bindings.json',derived)
save(L/'provenance.json',dict(lane=str(L),utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),counts=dict(additional=9,total=39,next=40,root_alone_counts=True),sources=len(derived),scientific_bindings=len(post),history_references=876,history_mode='verified immutable references in place; no recursive copies',guard='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',caps=dict(AS_MiB=512,groupRSS_MiB=512,CPU_seconds=210,wall_seconds=230),registry_status='inherited denied routes parked; current heads not obtained',protocol_deviations='See FAILURES.md: initial upstream catalogue and first metadata read preceded lane freeze',scope='solo; lane only; no Lean/manuscript/git/shared/public/browser/MathDB changes'))
manifest={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['final-manifest.json','verification-receipt.json']}
save(L/'final-manifest.json',manifest)
print('Finalized',len(manifest),'files;',len(derived),'PDFs')
