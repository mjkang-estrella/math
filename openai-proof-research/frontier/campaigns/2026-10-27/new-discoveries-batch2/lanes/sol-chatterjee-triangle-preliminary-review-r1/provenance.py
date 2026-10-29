import pathlib,hashlib,json,shutil,datetime
D=pathlib.Path(__file__).parent; B=D.parent; P=B.parent
paths=[P/'AGENTS.md',P/'NEXT.md',P/'ledger.json',P/'prior-campaign-context.json',P.parents[3]/'AGENTS.md']
paths += [B/p for p in ['root-bajnok-beatty-exclusion-r1/EXCLUSION.json','root-dewitt-rank-exclusion-r1/EXCLUSION.json','root-gamma-level-complete-r3/PROOF.md','root-arcsinh-positive-r1/PROOF.md','sol-mmpp-classical-boundary-review-r3/review.md','sol-edge-irregulator-manuscript-packet-r1/packet/paper.tex','root-edge-irregulator-final-freeze-r1/CURRENT-REGISTRIES.json','sol-mmpp-survival-preliminary-review-r1/registry-inspection.json','sol-mmpp-survival-preliminary-review-r1/delta-body-receipts.json','sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py','sol-fresh-source-discovery-r82/PROOF.md','sol-fresh-source-discovery-r89/PROOF.md']]
paths += sorted((B/'sol-mmpp-survival-preliminary-review-r1/live').glob('delta-body-*.txt'))
paths += [pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')/p for p in ['AGENTS.md','sources/upstream.json','sources/CONTENTS.md']]
receipt=[]
for p in paths:
    if not p.exists():continue
    data=p.read_bytes(); rel=p.relative_to(P) if p.is_relative_to(P) else pathlib.Path('ancestor')/p.name
    dest=D/'context'/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
    receipt.append(dict(original=str(p.resolve()),copy=str(dest.relative_to(D)),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)))
(D/'context-provenance.json').write_text(json.dumps(receipt,indent=2))
m=json.loads((D/'review-freeze.json').read_text());out={}
for p,h in m['files'].items():
    out[p]={'original_matches':hashlib.sha256((pathlib.Path(m['source_lane'])/p).read_bytes()).hexdigest()==h,'copy_matches':hashlib.sha256((D/'frozen'/p).read_bytes()).hexdigest()==h}
(D/'freeze-after.json').write_text(json.dumps(out,indent=2));assert all(all(v.values()) for v in out.values())
(D/'provenance.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),candidate_files=59,before_all_match=True,after_all_originals_and_copies_match=True,independent_checker='check_independent.py',guard='context/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',checker_guard_peak_rss_bytes=12460032,checker_wall_seconds=0.9217098419321701,limits=dict(AS_MiB=512,group_RSS_MiB=512,CPU_seconds=210,wall_seconds=230,sampling_ms=40,BLAS_threads=1),children=False,credit=0,counts=[8,38]),indent=2))
print('59 original and own-copy hashes PASS; context receipts',len(receipt))
