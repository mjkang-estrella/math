from pathlib import Path
import hashlib,json,shutil,datetime
root=Path('/home/mj-kang/Documents/Dev/math'); batch=root/'openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2'; out=batch/'lanes/sol-bessel-ratio-current-prior-review-r2'
paths=[root/'openai-proof-research/AGENTS.md',root/'openai-proof-research/sources/upstream.json',root/'openai-proof-research/sources/CONTENTS.md',batch/'AGENTS.md',batch/'ledger.json',batch/'prior-campaign-context.json']
for lane,names in {'sol-fresh-source-discovery-r57':['discovery.md','provenance.json','registry-screen.json','http.jsonl','sources/*'],'sol-bessel-ratio-eligibility-review-r1':['review.md','evidence/*','http.jsonl'],'root-bessel-ratio-adjudication-r1':['ADJUDICATION.json'],'sol-bessel-ratio-one-crossing-formal-r1':['SUMMARY.md','formal/Crossing.lean','formal/Transfer.lean','formal/Cases.lean'],'root-polyomino57-acceptance-r1':['ACCEPTANCE-PRIOR-LIMITS.json'],'sol-polyomino57-full-final-review-r1':['live/omega-D5.json']}.items():
 for pat in names: paths+=list((batch/'lanes'/lane).glob(pat))
rows=[]
for src in paths:
 if not src.is_file():continue
 data=src.read_bytes(); h=lambda b:hashlib.sha256(b).hexdigest(); dst=out/'frozen'/src.relative_to(root);dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(data)
 rows.append({'source':str(src),'copy':str(dst),'sha256_before':h(data),'sha256_copy':h(dst.read_bytes()),'sha256_after':h(src.read_bytes())})
(out/'input-freeze.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':rows},indent=2))
print(len(rows), 'frozen files')
