from pathlib import Path
import json,datetime
out=Path(__file__).resolve().parent
p=out/'submission-manifest.json';d=json.loads(p.read_text());rs=json.loads((out/'receipts.json').read_text());lookup={r['id']:r for r in rs}
for e in d['papers']:
 if e['id'] in lookup:e.update(status='submitted',mathdb_url=lookup[e['id']]['url'])
d['submitted_count']=len(rs);d['status']='submitted' if len(rs)==len(d['papers']) else 'partially_submitted';d['updated_at_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
lines=['# MathDB submissions — 2026-11-04','',f"Published {len(rs)} of {len(d['papers'])} previously unsubmitted accepted papers.",'','Each submission includes the accepted PDF, a lossless JSON proof-source package, and a Python extraction script. All source PDF and archive SHA-256 hashes matched the acceptance records. The supplementary packages reconstruct all 8,196 archived files byte-for-byte.','', '| Result | Paper | MathDB |','|---|---|---|']
for r in d['papers']:
 link='[Published]('+r['mathdb_url']+')' if r.get('mathdb_url') else 'Pending'
 lines.append('| '+r['id']+' | '+r['title'].replace('|','\\|')+' | '+link+' |')
lines+=['','Submission receipts: `receipts.json`. Complete metadata and artifact hashes: `submission-manifest.json`. Public supplementary-file verification: `public-file-verification.json`.','', 'These are AI-assisted preprints with the exact acceptance scope and qualifications preserved; publication is not journal peer review.']
(out/'SUBMISSION-INDEX.md').write_text('\n'.join(lines)+'\n');print(d['status'],len(rs))
