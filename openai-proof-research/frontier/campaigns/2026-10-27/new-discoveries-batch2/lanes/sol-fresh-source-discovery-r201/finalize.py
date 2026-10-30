from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def sha(b): return hashlib.sha256(b).hexdigest()
def save(n,x): (L/n).write_text(json.dumps(x,indent=2)+'\n')
utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
records=json.loads((L/'history-receipt.json').read_text())['records']
changes=[];missing=[]
for x in records:
    p=Path(x['original']); c=L/x['copy']
    assert sha(c.read_bytes())==x['sha256']
    if not p.exists(): missing.append(str(p));continue
    b=p.read_bytes()
    if sha(b)!=x['sha256']:
        n='report-refresh/'+str(p.relative_to(L.parents[5])); q=L/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
        changes.append(dict(original=str(p),old_copy=x['copy'],old_sha256=x['sha256'],new_copy=n,new_sha256=sha(b)))
save('active-refresh.json',dict(utc=utc,changes=changes,missing=missing,scope='Point-in-time snapshots, never immutable scientific originals. Old bytes retained.'))
# Preserve previous r199 point-in-time versions for changed direct reports where available.
old=[]
previous=L.parent/'sol-fresh-source-discovery-r199'
for x in json.loads((previous/'history-receipt.json').read_text())['records']:
    matches=[a for a in records if a['original']==x['original'] and a['sha256']!=x['sha256']]
    if matches:
        p=previous/x['copy'];b=p.read_bytes();assert sha(b)==x['sha256']
        n='predecessor-snapshots/'+x['copy'];q=L/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
        old.append(dict(original=x['original'],previous_snapshot=str(p),copy=n,sha256=sha(b),current_snapshot_sha256=matches[0]['sha256']))
save('predecessor-versions.json',old)
primary=json.loads((L/'primary-freeze.json').read_text())
old_freeze=L/'scientific-freeze.json'
if old_freeze.exists() and not (L/'report-snapshot-freeze.json').exists():
    (L/'report-snapshot-freeze.json').write_bytes(old_freeze.read_bytes())
save('scientific-freeze.json',dict(scope='Only downloaded primary source originals/copies; administrative and mutable reports excluded.',files=primary))
for x in primary: assert sha(Path(x['original']).read_bytes())==sha((L/x['copy']).read_bytes())==x['sha256']
save('initial-original-copy-verification.json',dict(utc=utc,primary_files=len(primary),status='PASS; freeze preceded first extraction and mathematical body reading'))
http=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]
save('sources-receipt.json',dict(utc=utc,requests=http,primary_body_reads={'gauss.pdf':'Sections 2,7,8.6–8.7,9; full statement and obstruction proofs','suto.pdf':'Sections 1–2 actual comparison and proofs','korn.pdf':'Introduction, definitions, Theorem 1.3, p4 conjecture','korn-new.pdf':'Theorems 1.1/1.3, second-inequality proof and domain comparison','singular.pdf':'Introduction and main theorem context'},unused=['zonoid.pdf']))
save('coverage-receipt.json',dict(utc=utc,qualified_original_reports=len(records),legacy_indexes=[193,194,197,199],r111_113_retained=all(any('sol-fresh-source-discovery-r'+str(r)+'/' in x['original'] for x in records) for r in [111,112,113]),qualification='r195 corrected qualified originals plus r198 original bindings and direct original lane reports. Legacy copied aliases retained as indexes only; no recursive promotion or equal-byte provenance inference.',limits='Not all history. Current complete public registry/head unavailable; parked intervals closed; active reports and administrative files are snapshots.'))
save('failure-receipt.json',dict(utc=utc,failed_commands=['bs4 import ModuleNotFoundError','initial exact Matrix.rank MemoryError'],initial_rank_guard=dict(exit=1,peak_rss=299237376,wall_seconds=33.6567056189524),corrected_rank_guard=dict(exit=0,peak_rss=58404864,wall_seconds=0.48101950203999877),denied_routes_attempted=[],closed_routes=['GitHub API/raw/codeload/diff/patch','ScienceDirect','Google challenge'],caps=dict(AS_RSS_MiB=512,CPU_seconds=210,wall_seconds=230),policy='No caps raised; failures preserved; no retry/bypass.'))
chron={}
for n in ['gauss','suto','korn','korn-new','singular']:
    import re,html
    s=html.unescape(re.sub('<[^>]*>',' ',(L/'sources'/f'{n}-abs.html').read_text()));s=re.sub(r'\s+',' ',s);i=s.find('Submission history');j=s.find('Full-text links:',i);chron[n]=s[i:j]
save('chronology.json',dict(utc=utc,submission_histories=chron,limits='PDF internal dates can differ from arXiv submitted dates; no publisher-version byte equivalence or worldwide priority certified.'))
save('provenance.json',dict(utc=utc,lane=str(L),status='UNRESOLVED; zero ordinary nominations',counts=dict(additional=9,total=39,next=40),scientific_inputs=primary,report_history='history-receipt.json',report_status='All research reports are point-in-time snapshots; administrative NEXT/ledger/prior context snapshots not scientific inputs.',legacy_indexes='indexes/',access='sources-receipt.json',coverage='coverage-receipt.json',chronology='chronology.json',failures='failure-receipt.json',manifest_exclusions=['finalmanifest.json','verification-receipt.json'],guard='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'))
exclusions={'finalmanifest.json','verification-receipt.json'}
save('finalmanifest.json',dict(utc=utc,explicit_exclusions=sorted(exclusions),files=[dict(path=str(p.relative_to(L)),bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in exclusions]))
print('final writes complete',len(primary),'primary',len(records),'report snapshots',len(changes),'live changes',len(old),'retained predecessor versions')
