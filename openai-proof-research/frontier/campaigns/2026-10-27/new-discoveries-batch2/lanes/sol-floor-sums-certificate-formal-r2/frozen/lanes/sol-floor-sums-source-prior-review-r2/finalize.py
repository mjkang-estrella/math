from pathlib import Path
import json, hashlib, datetime
L=Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def put(n,x): (L/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
rows=json.loads((L/'original-copy-checks.json').read_text())
for n in ['wong-current.pdf','wong-current.txt','pong11.pdf','pong11.txt']:
    p=L.parent/'sol-floor-sums-breadth-depth-r241/sources'/n
    q=L/'frozen/certificate/frozen/sources'/n
    a=sha(p); assert a==sha(q)==sha(p)
    rows.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=a,original_before=a,original_after_copy=a,copy_after=a,administrative=False,reused_existing_frozen_copy=True))
put('original-copy-checks.json',rows)
requests=[json.loads(x) for x in (L/'retrieval.jsonl').read_text().splitlines()]
for r in requests:
    if 'sha256' in r: assert sha(L/r['path'])==r['sha256']
body_specs=[
('Wong2018','frozen/certificate/frozen/sources/wong-current.pdf','https://cs.uwaterloo.ca/journals/JIS/VOL21/Wong/wong7.pdf','2018-02-23','JIS published version',['1-3','14-19'],'Exact p15 full uniform-m conjecture; Theorem15 weaker; not full Conjecture17','4-13 not independently read in this lane'),
('OnphaengPongsriiam2017','frozen/certificate/frozen/sources/pong11.pdf','https://cs.uwaterloo.ca/journals/JIS/VOL20/Pongsriiam/pong11.pdf','2017-01-14','JIS published version',['1-3','14-20'],'Definition1 multiset; Theorem9 whole proof: general block bound; even-dimensional sharp upper endpoint','4-13 pointwise extrema proofs not independently read here'),
('Tverberg2012','retrieved/tverberg2012.pdf','https://www.impan.pl/shop/publication/transaction/download/product/82787?download.pdf','2012','Acta Arithmetica published version DOI10.4064/aa155-4-1',['349-351'],'Full body; proof n2 nonnegativity; claims only n2,n3 bounds; asks higher-dimensional results','None within three-page body; no separate original Jacobsthal1957 body'),
('Hermite2019','retrieved/hermite2019-primary.pdf','https://www.fq.math.ca/Papers/57-2/pongsriiam02072019.pdf','2019-05','Fibonacci Quarterly published version',['126-133'],'Full body; Theorem3.1 already contains one-subset max formula; Corollary3.4 only n2 nonnegativity','None within article; no inference from formula to sharp n4 bound'),
('Palatsang2021','retrieved/scienceasia2021.pdf','https://www.scienceasia.org/2021.47.n5/scias47_640.pdf','2021','ScienceAsia published version; received2021-02-11 accepted2021-05-09',['640-644'],'Full body; univariate floor progression quadratic identities, not alternating subset prefix extrema','None within article'),
('Phunphayap2022','retrieved/combinatorial2022.pdf','https://files.ele-math.com/articles/jmi-16-95.pdf','2022','JMI published version; received2021-12-14',['1455-1464','1471-1475'],'Definitions; preliminaries; Theorems1-4 proofs; Theorem5 statement; Theorem8 proof; references. Absolute-value f4/f5/f6 and g4, not floor-prefix joint extrema','1465-1470 not independently read; no blanket clearance of higher-dimensional auxiliary proofs')]
bodies=[]
for key,path,url,date,version,pages,scope,limits in body_specs:
    p=L/path;t=p.with_suffix('.txt')
    bodies.append(dict(key=key,url=url,date=date,version=version,pdf_path=path,pdf_sha256=sha(p),text_path=str(t.relative_to(L)),text_sha256=sha(t),actual_body_read=True,read_printed_pages=pages,scope=scope,unread_limits=limits))
citers={}
for n in ['citers','predecessor-citing','tverberg-citers']:
    d=json.loads((L/'retrieved'/n).read_text());citers[n]=dict(indexed_count=d['meta']['count'],returned_count=len(d['results']),entries=[dict(id=x['id'],title=x['title'],date=x['publication_date']) for x in d['results']],exhaustive_worldwide=False)
put('exactcoverage.json',dict(target='For all positive integer m, indexed ai,K in [0,m-1], signed 4-variable floor-prefix S >= -3 floor(m/3)',bodies=bodies,indexed_citers=citers,discovery_only=[r for r in requests if not r['key'].endswith('.pdf')],current_registry='HOLD; inaccessible current head and post-pinned interval; no prohibited-route retry',immutable_registry_screen='registry-fixed-screen.json',missing_concrete=['Current public-registry exact-statement/head content after fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','Carlitz1960, Jacobsthal1957, Carlitz1959, Grimson1974 original bodies','Four other 2017 indexed citing bodies (see predecessor-citing response)','2022 pp1465-1470 auxiliary proofs; any complete joint shifted-G/residue bridge'],no_global_priority_clearance=True))
fail=[r for r in requests if 'error' in r]
fail.extend([dict(kind='source_mismatch',path='retrieved/tverberg-doi',detail='Guessed product89131 returns unrelated Julia-set article; rejected despite HTTP200. Correct DOI-matched82787 PDF separately obtained.'),dict(kind='search_limit',path='retrieved/arxiv-authors',detail='27 returned entries, mostly unrelated Wong papers; noisy query not author census or proof of absence.'),dict(kind='search_limit',path='retrieved/crossref',detail='12 returned entries do not include target; no negative inference.'),dict(kind='native_read_limits',detail='Initial broad file inventory and some combined native displays truncated; no inference of complete source coverage. Relevant scientific passages re-read with bounded output. Initial guessed r241 lane name did not exist; corrected using directory-name discovery.'),dict(kind='parked',detail='Previously denied GitHub API/raw/codeload/diff/patch, ScienceDirect, Google challenge routes and old inaccessible intervals not retried. Current registry HOLD.')])
put('failures.json',fail)
put('provenance.json',dict(created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),lane=str(L),verdicts=dict(SOURCE='PASS',PRIOR='HOLD bounded',SUBSTANTIVE='qualified PASS for continued consideration',recommendation='INVEST; acceptance and priority HOLD'),counts=dict(additional=9,total=39,next=40,changed=False),guard='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',environment=dict(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1'),limits=dict(address_space_bytes=512*1024**2,group_rss_bytes=512*1024**2,cpu_seconds=210,wall_seconds=230),scientific_freeze='original-copy-checks.json',new_primary_freeze='retrieval.jsonl captures hashed HTTP bytes before scientific reading; immutable captured originals, separately hashed pdftotext derivatives',administrative_policy='snapshots only; no live-admin immutability assertion',requests=requests,not_done=['No checker implementation re-review','No active formal-lane reading','No Lean/manuscript/shared/git/public/browser/MathDB edits','No count changes or acceptance','No children'],manifest_excludes=['final-manifest.json','final-verification-receipt.json']))
for row in rows:
    assert sha(L/row['copy'])==row['sha256']
    if not row['administrative']: assert sha(Path(row['original']))==row['sha256']
put('final-manifest.json',{str(p.relative_to(L)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['final-manifest.json','final-verification-receipt.json']})
print('Finalized',len(bodies),'actual bodies; manifest excludes self and receipt')
