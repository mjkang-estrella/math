from pathlib import Path
import json,hashlib,datetime,shutil
L=Path(__file__).resolve().parent;B=L.parent.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(n,o):(L/n).write_text(json.dumps(o,indent=2)+'\n')
freeze=json.loads((L/'freeze-before.json').read_text())
records=freeze['files']
after=[]
for r in records:
 a=sha(Path(r['original']));b=sha(L/r['copy']);assert a==b==r['sha256']
 after.append(dict(original=r['original'],copy=r['copy'],expected=r['sha256'],original_after=a,copy_after=b,pass_check=True))
dump('freeze-after.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':after})
# Preserve initial ambiguous-name record; correct snapshot names without touching originals.
shutil.copyfile(L/'administrative-snapshots.json',L/'administrative-initial-records.json')
admin=[]
for p,n in [(B/'AGENTS.md','batch-AGENTS.md'),(B.parents[3]/'AGENTS.md','ancestor-AGENTS.md'),(B/'ledger.json','ledger.json'),(B/'prior-campaign-context.json','prior-campaign-context.json')]:
 q=L/'administrative'/n
 if n.endswith('AGENTS.md'):shutil.copyfile(p,q)
 admin.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=sha(q),snapshot_only=True))
dump('administrative-snapshots.json',admin)
prior=next(r for r in records if r['original'].endswith('sol-polynomial-basins-preliminary-review-r1/provenance.json'))
old=json.loads((L/prior['copy']).read_text())
coverage=[]
scopes={
 '1301.0517':'Complete 2-page precursor body, unnumbered question p2 and trap examples',
 '1505.03237':'Complete 5-page body, Definitions2/3, Theorems1/5/7/9 and proofs, Q12 p5; final 2018 body unread',
 'borisov3':'Journal Q10 p4 and surrounding NIL discussion pp4-5, Theorem6/8 identified and candidate comparison; preliminary review supplies full-body coverage',
 '1101.3482':'Introduction/preparations and Proposition3.1 statement and proof pp1-4, later results unread',
 '0707.1837':'Introduction and Theorems1.1/1.2 material pp1-3; preliminary Cor1.3 coverage reused as attributed comparison; later proofs unread'}
for s in old['sources']:
 t=dict(s);t['body_coverage']=next(v for k,v in scopes.items() if k in s['url']);t['reuse']='Existing immutable PDF and extracts; no reacquisition'
 t['local_pdf']=next(r['copy'] for r in records if r['sha256']==s['sha256'])
 t['local_text']=next(r['copy'] for r in records if r['sha256']==s['text_sha256'])
 coverage.append(t)
newscopes={
 'kps':('1999-11-14 v1','Introduction pp2-3, Theorem1; proof construction pp39-40 (initial displayed part); incidental bounded read pp44-46. Full proof dependencies and remaining body unread.'),
 'iterated-identities':('Body dated 2018-09-14, v2; first submission 2017-10-11','Introduction/problem/Theorem1 pp1-3; Theorem3/Cor3.1 pp7-8. Other proofs unread.'),
 'nilpotent-polynomials':('2024-06-23 v3; first-submission date not independently checked','pp1-4 definitions/introduction/main statements and references; later proofs unread.'),
 'locally-nilpotent':('2023-09-19 v1; older overlapping submission 2022-11-12 metadata only','pp1-6 introduction/definitions/Fact1.1/CRS Lemma3.2 proof; Theorem4.1 and proof pp6-8; Theorem5.1 and first proof cases pp10-11; Theorem5.3 and first proof p13; section6/references pp15-17. Remaining classifications proofs and primary cited local-global proof unread.')}
retrieval=[]
for n in ['retrieval.json','retrieval2.json','retrieval3.json','retrieval4.json','retrieval5.json']:
 for r in json.loads((L/n).read_text()):
  retrieval.append(r)
  if r['name'] in newscopes:
   date,scope=newscopes[r['name']];coverage.append(dict(r,date=date,body_coverage=scope,metadata_only=False))
dump('exactcoverage.json',{'sources':coverage,'metadata_only':[r for r in retrieval if 'text' not in r], 'explicit_gaps':['2018 geometric journal final body','2211.06760v3 and final INTEGERS24 A13','Benedetto et al. Periods of rational maps modulo primes Theorem5 primary proof','Corrales-Rodriganez-Schoof support problem primary theorem','current public proof registries and inaccessible historical intervals'], 'citation_warning':'OpenAlex returned one citer but primary Sengupta bodies cite Borisov too: affirmative index incompleteness; no citation closure or absence claim.'})
guard= L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
dump('provenance.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'recommendation':'EXCLUDE for substantive routine-adaptation criterion; root judgment required','printed_priority':'unresolved bounded coverage; no located full same-object printed theorem asserted','counts_unchanged':[9,39,40], 'guard':str(guard),'guard_sha256':sha(guard),'limits':{'address_space_bytes':512*1024*1024,'group_rss_bytes':512*1024*1024,'cpu_seconds':210,'wall_seconds':230},'environment':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},'source_coverage':'exactcoverage.json','freeze_before':'freeze-before.json','freeze_after':'freeze-after.json','administrative':'administrative-snapshots.json','failures':'failures.md','retrieval_receipts':['retrieval.json','retrieval2.json','retrieval3.json','retrieval4.json','retrieval5.json'],'scientific_originals_modified':False,'root_only_accepts':True,'children':0})
files={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['final-manifest.json','verification-receipt.json']}
dump('final-manifest.json',{'algorithm':'sha256','excluded':['final-manifest.json','verification-receipt.json'],'files':files})
print('Finalized',len(files),'files;',len(coverage),'primary source records; originals/copies all unchanged')
