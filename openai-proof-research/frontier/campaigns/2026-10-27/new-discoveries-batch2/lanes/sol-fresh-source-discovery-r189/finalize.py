import json,hashlib,datetime,subprocess,sys
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5]
G=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
mode=sys.argv[1]
if mode=='prepare':
 p=subprocess.run(['python',str(L/'checks.py')],capture_output=True,text=True)
 (L/'checks-final.stderr').write_text(p.stderr);assert p.returncode==0
 old=(L/'checks.json').read_text()
 if not (L/'checks-initial.json').exists():(L/'checks-initial.json').write_text(old)
 (L/'checks.json').write_text(p.stdout)
 p2=subprocess.run(['python',str(L/'checks.py')],capture_output=True,text=True)
 assert p2.returncode==0 and p2.stdout==p.stdout
 save('replay-receipt.json',dict(utc=now(),returncode=0,identical=True,sha256=sha(p.stdout.encode()),no_finite_proof_premise=True))
 pairs=json.loads((L/'primary-copy-provenance.json').read_text())
 used={a for a,c,h,z in pairs}
 for p in (L/'sources').iterdir():
  a=str(p.relative_to(L))
  if a not in used:
   b=p.read_bytes();c='primary-copies/'+p.name;(L/c).write_bytes(b);pairs.append([a,c,sha(b),len(b)])
 save('primary-copy-provenance.json',pairs)
 save('primary-hashes.json',[[str(p.relative_to(L)),sha(p.read_bytes()),p.stat().st_size] for p in sorted((L/'sources').iterdir())])
 save('guard-binding.json',dict(path=str(G),sha256=sha(G.read_bytes()),AS_MiB=512,RSS_MiB=512,CPU_seconds=210,wall_seconds=230,unchanged=True,environment={'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'}))
 hist=json.loads((L/'history-receipt.json').read_text());changes=[]
 for path,h,z in hist['changed']:
  row=next(r for r in json.loads((L/'original-copy-provenance.json').read_text()) if r[0]==path)
  changes.append(dict(path=path,sha256=h,text=(L/row[1]).read_text()))
 save('changed-records-read.json',changes)
 save('search-receipt.json',dict(utc=now(),native_search_deviation='Native web search was used for discovery after Bing RSS returned irrelevant successful bodies; it was not passed through helper_guard. Disclosed as a workflow deviation, no browser. All primary-body HTTP, extraction, edits except allowed apply_patch, and hashes subsequently guarded.',queries=['arxiv conjecture integer-valued polynomials','arxiv algebra open question irreducibility 2025','Guo 2003.12653 conjecture proof','integer-valued Conjecture 4.1 Guo','On a conjecture related to integer-valued polynomials journal','On the divisibility of sums involving powers of multi-variable Schmidt polynomials arxiv','Guo integer-valued 2023 conjecture double factorial','Guo 453 conjecture integer-valued proof','Guo (2l-1)!! conjecture','Guo integer-valued polynomials Conjecture 2 proof','2003.12653 exclusions'],primary_hits=['https://bulletin.ssmr.ro/pdf/66-4/articol_8.pdf','https://bulletin.ssmr.ro/volumes/66-4/node9.html','https://arxiv.org/abs/1412.5734','https://arxiv.org/abs/2608.13242','https://lean.up.railway.app/'],limits='Search results are discovery pointers only. Actual guarded retrieved bodies support the mathematical assertions. No exhaustive public/historical clearance; all denied routes remain held.'))
 save('provenance.json',dict(utc=now(),lane=str(L),status='Full ordinary proof candidate; strongest complete classical-adaptation objection for root',counts={'additional':9,'total':39,'next':40,'credit':0},target={'author':'Victor J. W. Guo','title':'On a conjecture related to integer-valued polynomials','journal':'Bull. Math. Soc. Sci. Math. Roumanie 66(114)(4)(2023)449-453','statement':'Conjecture2 equation4.1 p452','arxiv':'2003.12653v1','arxiv_utc':'2020-03-23T10:55:17Z','received':'2022-04-08','accepted':'2022-05-12','doi':'Not authenticated; no DOI asserted'},full_scope='all positive l,n and 0<=k<n',proof='PROOF.md; independent review pending',closest_proof='Chen–Guo1412.5734v1 Sections2-4; journal IJNT14(2018)365-370 DOI10.1142/S1793042118500240; published author body404 so journal comparison remains unread',history={'records':len(hist['records']),'changed':len(hist['changed']),'missing':hist['missing'],'r111_113_retained':True},primary_bodies='sources/, http.jsonl and primary-hashes.json',freeze='scientific-freeze.json',limits=['No global priority certification','No authenticated GitHub current heads or missing history clearance','Current catalog search is bounded, not full-body exclusion','Substantive eligibility may fail by complete source/classical adaptation'],children=False,git=False,browser=False,external_messages_posts_uploads=False,MathDB_edits=False,Lean=False,manuscript=False,workflow_deviations='FAILURES.md'))
 print((L/'checks.json').read_text())
elif mode=='freeze':
 excluded={'scientific-freeze.json','scientific-verification.json','finalmanifest.json','manifest-verification.json','context-NEXT.md','context-ledger.json','context-prior-campaign-context.json'}
 files={str(p.relative_to(L)):sha(p.read_bytes()) for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in excluded}
 save('scientific-freeze.json',dict(utc=now(),files=files,exclusions=sorted(excluded),administrative_policy='NEXT/ledger/prior context are immutable local snapshots only; their live originals are never scientific bindings.'))
elif mode=='manifest':
 excluded={'finalmanifest.json','manifest-verification.json'}
 save('finalmanifest.json',dict(utc=now(),files={str(p.relative_to(L)):sha(p.read_bytes()) for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in excluded},explicit_exclusions=sorted(excluded)))
