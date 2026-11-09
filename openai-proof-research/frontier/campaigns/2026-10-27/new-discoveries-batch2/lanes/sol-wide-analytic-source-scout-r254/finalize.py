from pathlib import Path
import hashlib,json,datetime
l=Path(__file__).resolve().parent
p=l/'SCOUTING.md';t=p.read_text().replace('Frączyk–Hutchcroft–Nachmias,2012.15502v1','Itai Benjamini–Mikołaj Frączyk–Gábor Kun,2012.15502v1');p.write_text(t)
(l/'SUMMARY.md').write_text('''# r254 handback

Proposed complete ordinary proof of Athreya–Mukherjee–Mukherjee2304.01145v2 Conjecture2.4: every fixed1≤s≤r has dependent super-coupon cover expectation asymptotic (r/s)binom(n,s)/binom(r,s) log binom(n,s). PROOF.md gives all analytic bridges; no growing-parameter or Gumbel claim.

Two sustained mechanisms: explicit one-target birth–death hitting recurrence, followed by fixed-dimensional pair-union killed chains. Analytic perturbation and stationary escape flux yield relative logarithmic-time pair tails, giving a second-moment lower bound and summed-tail expectation upper bound. Thirty-two exact rational lump/stationarity/flow cases pass as supporting checks only.

Fifteen distinct attributed source-question families screened, one ranked survivor. The quantization conjecture also closes fully but is explicitly EXCLUDED as routine same-source pair-error adaptation;306 finite exact parameter cases support that comparison. No outcome credit requested.

HOLD for independent proof/source/prior/substantive review. Strongest objection: classical finite-matrix perturbation plus source overlap/second-moment methods may routinely subsume the new assembly. Actual Keller2012 and Abadi–Saussol2010 statements/proof bodies were compared; no claim of a prior explicit matching coupon theorem. Published target version, public-registry heads and full citing coverage remain uncleared under inherited route denials. Lawful live arXiv exact-title/object/rare-event searches are recorded with bounded coverage.

Root alone accepts/counts. Counts9additional/39total/next40 unchanged. Solo, assigned-lane only; no children/git/shared/public/browser/MathDB/Lean/manuscript actions. Final manifest excludes itself and verification receipt; separate guarded verifier follows. See FAILURES.md for unsuccessful history traversal, repaired attribution draft, search noise and coverage gaps.
''')
(l/'progress.json').write_text(json.dumps({'date':'2026-10-30','additional':9,'total':39,'next':40,'screened_families':15,'ranked_survivors':1,'ordinary_math':'PROPOSED_COMPLETE_COUPON_FIXED_PARAMETERS','novelty':'HOLD','substantive':'HOLD_ROUTINE_ADAPTATION_OBJECTION','source':'VERSIONED_PREPRINT_PASS_PUBLISHED_HOLD','formal':'NOT_STARTED_NOT_AUTHORIZED','credit':0,'next_step':'Independent source/proof/subsumption/substantive review of PROOF.md; no additional finite sweeps needed.'},indent=2))
(l/'FAILURES.md').write_text('''# Failures and access/eligibility limits

1. The first expanded history traversal stopped with NotADirectoryError because lanes/ contains a root report file as well as directories. Guard exit1, no scientific result inferred. Corrected screen.py explicitly filters directories and completed1152 role-qualified report references. Failure retained here rather than erased.
2. Initial recursive filename discovery and several tool outputs were truncated. These are not complete read evidence. Bounded subsequent source/body reads supply the statements and proof routes actually used. Early history coverage722 reports preceded source selection; expanded1152-role coverage followed initial retrieval. Neither scans every deeper historical body; inaccessible historical intervals are parked, not cleared.
3. Initial generic arXiv query combining quantization and Gomez returned mostly irrelevant neural/physics results. Exact-title follow-up found source2305.02372v1. Search noise is not negative prior evidence. Rare-event query and exact-title/object searches are finite indexed searches, not citation-complete searches.
4. A draft expander-paper author line incorrectly named a different collaboration. Direct frozen title-page read corrected it to Itai Benjamini, Mikołaj Frączyk and Gábor Kun before final manifest. No mathematical assertion depended on that draft author line.
5. No HTTP403/429/challenge was encountered in this lane's lawful arXiv requests. Inherited denied GitHub API/raw/codeload/diff/patch, ScienceDirect and Google challenge routes were NOT retried. No proxy/TLS-disable/browser bypass. No registry current-head clearance is available. Original older inaccessible bodies are not cleared by newer abstracts.
6. Source statements are versioned preprints, not authenticated published-target correspondence. Original predecessor and current citing bodies for parked breadth entries remain incomplete. Absolute novelty, current universal open status and substantive eligibility are NOT claimed.
7. PROOF.md is solo ordinary mathematics, not independently reviewed, formally replayed or accepted. Classical escape-rate/spectral-perturbation methods and the source's own recurrence/second-moment apparatus create a substantial routine-adaptation objection. No Lean/manuscript work or count action was performed.
8. Helper invocations from stdin were not all saved as executable scripts. Their resulting source bytes, frozen copies, request bindings and reports are preserved; checks.py, screen.py and verify.py are runnable. Re-fetching is neither required nor recommended for artifact verification.
''')
(l/'runnablechecks.md').write_text('''# Runnable bounded checks

Run from repository root with the exact fixed guard:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-wide-analytic-source-scout-r254/checks.py
```

32 exact finite Markov-lump transition, stationary, reversible-flow cases;306 quantization permutations/threshold cases. No random census or numeric spectral limit is a proof premise. Do not run checks after manifest unless prepared to regenerate it; deterministic result bytes are currently bound.

For read-only verification, replace the final script path by this lane's verify.py. All runs retain fixed512MiB address-space/group-RSS,210CPU/230wall caps. No cap raises. Verification compares frozen scientific originals/copies and immutable history references; administrative originals are snapshots only. Verification receipt is excluded from the final manifest.
''')
# bind the two explicitly reopened history bodies as original/copy pairs.
extra=[]
for name in ['sol-fresh-source-discovery-r136','sol-fresh-source-discovery-r154']:
 p=l.parent/name/'discovery.md';d=p.read_bytes();h=hashlib.sha256(d).hexdigest();c=l/'frozen'/(h+'.md');assert c.read_bytes()==d;extra.append({'original':str(p),'copy':str(c),'sha256':h})
(l/'reopened-bindings.json').write_text(json.dumps(extra,indent=2))
queries=[]
for p in (l/'retrieved').glob('*.xml'):
 d=p.read_bytes();h=hashlib.sha256(d).hexdigest();c=l/'frozen'/(h+'.xml');assert c.read_bytes()==d;queries.append({'original':str(p),'copy':str(c),'sha256':h})
(l/'retrieval-bindings.json').write_text(json.dumps(queries,indent=2))
(l/'provenance.json').write_text(json.dumps({'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'primary_bodies':'primarybindings.json','queries':['query-binding.json','query2-binding.json','live-search.json','target-search.json','rare-binding.json'],'chronology':'chronology.json','scientific_freeze':['bindings.json','primarybindings.json','reopened-bindings.json','retrieval-bindings.json'],'immutable_history':['history-bindings.json','expanded-history-bindings.json'],'administrative':'administrative/ snapshots only; no original comparison','guard':'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py','caps':{'address_space_MiB':512,'group_RSS_MiB':512,'CPU_seconds':210,'wall_seconds':230},'thread_env':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},'no_shared_mutations':True,'priority_limit':'No current public proof-registry head, no complete target journal/citer clearance, no absolute worldwide priority claim.'},indent=2))
files={str(p.relative_to(l)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(l.rglob('*')) if p.is_file() and p.name not in ['finalmanifest.json','verification-receipt.json']}
(l/'finalmanifest.json').write_text(json.dumps(files,indent=2));print('MANIFEST',len(files))
