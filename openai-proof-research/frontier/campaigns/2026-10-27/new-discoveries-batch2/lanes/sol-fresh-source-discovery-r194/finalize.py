from pathlib import Path
import json,hashlib,datetime,subprocess,re
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
def put(n,s):(L/n).write_text(s.strip()+'\n')
h=json.loads((L/'history-receipt.json').read_text());f=json.loads((L/'scientific-input-freeze.json').read_text())
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
save('guard-binding.json',dict(path=str(guard),sha256=sha(guard.read_bytes()),AS_MiB=512,RSS_MiB=512,CPU_seconds=210,wall_seconds=230,caps_raised=False,limit='40ms sampled RSS; unsampled transients not ruled out'))
save('primary-hashes.json',[dict(file=str(p.relative_to(L)),bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in sorted((L/'sources').iterdir())])
save('chronology.json',dict(retrieval_utc='2026-10-30T04:58:28Z through 05:00:21Z; exact events in http.jsonl/search.jsonl',matrix=dict(arxiv='2610.37150v1',submitted='2026-10-27T12:49:21Z',journal_listed=False,versions_seen=['v1'],source='Conjecture1.1 p1; Theorem1.2 even size; Remark3.1 p4'),divisor=dict(arxiv='2610.37512v1',submitted='2026-10-27T16:35:43Z',journal_listed=False,versions_seen=['v1']),valuation=dict(arxiv='2610.37356v1',submitted='2026-10-27T14:55:02Z',internal_pdf_date='2026-10-28',journal_listed=False,versions_seen=['v1']),closest_published=dict(title='The commuting graph of the ring M3(Fq)',authors='H. R. Dorbidi and R. Manaviyat',doi='10.1080/03081087.2022.2149690',journal='Linear and Multilinear Algebra72(1)(2024)25–30',limit='Bibliography-reported; actual body403 unread, online date not authenticated'),original2004=dict(doi='10.1016/j.laa.2004.05.001',title='On commuting graphs of semisimple rings',body='Unread; ScienceDirect route inherited denied, not requested')))
put('SUMMARY.md', '''# r194 — matrix-ring recognition unresolved; zero nominations

Sustained one fresh full-scope algebraic target: for every finite field F and
integer m>=2, does Gamma(R) isomorphic to Gamma(M_m(F)), for a ring R with
identity, force R isomorphic to M_m(F)? Latest actual primary body
Shahverdi–Shahverdi arXiv:2610.37150v1 retains this as Conjecture1.1 and proves
the even-size case. Those public cases receive no credit. No all-size proof
or refutation was obtained. No PROOF.md, Lean or manuscript.

The strongest available classical bridge is the source's conditional
prime-size-to-multiple transfer. It does not close odd prime bases. Exact
ring controls demonstrate why order/center data and commutative centralizer
graphs alone do not close the gap. The missing universal recognition step,
precise hypotheses and method falsifiers are in discovery.md.

Refreshed 2,564 qualified historical record paths, nine changed/new, zero
missing; these are not 2,564 unique investigations. Inherited aliases and
r111–113 originals retained, bound to original bytes. Coprime-divisor
matching and Fibonacci valuation-tree questions were rejected by actual
public proof bodies as reconnaissance, not fresh target slots.

Current registry catalog and pinned metadata screens have no matching alias;
current complete registry bodies/heads and parked history remain incomplete.
Closest2024 published proof body403 unread, so no literature clearance.
Exact UTC, URLs, primary bytes/hashes/chronology, capped runnable checks,
scientific input/copy freeze and separate final manifest verification retained.
Counts unchanged:9 additional/39 total,next40; root alone accepts/counts/stages.
''')
put('discovery.md', '''# Exact target and source boundary

For every finite field F, every integer m>=2 and every ring R with identity,
if the simple graphs Gamma(R) and Gamma(M_m(F)) are isomorphic, must the rings
be isomorphic? Gamma has vertices R minus its center; distinct vertices are
adjacent iff they commute. No assumed finiteness, F-algebra structure,
semisimplicity or field center is added to R. This is the literal full
Conjecture1.1 on p1 of Hamid and Vahid Shahverdi, arXiv:2610.37150v1.
The complete four-page body, including centralizer/normalizer proofs and
radical/double-centralizer argument, was read. Latest abs lists v1 only,
27Oct2026 12:49:21UTC, no journal reference. Original2004 attribution is
reported by this primary, not independently authenticated from that body.

Public Theorem1.2 settles every even m. Remark3.1 already gives conditional
transfer from any prime size to its multiples. Its bibliography reports
Dorbidi–Manaviyat2024 settles m3 assuming Z(R) is a field. The actual2024
publisher full/PDF routes returned403 and are unread. No claim that its
proof has been inspected or that it is the latest worldwide result. Search
RSS results were irrelevant and provide no clearance. This material body
gap remains HOLD; no proxies, browser, TLS weakening or denied GitHub route.

# Strongest complete available classical-adaptation bridge

The following is a conditional source adaptation, not a new nominee.
Assume recognition holds for size k>=2 over EVERY finite field; put m=kn,
n>1. Also use the order/center determination theorem cited by the source:
|R|=q^(m²), |Z(R)|=q. These cited upstream results are dependencies, not
independently reproved here. A companion block Q of an irreducible polynomial
of degree n repeated k times has matrix centralizer M_k(F_(q^n)). A graph
isomorphism transfers its noncentral closed-neighborhood centralizer graph;
by the assumed recognition its counterpart C in R is that simple ring.
Its field center contains Z(R); hence Z(R) is a finite domain, thus F_q.

Let J=J(R). C intersect J=0: it is a proper ideal of simple C since1 notin J.
If u in1+J normalizes C, then ucu^-1-c is in C intersect J for all c in C,
so u centralizes C, hence the defining element x of C=C_R(x). Thus u in C
and u-1 in C intersect J, forcing u=1. The action on all such centralizers
is free. The corresponding matrix centralizers are one conjugacy orbit
with normalizer GL_k(q^n) semidirect Gal(F_(q^n)/F_q). Therefore |J| divides
|GL_(kn)(q)|/(n |GL_k(q^n)|). If q=p^ell, its p-valuation is
ell*k²*n*(n-1)/2-v_p(n); hence dim_F J < m²/2.

The commutator map j -> jx-xj on J has zero kernel and is bijective. It
follows by subtracting a suitable j that the image of C is exactly
C_(R/J)(xbar). A product decomposition of the semisimple quotient would
split this simple centralizer into nonzero factors, so S=R/J is simple.
Let d=[Z(S):F_q]. Its center lies in Z(C), so d divides n. The double
centralizer theorem applied to the simple subalgebra C in S over Z(S),
and the fact that C_S(C)=Z(C) (an element commuting with C commutes with
xbar and so lies in C), give dim_F S=m²/d. Thus
dim_F J=m²(1-1/d). For d>=2 this contradicts the strict half-dimension
bound, so d=1,J=0 and R=M_m(F_q) by finite simple ring classification.
All this is the complete source mechanism, with k replacing2. By strong
induction, recognition at every prime size implies all sizes. It does not
prove a single missing odd prime base and supplies no substantive exclusion
of the FULL target. No exclusion by shortness is made.

# Missing universal lemma and attempts to falsify methods

The remaining prime-base recognition must recover enough ring structure
from a graph to force semisimplicity and the correct field center at odd
prime size. Merely choosing an irreducible degree-m matrix centralizer gives
a commutative field on the matrix side, whose own commuting graph is empty.
Its transferred graph proves commutativity only. Even supplementing order
does not prove a field: F4 and F2[epsilon]/(epsilon²) both have order4 and
empty graphs under the same noncentral-vertex convention. A local ring
isomorphism cannot be assumed from the graph. Consequently the source's
simple-centralizer argument cannot just take k=1.

A second concrete method falsifier has the same global order and center
order as M3(F2). Let T consist of triples (a,B,U) with a in F2 and B,U in
M2(F2), multiplication (a,B,U)(c,D,V)=(ac,BD,aV+UD). This is a triangular
bimodule ring; associativity follows from matrix associativity and the
commuting left scalar/right matrix actions. Identity is(1,I,0).
J={(0,0,U)} has order16, square zero, and quotient F2 x M2(F2) semisimple,
so it is exactly the Jacobson radical. Commuting with all(0,0,V) forces
B=aI, while commuting with all(c,D,0) forces U=0. Thus its center has
order2 and |T|=512, matching M3(F2), but it is not simple.

Exact exhaustive centralizer counts distinguish the graphs: M3(F2) has
degree histogram {5:412,29:98}; T has {5:160,13:216,29:116,125:18}.
Thus T is NOT a counterexample to the conjecture. It defeats only the
shortcut using order/center as sufficient recognition data. There are no
positive prime-size reconstruction results inferred from this check.

A plausible universal direction is a reconstruction theorem using the
entire nested centralizer/intersection poset, not just sizes or individual
commutative centralizer graphs, to force the odd prime bases. The exact
missing lemma is that this graph data for M_p(F_q), p odd prime, excludes
all nonzero Jacobson radicals and forces its ring center to be a field.
No proof of that lemma or full counterexample is supplied. For m3 the
published field-center result would then apply, subject to body verification;
for larger odd primes additional simple-ring recognition remains necessary.
This is a universal research route with explicit gaps, not a nominee.

# Broad reconnaissance, prior art and chronology limits

Three live recent lists math.NT, math.RA, math.AC were read. Early exact
title/arXiv/author screens preceded investment. Alekseyev2610.37512v1
Theorems1.1–1.3, Vandermonde construction and partition proofs already
resolve McNew–Pomerance strong matchability and divisor questions.
Florez–Higuita-Diaz–Ramirez2610.37356v1 Proposition3.1/Section3.1 and
lifting formulas already refute the Givens–Moll even-branch simplicity
question at p971,a194: e388=971*488 mod971² and delta=0 make the entire
root terminal. Both are public resolutions and were never fresh slots.
Their arXiv histories and exact bodies are frozen; AI-use disclosures in
these papers and the matrix source do not substitute for validation.

The 2,564-record qualified history union preserves all inherited r111–113
paths, even inherited aliases; raw r191 10,196 copied paths were not used.
Only original-to-copy bindings justify retained coverage. Nine changed/new
records were refreshed, copied and recorded with full text. Neighboring
commuting-graph energy/Zagreb work is a different statement, not an alias
of ring recognition. No content-hash-only deduplication or claim of unique
investigation count. Current successful registry catalog was refreshed;
exact matrix aliases absent there and in pinned OpenAI contents/tree metadata.
This is NOT a current full public proof-tree/history audit. GitHub routes,
ScienceDirect, Google challenge routes and earlier parked intervals remain
unrequested/HOLD. No worldwide novelty or priority certification.
''')
put('FAILURES.md', '''# Failures, protocol deviations and limits retained

Initial pwd/rg read-only inventory was outside helper_guard. The next
read-only ancestor/guard cat loop was also outside it. Native bounded reads
were allowed, but the shell inventory was a helper-command deviation. No
write or network request occurred in those commands. Subsequent helper,
Python, retrieval, edit, hash and check commands used the designated guard;
native apply_patch was separately authorized. Fixed caps were not raised.

PDF extraction emitted font mismatch warnings; authoritative primary bytes
and extracted text retained. Source PDFs were first extracted/read directly
in sources before dedicated primary-copies were made. The retrieval receipt
hashes bind those original bytes and the later paired freeze verifies them,
but this does not retroactively establish a pre-read copy receipt. Assigned
historical science had original/copy bindings from initialization onward.

Closest2024 Taylor full route403 was followed by a queued distinct PDF
route, also403. This was not a new author/institutional route and should
have been stopped after the full-route403. Both bodies/hashes/errors are
preserved, no further Taylor request or bypass made. No denied historical
GitHub/API/raw/codeload/diff/patch, ScienceDirect, Google, Crossref/export429,
DBLP-challenge,2014 graph403 or other inherited parked route requested.

Three guarded Bing RSS queries returned irrelevant stopwatch/Nintendo/
YouTube results. They give no source or prior-art clearance. No native
search or browser was substituted. The current successful registry catalog
refresh gives metadata only; complete current heads/bodies and historical
gaps remain HOLD. The2004 original and material2024/2010 published matrix
proof bodies were not obtained/read. Publication details for these are
bibliography-reported, not authenticated version comparisons.

The universal prime-size reconstruction lemma remains unproved. Finite
controls are method diagnostics, not full source proof/refutation. No
PROOF.md, Lean, manuscript, shared/count edits, git, children, MathDB edits,
external messages/posts/uploads. Only the assigned r194 lane was written.
''')
put('progress.md', '''# Progress and handback

1. Read ancestor/batch rules, ledger, prior context and current NEXT; counts9/39,next40.
2. Bound corrected r189/r191 indexes; refreshed2,564 historical paths/nine changes,
   preserved aliases and r111–113; parked inherited failed routes.
3. Guarded broad current NT/RA/AC source search; exact early screens.
4. Read three actual primary bodies; two public resolutions rejected as reconnaissance.
5. Sustained full matrix recognition question; read full closest available2026 proof,
   attempted material2024 publisher body early, retained403 and access limits.
6. Wrote complete conditional classical bridge and exact missing prime-base lemma.
7. Exact finite diagnostics: two512-element rings,4,096 module controls,768
   dimension-bound controls; method falsifiers, no all-order proof.
8. Scientific originals/copies and guard frozen; runnable checks replayed;
   separate guarded verification follows final manifest writes.

Zero nominations/credit. Root alone may adjudicate further research. No formal
or manuscript investment recommended on this incomplete result. Do not reopen
denied routes or parked history absent concrete new legitimate evidence.
''')
put('run-checks.sh',f'''#!/bin/sh
set -eu
cd "$(dirname "$0")"
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python '{guard}' python checks.py
''')
save('provenance.json',dict(utc=now(),status='UNRESOLVED; zero nominations',counts=dict(additional=9,total=39,next=40,credit=0),target='Shahverdi–Shahverdi2610.37150v1 Conjecture1.1, all m>=2 finite fields and unital R',fresh_target_slots=1,reconnaissance_rejections=['2610.37512 public coprime matching proofs','2610.37356 public valuation-tree refutation'],qualified_history_paths=len(h['records']),changed=len(h['changed']),unique_investigation_count_asserted=False,r111_113={str(r):sum(f'r{r}/' in p for p,z,b in h['records']) for r in [111,112,113]},http='http.jsonl',primary='primary-hashes.json',chronology='chronology.json',science='scientific-input-freeze.json',missing_lemma='Odd prime-size ring reconstruction from full commuting graph; field center/radical exclusion',limitations=['Closest2024 published body403 unread','Current full public trees and historical coverage incomplete','No universal source proof or worldwide priority assertion'],failures='FAILURES.md',children=False,git=False,browser=False,Lean=False,manuscript=False,external_messages_posts_uploads=False,MathDB_edits=False))
p=subprocess.run(['python',str(L/'checks.py')],capture_output=True);assert p.returncode==0
save('replay-receipt.json',dict(utc=now(),returncode=p.returncode,stdout_sha256=sha(p.stdout),matches_initial=p.stdout==(L/'checks.json').read_bytes()));assert p.stdout==(L/'checks.json').read_bytes()
# Scientific outputs: immutable lane science; administrative snapshots are separately preserved.
excluded={'finalmanifest.json','manifest-verification.json','scientific-freeze.json','scientific-verification.json'}
save('scientific-freeze.json',dict(utc=now(),files=[[str(p.relative_to(L)),sha(p.read_bytes()),p.stat().st_size] for p in sorted(L.rglob('*')) if p.is_file() and p.name not in excluded and not p.name.startswith('snapshot-')]))
