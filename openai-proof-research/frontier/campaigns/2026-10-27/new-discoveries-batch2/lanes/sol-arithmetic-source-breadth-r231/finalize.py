"""Guarded administrative delivery writer; no source mutation."""
from pathlib import Path
import json,hashlib,datetime,re
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,s):(L/n).write_text(s)
old=L.parents[2]/'2026-10-26'/'new-discoveries'
# Use the actual sibling campaign path, not recursive historical trees.
old=L.parents[3]/'2026-10-26'/'new-discoveries'
terms=['Rahavandrainy','Garth','Ezerman','Gavrylkiv','Zelinsky','Pandey','polynomial pairs','Cameron','Prodinger']
refs=[];hits=[]
for section in ['lanes','candidates']:
 for p in (old/section).glob('*/SUMMARY.md'):
  h=sha(p);refs.append({'path':str(p.resolve()),'sha256':h});s=p.read_text(errors='replace');assert sha(p)==h
  for t in terms:
   for m in list(re.finditer(re.escape(t),s,re.I))[:2]:hits.append({'path':str(p.resolve()),'term':t,'excerpt':s[max(0,m.start()-50):m.end()+150]})
write('prior-campaign-aliases.json',json.dumps({'root':str(old),'references':refs,'hits':hits},indent=2)+'\n')
print('first-campaign summaries',len(refs),'hits',len(hits))
# Fully traverse the two administrative snapshots; acceptance scope is root-owned.
for name in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((L/'admin'/name).read_text());print(name,'accepted records',len(d.get('accepted',[])))
write('SUMMARY.md','''# r231: arithmetic breadth, zero eligible outcomes

Eleven genuinely question-posing arithmetic/algebraic primary families were
screened from 2002–2020 bodies, with bounded 2021–2026 follow-up. They are not
eleven open leads. Three unresolved directions are ranked in SCOUTING.md;
none has complete current novelty clearance.

Complete ordinary all-parameter proof: Gallardo–Rahavandrainy's 2020 p.6
binary-composition irreducibility claim. PROOF.md gives a quadratic trace/image
proof and a direct Frobenius orbit proof. Recommend **zero credit**: classical
cyclotomic/composition bridge. The separate odd-perfect-polynomial question is
not solved. No inference of novelty from age, shortness or database labels.

Early exclusion: HMT2016 C27 is explicitly refuted by Emmons–Xiao2022
Theorem21/Remark22; the actual proof body was read. Exact p=3 rational witnesses
were independently checked as an uncredited source-fidelity control.

Checks PASS:75 odd polynomial parameters u=3..151,17 trace/orbit controls,
3 exact rational derivative witnesses. Finite checks do not replace the universal
proof. All sources/receipts, chronology, alias limits, failures and executable
checks are retained. Separate guarded verification follows final manifest writes.

No Lean, manuscript, children, shared edits, git, public posting, browser or
MathDB changes. Root alone accepts/counts; snapshot stays9additional/39total,
next40. See discovery.md and provenance.json for priority limits.
''')
write('discovery.md','''# Decision and limitations

No eligible discovery. Full source polynomial assertion is proved in PROOF.md,
but its strongest subsumption objection is compelling: irreducibility of a
cyclotomic composition reduces directly to the elementary quadratic trace
criterion. This is the actual bridge, exhibited rather than discarded for being
short. It does not require any numerical conjecture or unproved field statement.

Selected scope: all odd u>1 in F₂[X], P=X²+X+1, R_u=ΣP^j; irreducible iff u is
prime and 2 has order u−1 modulo u. Composite u and nonprimitive prime u are
handled by explicit proper-factor substitutions. Primitive u is handled in two
ways closing every parameter. All hypotheses, ℓ=3 and no-perfectness overclaim
are explicit. Complete proof is not evidence of literature novelty.

Closest actual bodies:2020 journal source p6;2021 arXiv2106.10008v1
Thm1.1/C1.2/Lemma2.3;2026 arXiv2606.08640v3 introductory special-perfect
definition and subsequent necessary-condition arguments. Their scopes differ;
none is used as a missing-proof clearance. Exact chronology/hashes in receipts.

Early same-object rejection was successful for HMT:2016 source C27;2017
Pandey–Saxena suspicion and algorithms;2022 Emmons–Xiao Thm21/Remark22 actual
full proof. Stop that target, including our three simple rational witnesses.

History screen uses compact SUMMARY/discovery/source-alias files (346 initial
references plus expanded bindings), not SCOUTING-only or mass historical copies.
Actual Gallardo author hit r89 concerns binary Collatz degree/length, while r75
is a different restricted-sumset author. Farhi r25 concerns exponential growth,
not floor-square ternary representations. No fresh claim on those old objects.
The r229 primary inventory is word/morphism/shuffle material; r230 is wavelet
material. Arithmetic digit multiplication C4 is distinguished by its equations,
not its palindromic wording. No r228 Seidel return.

Current public proof-registry coverage is not complete: inherited denied
GitHub API/raw/codeload/diff/patch routes were not retried. No ScienceDirect,
Google challenge route, proxy, TLS disabling, browser bypass or repeated HEAD
loop. Crossref returned429 once and was stopped. Search results were irrelevant
and supply no negative prior-art inference. ArXiv query results are bounded
locators, never proof clearance; retained actual primary bodies control exclusions.

Ranked leads and exact missing steps are in SCOUTING.md. All are provisional
research directions rather than certified open questions. No zero-result padding
with Fried's ten already-resolved2026 conjectures or downloaded theorem-only papers.
''')
write('progress.md','''# Guarded progress and replay

Read applicable ancestor/batch AGENTS and snapshots of ledger/prior context.
Only the assigned lane was created/edited. Compact scientific references were
hashed before semantic reads and retained by immutable path/hash, with no
recursive historical duplication. Downloaded bytes and extracted text were
receipted before scientific reading. Final verification rehashes originals and
local primary bytes; administrative files are snapshots only.

Breadth:eleven retained question families; resolved controls and unsuitable
targets disposed compactly. Selected binary-polynomial conjecture developed
through trace-image field towers and direct Frobenius dynamics. This closes the
source claim but exposes routine classical subsumption, so no nomination.
HMT target stopped upon actual2022 proof-body exclusion.

Exact replay from the lane directory (substitute the absolute lane if elsewhere):

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python checks.py

Fixed guard:AS512MiB/groupRSS512MiB,CPU210s,wall230s, no cap changes.
Successful exact check run:75 polynomials,17 trace cases,3 rational identities;
sampled peak group RSS12,201,984 bytes, wall0.1203s. Retrieval batches stayed
below128MiB sampled group RSS. Final manifest excludes itself and the separate
verification receipt. verify.py is run separately through the same guard.
''')
write('FAILURES.md','''# Preserved failures / access limits

1. Initial guarded index parser attempted import bs4, which is unavailable:
   ModuleNotFoundError. Exit1. Replaced with bounded standard-library parsing;
   no installation, cap raise or bypass. Original tool output remains in session.
2. Bing RSS exact-phrase queries returned unrelated general-word results,
   including irrelevant adult results for the dihedral query. Raw responses are
   retained search-0..3.xml. No result destination was opened; no clearance.
3. Crossref bibliographic queries returned unrelated records; fourth request
   returned HTTP429. Exact failure URL is retained in failures.jsonl. No retry.
4. Guessed HMT tossa8.pdf returned404 before using the explicit volume-index
   tossa6.pdf link. Both events retained; no repeated inaccessible-interval loop.
5. No complete current public registry or all-citation history could be cleared
   inside inherited denied routes. This is an eligibility limit, not proof of
   absence. No forbidden route attempted.
''')
receipts=[json.loads(s) for s in (L/'source-receipts.jsonl').read_text().splitlines()]
prov={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lane':str(L),
 'counts_snapshot':{'additional':9,'total':39,'next':40,'authority':'root only'},
 'scientific_freeze':'Remote primary bytes saved and SHA256 receipted before extraction/read; derived text separately receipted. Local originals referenced by pre-read SHA256; final separate recheck.',
 'administrative':'admin snapshots only; no immutability assumption about shared ledger',
 'source_records':receipts,'question_families':11,'nomination':None,
 'proof':'complete but uncredited classical composition bridge','prior_limits':'bounded arXiv author/title queries and actual closest bodies; denied registries not retried',
 'guard':{'AS_MiB':512,'group_RSS_MiB':512,'CPU_seconds':210,'wall_seconds':230},
 'no_changes':['shared','git','public','browser','MathDB','Lean','manuscript','counts']}
write('provenance.json',json.dumps(prov,indent=2)+'\n')
manifest=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['final-manifest.json','verification-receipt.json']:
  manifest.append({'path':str(p.relative_to(L)),'bytes':p.stat().st_size,'sha256':sha(p)})
write('final-manifest.json',json.dumps(manifest,indent=2)+'\n')
print('manifest entries',len(manifest))
