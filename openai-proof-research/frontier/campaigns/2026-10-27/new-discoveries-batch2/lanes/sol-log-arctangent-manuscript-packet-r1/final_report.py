from pathlib import Path
import json,hashlib,shutil,zipfile
P=Path(__file__).resolve().parent; h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
with zipfile.ZipFile(P/'packet.zip') as z:(P/'SHA256SUMS').write_bytes(z.read('SHA256SUMS'))
S=P.parent/'sol-cascade-source-prior-review-r2';(P/'dated-registry-support').mkdir(exist_ok=True)
for n in ['review.md','provenance.json','registry-screen.json']:
 shutil.copy2(S/n,P/'dated-registry-support'/n)
(P/'REGISTRY-ADDENDUM.md').write_text('''# Dated existing registry evidence (not a current-worker review)

Read only the explicitly identified completed sol-cascade-source-prior-review-r2
record; no current concurrent audit was read or polled. Its 07:05:10--07:05:12 UTC
head observations retain OpenAI 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a and
Count dbf673741a54c7dc9d88a6aec0e8148a538f4a3a. Omega had advanced from
5517865965160e8d20e4122aafe4e6c468c6c41d to
6ff649996d7a76101b50eee3dc2a0ef3720691e4. The completed review screened the
complete base trees plus the 33-path public net delta and 38-commit patch,
not a fresh complete recursive tree at the latter head. No matching resolution
was found in that bounded screen. This is dated evidence, not final refresh.

Its historical journal-unread paragraph is superseded by actual published-body
reading here and investment-review-r3. Its MathDB/body-coverage limits remain.
The packet provenance conservatively anchors its inherited investment evidence
to 06:53--06:55; this adjacent addendum carries the later explicitly authorized
07:05 existing record without modifying the replayed archive. The current
independent prior-art review and final refresh remain root responsibilities.
''')
r=json.loads((P/'FINAL-RESULT.json').read_text())
(P/'FINAL-RESULT.md').write_text(f'''# Final implementation result: preparation PASS, no acceptance

Credit **0**. Pending root's final independent review and acceptance decision.
Counts remain **3/30 additional, 33/60 total**. No ledger/count edits, git commands,
children, browser tabs, uploads, contacts, accounts or other-lane writes occurred.
All mathematical source modules are unchanged from the supplied frozen hashes.

## Deliverables

* `main.tex`, `paper.pdf`: self-contained seven-page ordinary mathematical paper,
  author label Research manuscript; exact published two-branch inequality only.
* `supplement/exact_check.py`, `supplement/exact-results.json`: complete exact
  field-arithmetic reconstruction, all 36 prefix signs, actual derivative24
  identity, zero mode/parity, 24 jets, independent integer cross-check and rejected
  94-only mutation. Hard512MiB AS/35CPU, BLAS1, external45-second wall deadline.
* `packet.zip`: sorted source-only proof archive, fixed ZIP timestamps and modes,
  embedded SHA256SUMS, no oleans/ileans/prebuilt proof artifacts. PDFs are documents.
* `README.md`, `PROOF.md`, `provenance.json`, `pins.json`, `FAILURES.md`, supporting
  source/review byte copies, and a strengthened `verify.py` plus origin audits.
* `audit-inventory.json`: all actual declaration types/axioms/flags, extracted from
  the fresh run; raw logs and resource receipts are in `extracted/fresh-replay`.

## Own extracted replay and reproducibility

**PASS70 modules =35 immutable mathematical modules +35 origin audits.**
Endpoint: `LogArctangentSource.source_conjecture37 : SourceClaim`, no premises.
Actual SourceClaim quantifies positive distinct real inputs and concludes BOTH
literal branch inequalities. No residual E or monotonicity premise.

Exhaustive module-origin inventory: **{r['audit_declarations']} declarations**, including
generated/private/instances; no namespace filter. Every actual unsafe flag is
false; custom axiom declarations0; actual partial flags0. A name containing unsafe
is never used as a flag. All transitive axioms are within propext/Classical.choice/
Quot.sound. Consumed source hashes cover **{r['consumed_sources']} modules**, including
pinned upstream source, and are in the fresh receipt. Upstream truth is accepted
as instructed, not re-audited. No root output olean is in the replay search path.

Actual Lean4.34.1 version and binary SHA
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550` asserted.
All eight package HEAD revisions asserted by read-only file/object decoding, and
all tracked content/index compared to each pinned commit before and after replay;
mathlib is clean at d13f23b723b8a846827a245b89c10fc7d3f11612. No git command used.
Serial `-j1 -DwarningAsError=true -DautoImplicit=false` throughout. Each process
has a240-second wall deadline; sampled process-group RSS cap3GiB, no inflation.
Peak passing sampled RSS **{r['peak_group_sampled_RSS_bytes']} bytes = {r['peak_GiB']:.9f}GiB**.
This is a 40ms sampled bound, not a continuous or virtual-address-space guarantee.
All passing samples are strictly below3GiB. The margin is small; future replays
must retain the cap and preserve any failure rather than raise it.

PDF and ZIP reproduced byte-identically twice locally AND again by running their
builders from this own extracted archive. Every embedded/extracted payload hash
matched before/after the fresh run. All seven final PDF pages rendered and
personally read; no clipping or box warnings. Initial overfull equation fixed.

Paper SHA256: `{r['paper_sha256']}`.
ZIP SHA256: `{r['archive_sha256']}`.

## Source/novelty boundaries and strongest surviving objections

Actual Mihoković--Raïssouli published body, AADM20(1)(2026)1--23,
DOI10.2298/AADM240618001M, Conjecture37p21, equation(5)p4, resultantp1 and
Definition1p2 were read in text/renders. Publisher PDF hash
12d7e2e0ad6791af369b747fb26d8e3e2145c493dc3804445334102557f5010f.
The genuine published question survives arXivv2 Conjecture4.7. Formal success is
not evidence of priority. Classical stabilization/Abel/calculus are uncredited.
The optional ordinary between-means sandwich is not in the formal endpoint;
stronger super-stabilizable terminology is deliberately unclaimed.

Strongest external objection: an existing global same-object ratio theorem or a
verified routine classical specialization may subsume the full source outcome.
No such bridge was found in the bounded body reviews; this does not prove its
absence. MathDB access, missing specialized bodies, no comprehensive citation
index sweep and final current-registry reconciliation remain limits. The explicit
07:05UTC existing registry record is carried in REGISTRY-ADDENDUM.md with bounded
base-tree-plus-delta coverage. No concurrent current review was read or polled.

Remaining gates are root's independent final manuscript/packet review, current
source/prior-art reconciliation and acceptance. No identified mathematical or
replay gap remains for the literal displayed conjunction, and no acceptance is
implied. The two branches and all helpers are one prospective family, not credits.

## Preserved failures and fixes

Root's default-parallel resource failure is retained as supporting context.
Our own first combined audit with import Lean was killed at3242569728 sampled
bytes; first split Centered audit still importing Lean was killed at3223007232.
Both failures are preserved in FAILURES.md and initial-replay logs. Removing the
unneeded Lean import and auditing by actual origin fixed the resource issue;
mathematical files and3GiB cap did not change. First PDF build had one24.57745pt
box warning, fixed before the final visually read reproducible build.
''')
# Receipt hashes use existing files, no circular self-hash or stale archive paths.
files=['paper.pdf','main.tex','packet.zip','SHA256SUMS','FINAL-RESULT.md','FINAL-RESULT.json','audit-inventory.json','REGISTRY-ADDENDUM.md','pdf-reproduction.json','archive-reproduction.json','visual-QA.json','original-manifest-recheck.json','extracted/fresh-replay/RESULT.json','extracted/fresh-replay/replay.json','extracted/fresh-replay/consumed-source-hashes.json']
files += [str(f.relative_to(P)) for f in (P/'dated-registry-support').iterdir()]
(P/'receipts-sha256.json').write_text(json.dumps({n:h(P/n) for n in sorted(files)},indent=2)+'\n')
print('Final report written; acceptance untouched')
