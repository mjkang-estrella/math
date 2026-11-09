from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent
(P/'README.md').write_text('''# Logarithm-arctangent source inequality: review packet

Credit0 / pending final review / no priority claim. Root alone owns acceptance.
Counts remain 3/30 additional, 33/60 total. No count or ledger mutation.

Read main.tex or paper.pdf for the self-contained ordinary proof. Its finite
arithmetic has a compact exact reconstruction rule and a full machine-readable
supplement. Run `python3 supplement/exact_check.py` (hard 512 MiB AS, 35 CPU
seconds; external 45-second wall deadline is enforced by verify.py; BLAS1).

Run `PYTHONDONTWRITEBYTECODE=1 python3 verify.py replay` from an extracted packet.
The replay directory must not already exist. It builds 35 unchanged mathematical
modules and 35 exhaustive origin audit modules, serially, using the absolute
pinned Lean binary and external eight package caches in pins.json. It does not
read root-generated candidate oleans. Only local extracted replay outputs and
pinned upstream package/toolchain oleans enter LEAN_PATH.

The monitor samples process-group RSS every 40 ms, kills at >=3 GiB, and applies
a 240-second wall deadline per process. Sampling is not a continuous bound or
virtual-address-space limit. Every passing sample must be strictly below 3 GiB.
No limit inflation is permitted. The checker has its own hard AS/CPU limits.

Each audit enumerates env.header.moduleData[i].constNames for its actual origin,
not a namespace/name regex. Logs include generated/private/instance declarations,
actual types, transitive axioms, unsafe/partial/axiom flags. Only propext,
Classical.choice and Quot.sound are allowed. Unsafe declarations/custom axioms
are rejected. Harmless generated partial recursors can have partial=true and
unsafe=false; neither their names nor the substring unsafe is a rejection rule.
Consumed upstream mathematical source hashes are recorded separately. This
accepts pinned upstream mathematics as instructed; it does not reprove mathlib.

build_pdf.py uses the recorded existing Tectonic binary and a lane-local copy of
its cached resource bundle; no network is needed. Set SOURCE_DATE_EPOCH is fixed.
The archive is sorted, ZIP_STORED with timestamp 2026-10-29 00:00:00 and mode 0644.
`python3 pack.py` writes packet.zip and verifies its embedded SHA256SUMS after
extraction. Build twice and compare hashes. Source-only means no oleans or
prebuilt proof artifacts; manuscript and primary-source PDFs are documents.

Adjacent receipts document the actual extracted replay and PDF/ZIP comparisons.
Initial failures are retained outside the archive and described in FAILURES.md.
Input sources and inherited status notes are preserved verbatim under inputs;
obsolete no-Lean/journal-HOLD paragraphs there are historical, not current status.
''')
(P/'PROOF.md').write_text('''# Proof and source map

The authoritative ordinary proof is main.tex, Sections 1--6; paper.pdf renders it.
Sections 4--5 and supplement/exact_check.py provide the complete finite-rule proof
of global E positivity. No sampled finite numerics is used. Mathematical Lean
modules are byte-identical to integrated-core-hashes.json (35 modules).

* Published equation (5), p4 -> MeanSourceDefs.mean, exactly log b-log a / sqrt2.
* Published resultant p1 -> MeanSourceDefs.resultant, inner Bq, outer Bp.
* Published Conjecture37 p21 -> SourceClaim and SourceTheorem.source_conjecture37,
  unconditional theorem of SourceClaim; universal positive distinct real inputs,
  conjunction of both branches, no residual E or monotonicity premise.
* MeanAnalyticDefs -> literal A,B,U,V,E in paper Section3.
* MeanExpansion/MeanFiniteCertificate -> twelve ordered frequencies/36 prefixes.
* ExpPolynomial/MeanEExpansion/MeanWeights/MeanEHighPositive -> actual derivative
  24 identity, c1+c2 (96 total), not c1 alone (94).
* MeanJets*, MeanJet12--23, MeanEPositive -> exact jets and derivative ladder.
* MeanDerivatives/GapAnalytic/GapMonotonicity/Centered -> J comparison and strict
  centered log(S/M) increase, including zero limit and positive denominators.
* Stolarsky/Transfer -> classical two-sign stabilization and homogeneous transfer.
* FiniteAbel -> classical supporting identity, no separate credit.

The source Definition1 between-means terminology is NOT the formal endpoint.
AUXILIARY.md is ordinary supporting material only. Neither stronger terminology,
all parameter ranges nor other source conjectures are claimed.

Sources: actual published PDF and complete extracted text are in inputs/root-log-
arctangent-source-r3/sources. The publisher PDF hash is
12d7e2e0ad6791af369b747fb26d8e3e2145c493dc3804445334102557f5010f.
Rendered printed pages 1,2,4,21 were personally read in this lane. The arXiv label
is Conjecture4.7; the surviving published label is Conjecture37. The older source
subsumption HOLD is superseded as to journal identity by actual body reading and
the investment-review-r3 decision, which is not acceptance. Formal success does
not confer public-claim credibility or priority.
''')
(P/'FAILURES.md').write_text('''# Preserved limitations and corrections

Root reported default-parallel MeanFiniteCertificate compilation hitting 3 GiB;
root's -j1 replay passed unchanged sources. This packet requires -j1 everywhere.

Own initial 35 mathematical modules passed serially. The first combined audit
with an unnecessary `import Lean` reached sampled 3,242,569,728 bytes and was
killed; a first per-origin Centered audit with that import reached 3,223,007,232
bytes and was killed. No limit was raised. The correction is per-origin audits
without `import Lean`; required metaprogramming APIs are already imported by the
mathematical modules. Mathematical proof bytes were never changed. Initial logs
and replay are retained adjacent to the archive, not passed off as a full PASS.

The first PDF build caught a 24.57745pt overfull equation. Splitting its displayed
line fixed it; final build asserts absence of Overfull and is visually reviewed.
A deliberate 94-only derivative mutation is rejected by the exact checker; that
negative control is expected and not a failed proof.

Strongest surviving objection: a prior global ratio theorem or a fully verified
routine classical specialization could subsume the whole source outcome. Existing
bounded reviews found none. Missing MathDB access and incomplete specialist-body
coverage persist. Final current registry/prior-art reconciliation and independent
packet/manuscript review belong to root. Credit remains zero.
''')
inputs=json.loads((P/'input-before.json').read_text());L=P.parent
assert all(hashlib.sha256((L/n).read_bytes()).hexdigest()==s for n,s in inputs.items())
(P/'input-after.json').write_text(json.dumps(inputs,indent=2)+'\n')
provenance={'date_utc':'2026-10-29','status':'credit0/pending-final-review/no-priority','counts':'3/30 additional;33/60 total;unchanged','formal_freeze_supplied':'33b9e8cbf9 (not git-authenticated)','source':{'authors':'Lenka Mihoković; Mustapha Raïssouli','title':'Results on comparison and sub/super-stabilizability of some new means','journal':'AADM20(1)(2026)1-23','doi':'10.2298/AADM240618001M','url':'https://pefmath.etf.bg.ac.rs/vol20num1/AADM-Vol20-No1-1-23.pdf','sha256':'12d7e2e0ad6791af369b747fb26d8e3e2145c493dc3804445334102557f5010f','cached_body_read':True,'rendered_pages_personally_read':[1,2,4,21]},'access_limits':['No new HTTP requests in this lane. Cached primary bodies reused.','Inherited old publisher hostname TLS failure not retried; no bypass.','MathDB denial persists; no MathSciNet/zbMATH sweep.','Yang2009 and prospective strong-order bodies not obtained.','Dated registry evidence only; final refresh pending; no concurrent worker polled.'],'dated_registry':{'omega':'5517865965160e8d20e4122aafe4e6c468c6c41d','openai':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a','count':'dbf673741a54c7dc9d88a6aec0e8148a538f4a3a','observed':'2026-10-29 06:53--06:55 UTC; investment review; not a later claim'},'input_hashes':inputs,'immutable_math_manifest':'inputs/integrated-core-hashes.json','package_pins':'pins.json','procedures':{'git_commands':False,'children':False,'external_mutations':False,'writes':'assigned lane only'},'checker_adaptation':'reviewed exact_review.py retained verbatim in inputs; supplement changes only local path/integrity plumbing, exact arithmetic unchanged'}
(P/'provenance.json').write_text(json.dumps(provenance,indent=2,ensure_ascii=False)+'\n')
