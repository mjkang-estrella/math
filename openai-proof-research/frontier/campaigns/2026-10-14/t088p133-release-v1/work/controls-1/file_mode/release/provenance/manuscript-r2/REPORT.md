# T088P133 final-manuscript implementation, round 2

Completed implementation for the parent's independent final manuscript review. Runner as assigned: Codex / GPT-6 Astra / high / default service tier. Author Myeongjin Kang; no affiliation or contact. Count remains18/20. Publication/uploads/submissions/contacts/browser UI STOPPED. No nested agents, git, staging, commits or release. Every new file, build, copied cache, private evidence and scratch item is within this assigned r2 root. No active fresh-structural-discovery-r137 content was read. Pinned fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb theorems and operative proofs were stipulated true; no upstream truth audit was performed.

This is implementation, not an independent correctness, contribution, formal, manuscript, acceptance, count or release gate. Parent alone integrates and dispatches independent final review. The adopted formal PASS has only its stated deterministic scope; no author formal repair was requested or made.

## Delivered manuscript and exact preservation

The20-page paper is `packet/public/output/pdf/main.pdf`; complete source is `main.tex`, `references.tex`, `witness-tables.tex` and the new `formal-appendix.tex`. The theorem remains exactly V4(Pi K)<=(160/3)V4(K)^3 for convex4-polytopes with nonempty interior and at most six ACTUAL irredundant facets, with h(Pi K)(u)=V3(K|u-perp), equality iff a simplex. Every six-facet case remains strict, including nonsimple, repeated-Gale, zero and boundary strata. No >=7-facet, general-body, dimension5-8, auxiliary best-constant or positive all-n threshold theorem is added.

`qa/source-preservation.json` and `qa/main-r1-to-r2.diff` show that all mathematical-section bytes through AppendixA are unchanged after removing the explicitly delimited new formal use-site paragraph. All1 theorem,5 lemma,3 proposition and9 proof environments are identical. The witness appendix, exact witness JSON, original author code, floating geometry, later independent recurrence, exact reproduction driver, build script and bootstrap are byte-identical to r1. All248 nonzero terms and all11 prior bibliography entries are preserved. Only current status/provenance wording, the PropositionB use-site note, formal appendix and two formal references were added/updated. The full probability/geometry proof remains necessary and intact.

## Actual formal integration

The independently supplied original r1, formal implementation and independent review FINAL/MANIFEST/outsideREPORT anchors were authenticated before reuse and reauthenticated at completion. The original formal code/control/audit bytes, pins, notices/licenses, coverage and scripts are unchanged;53 original public files are bound in `formal/origin.json`. Original envelopes are under `formal/historical/`. The parent adoption has PASS_SCOPED_SUPPORT, no required repairs. Original r1's truthful pending status remains untouched, and unchanged historical copies are explicitly labelled.

Exact scope:21 support declarations (3 definitions/18 theorems),20 controls and15 independent semantic/type/use-site audit declarations, using only propext,Classical.choice,Quot.sound. `T088P133.rational_mixture_lt_one` is universal over real alpha,beta,p,q,d,P,N with alpha,beta>0,sum2,0<p<1,q=1-p,d>=0,P,N>0,2dp²<P,2dq²<=N and concludes (1+d)[p alpha/(alpha+P/p)+q beta/(beta+N/q)]<1. Non-strict wrapper, positive denominators, moment conversions, residual decompositions and reduced p=0/p=1 expressions are covered. d=0 is included. `one_sided_lt_one` validly requires no d>=0.

The new use-site note maps original equation labels eq:Sn,eq:mixture,eq:two-brackets to the actual reviewed declarations. AppendixC states exact hypotheses and Lean's polynomial residual/square decomposition, while preserving the paper's Cauchy-Schwarz proof. The independent audit establishes the original normalized brackets and scalar-majorization composition with an EXPLICIT scalar premise. It does not establish that premise for an expectation.

ENTIRELY UNFORMALIZED: actual-facet geometry/nonzero middle-vector exclusion; mixed-volume attainment/coarea/Gamma-Dirichlet; distributions/log-concavity/HNBUE and expectation-to-mixture majorization; ten-pattern certificate and probabilistic interpretation; continuity/zero/repeated-knot assembly and derivation of strict moments; simplex equality, every-six-facet geometric strictness and the full theorem.

Trusted compiler: Lean4.34.1 commit5045d0056413266e57c625dcd7c365b10e377c52, at `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`. Trusted read-only precompiled cache: `frontier/campaigns/2026-10-14/formal/.lake/packages`, mathlibd13f23b723b8a846827a245b89c10fc7d3f11612 plus8 locked auxiliaries. Only supplied own sources rebuilt. No clean-source dependency rebuild or complete binary-cache authentication. No cache binaries/private bodies included in the public artifact.

## New portable proof-support execution

The new MIT `support/formal_reproduce.py` uses relative supplied inputs and explicit --lean/--cache. It copies unchanged source/pins/rebuild.py into a fresh package under the copy's build/work, compiles implementation/control/audit files, prints all56 actual types and axiom reports, and repeats the ten rational configurations and two semantic mutations. Original scripts and packages remain unchanged. The unchanged historical `formal/review/replay.py` requires its original companion implementation/project archive; it is explicitly NOT standalone portable reproduction and is not called by the new wrapper. Historical inventories are metadata, not required executable inputs.

The actual test used a separate context at `build/extracted-proof-support/`, supplied only formal public files and the new wrapper. It contains no manuscript/author/private source inputs. External execution inputs were the explicitly supplied trusted compiler/runtime and pinned precompiled cache. This is source-path portability testing, not OS-level filesystem isolation.

```sh
python3 -B build/extracted-proof-support/packet/public/support/formal_reproduce.py \
  --lean /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean \
  --cache /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages \
  --output "$PWD/build/extracted-proof-support/build/work/replay-1"
```

Result REPRODUCED_56_DECLARATIONS:21/20/15, no compilation warnings, actual implementation and review type logs identical to reviewed logs. Both added-premise mutations compiled their altered support but failed exact type contracts as expected. All10 exact rational configurations passed. Actual logs, commands, source hashes, dependency receipts and copied-context inventory are in `qa/formal/`. Historical eleven-case implementation and eleven-case review integrity suites remain attributed historical evidence; they are not mathematical semantic proofs. New manuscript artifact controls are separate.

## Exact support and PDF QA

The retained exact support was rebuilt on these new copies only:

```sh
bash packet/public/build.sh
python3 -B packet/public/support/author-certificate.py > build/author-certificate.log
python3 -B packet/public/support/independent_certificate.py build/checks/rebuilt-witness.json > build/independent-certificate.log
python3 -B packet/public/support/geometry_control.py > build/geometry-control.log
bash packet/public/build.sh
pdftotext -bbox packet/public/output/pdf/main.pdf build/main-bbox.xhtml
```

`build.sh` calls the exact reproduction driver, compares regenerated witness-table bytes, compiles with Tectonic0.17.0 --untrusted and2 reruns, checks source references/logs, and renders every page at120dpi. All five polynomials Np,NP,Den,D,T match the original author and independent recurrence for all10 patterns; witness bytes regenerate exactly. All248 coefficients are positive with the retained endpoint terms. The cleared algebra identity is an exact zero polynomial. The n=5 certificate has minimum coefficient-6, which rejects that certificate only; the separate existing corner calculation gives auxiliary ratio5495618760267/5255309886352>1, without any geometric conclusion in dimensions5-8. The author Monte Carlo and40-example floating geometry passes are diagnostics only; neither substitutes for proof.

The PDF skill's authoring marker was invoked exactly once before new PDF authoring. The first PDF build identified2 overfull lines in the new compiler/dependency paragraph. A hash table and ordinary prose wrapping corrected them. The two subsequent final builds had zero missing citations/labels, duplicate labels, TeX warnings, overfull or underfull lines. All20 final pages were individually viewed; page14 dense table columns were additionally inspected in a240dpi crop. No clipping, overlapping formulas/table entries, missing visible references or unreadable glyphs were observed. Reference13 occupies the otherwise sparse final page; it is an ordinary bibliography continuation. This is implementer visual QA, not independent manuscript review.

The two final builds produced identical PDF bytes and all20 identical PNG bytes, with SOURCE_DATE_EPOCH1792454400 and the same copied Tectonic binary/populated415-file cache. All415 cache file bytes and engine bytes still match r1. The local build refreshed33 fontconfig-cache mtimes, with unchanged modes; exact local metadata differences are recorded. No old cache was written. No clean offline release or cross-engine byte identity is claimed. The bbox extraction includes control characters2,3,18,19,20,21; they were removed only for XML parsing. No PDF/image was changed. All extracted word boxes lie inside their page; this supplements, not replaces, visual QA.

## Reads, provenance and rights

Required r1 source/bibliography/witness/prose/report/build/support/QA evidence, original role inputs, parent intake/adoption/dispositions and completed formal source/review/type/axiom/semantic receipts were read. Named file hashes and read extents are in `provenance/implementation-read-record.json` and `source-reading-records.json`. Large metadata inventories were authenticated/structurally parsed rather than represented as primary-body reading. Truncated combined text outputs were reread in bounded chunks/compact decoded form. All ten complete witness rows were decoded and printed. No new download or global/project priority/open-status survey occurred.

Actual retained primary rereads: SourceP README/main/references full; FHLX TeX157-374,991-1602, including all Section4, with PDF byte-authenticated only; Prekopa actual PDF text for Theorem3 and6-8 proofs; Petty introduction only for scope; Saroglou2011 opening statements/Section7 and2015v2 introduction/main statements; Klefsjo metadata/abstract only. Historical original r1 authentication of eight pinned bodies is explicitly distinguished from this round's17 retained-file hash checks. Brannen/CFLXX bodies remain unavailable; Klefsjo bodies and other historical body limits stay unread. Original acquisition records and bodies are private under their original rights.

PQ1-PQ5, SourceP/FHLX/r132/classical credit and bounded no-antecedent positioning are preserved. The prefreeze sketch/certificate already existed. The recorded freeze17:21:32UTC precedes extended prose, not all ideas. Original author FINAL17:31:58.711847UTC conflicts with drafting/packaging17:36-17:45UTC; both remain without choosing a cleaner chronology. Late reads and the original temporary-path deviation remain disclosed. Earlier network/usage failures were not mathematical verdicts; corrected missing-V checker and distinct-only spot-sample limitations remain explicit.

Original prose CC BY4.0; original code MIT with notices retained, including formal/audit code. No third-party body is relicensed or publicly bundled. Copied historical inventories are metadata only. Current private evidence/caches are separately bound and excluded from public verification. R1public52files/seven directories and its separate FINAL-bound36 named private files authenticate. The parent intake's1046 original checks,12 copied cases and exact support were artifact checks with sampled layout only. R1all17-page visual QA and same-cache PDF identity remain original implementer observations.

## Preservation, controls and seal boundary

The original six complete roots contain3682 entries. Exact path sets, bytes, sizes, modes, link counts and symlink targets match the pre-work snapshot; six named parent inputs match earlier copied bytes. No whole-parent or live-ledger preservation claim is made. Original r1/formal/review read-only public verifiers passed against the independently supplied anchors. The private r1 inventory was checked separately; public verifier results do not cover it. The preservation method is lstat/read/hash comparison, not syscall tracing.

New12-case preseal artifact controls passed on separately sealed full-payload copies, with clean acceptance and expected wrong-anchor/byte/missing/extra/directory/symlink/hardlink/mode/envelope rejections. Every verifier invocation was read-only and the real packet remained unchanged. `qa/integrity-controls.json` explicitly records its preseal timing; final artifact checks and any postseal copied controls are retained outside the immutable seal under work/. These are artifact checks, not mathematical review.

The public seal covers exactly147 files and22 directories under packet/, plus externally anchored FINAL.json, packet/MANIFEST.json and this outside REPORT.md. Public payload files are mode0444, directories0755. A trusted copy of verify.py and externally supplied three anchor values are required; the candidate's own manifest is not its own trust anchor. The verifier checks exact public path set/file bytes/sizes/modes/single links/directory modes and envelope bindings. It does NOT audit private evidence, cache contents, executable dependency trust, mathematical correctness, source rights or acceptance.

`private/MANIFEST-r2.json` names36 private files and is separately FINAL-bound. It includes the new cache inventory, which separately names416 engine/cache files. Both are outside the public verifier's coverage. Other build/work/tmp/tools products are excluded except the explicitly named engine/cache inventory. No private body or binary cache is part of packet/. Rebuilds must use a disposable writable copy; originals and this sealed manuscript remain unchanged. Parent alone dispatches independent final review.

Detached final hashes are emitted in DETACHED-ANCHORS.json and the implementation handoff, avoiding a circular self-hash in this report.
