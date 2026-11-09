from pathlib import Path
import json,hashlib,re,subprocess
R=Path(__file__).resolve().parent.parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
c=json.loads((R/'audit-certificate.json').read_text());corr=json.loads((R/'audit-correspondence.json').read_text())
sweeps=[json.loads(p.read_text()) for p in sorted(R.glob('audit-sweep-*.json'))]
assert len(sweeps)==36 and sum(map(len,sweeps))==1836
assert all(x[-1]==x[-3] for batch in sweeps for x in batch)
family=[json.loads((R/f'audit-family-{b}.json').read_text()) for b in range(19,44)]
assert all(x['result'][0]>x['result'][2] for x in family)
ledger={'mathematical_claims':{'parameters':c['parameters'],'generators':c['generators'],'composition_cardinalities':c['composition_counts'],'X':c['X'],'Y':c['Y'],'S':c['S'],'T':c['T'],'row_table':c['rows'],'D_five_part':c['D_five_part'],'type_flow':c['type_flow'],'reverse_flow':c['reversed_flow'],'HK':json.loads((R/'audit-hk.json').read_text()),'small_sweep':{'A_max':10,'a_max':10,'sum_max':16,'nontrivial_cases':1836,'all_pass':True,'remaining_cases':'proved by swap, identity, B=1 transfer or B=0 empty-domain argument'},'family':family},'formal_metadata':corr,'bibliographic_numbers':'IDs, theorem/section/reference numbers, dates, DOI, volume/pages, version numbers, dependency pins and hashes are identifiers, verified against frozen source copies and replay receipts; not arithmetic claims. 2026-11-04 is the preparation date. Zero credit is lane status.','algorithms':'Direct recursive enumeration plus all-prefix dominance; multiplicity DP and integral unit-transfer flow for supporting sweeps; HK target independent of transfer network.'}
(R/'numeric-claim-ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
proof='''# Proof and scope: DRAFT, AI-assisted, zero accepted credit

Source: Clifford Smyth, arXiv:1512.04084v1, Conjecture 1.5; MathDB 332037. N includes zero. U^m_n consists of length-m ordered maps to N summing to n. Rearrange concatenations decreasingly and compare equal total sums and all prefixes. The domain must dominate its image.

At (A,a,B,b)=(3,20,2,19), let X=U^3_19 × U^2_20 and Y=U^3_20 × U^2_19. Let D be all partitions of 39 dominated by some generator in G:

'''+json.dumps(c['generators'])+'''

Define S={x in X: rearr(concat(x)) in D} and T likewise in Y. Direct enumeration gives |S|=1137 and |T|=1134. D is downward closed by transitivity: total weights agree and each prefix inequality composes. A conjectured injection would map S into T and remain injective there, requiring 1137 ≤ 1134. Contradiction. This refutes the exact universal conjecture, not Smyth's independently proved total-nonnegativity theorem.

The row counts are in audit-certificate.json and every row matches the copied Lean certificate text (audit-correspondence.json). Compositions are enumerated uniquely by successive first entries. Prefixes beyond five equal the total. Complete sorted ordered-pair lists, including zeros, are S.json and T.json, serialized with Python json.dumps default separators and no trailing newline:

- S SHA-256: '''+c['hashes']['S']+'''
- T SHA-256: '''+c['hashes']['T']+'''

The Lean ZIP is reused byte-identically. Its endpoint is Smyth1512.not_conjecture15 : ¬ Smyth1512.Conjecture15. Seven literal definitions are compared textually to the reviewed discovery draft. The structural enumeration bridges, sum condition, finite/all-prefix bridge, duplicate-free lists and list/function realization are in Bridges.lean; CountBase and the row modules prove counts; Endpoint gives the finite injection contradiction. Controls proves sorted permutation fidelity and an inhabited true instance.

Supporting computation only: maximum matching 4407 by fresh HK and flow, reversed flow 4050, small region through bounds 10 and sum 16 passing, and family b=19 through 43 failing. The fresh sweep checks 1836 nontrivial cases; all remaining cases have the explicit general constructions in the paper. No infinite-family theorem or separate credit is asserted.

Root's copied replay receipt reports PASS for the packet's 48 modules and explicit checkers, with endpoint axioms propext, Classical.choice, Quot.sound. This worker never ran Lean, lake or leanchecker. The current registry receipt is bounded path/header screening, not full-body proof reading.

Retention: the author-hosted submitted Order manuscript retains the conjecture as Conjecture 6 and its implication as Theorem 7. The printed post-refereeing body is UNREAD. Prior-art searches are bounded; no priority claim is made. Significance is modest, low-profile and non-load-bearing. Root alone accepts; accepted credit is zero. The campaign context supplied to this lane was 37/40 beyond 39; this document makes no ledger update or assertion of a refreshed count.
'''
(R/'PROOF.md').write_text(proof)
(R/'REPRODUCE.md').write_text('''# Reproduction without Lean in this lane

All commands below are run from this dossier directory. Python uses only its standard library, in isolated mode. Required system tools for PDF: groff with eqn/tbl and PostScript device/fonts, Ghostscript, and Poppler. A local macros.tmac avoids a dependency on groff's optional ms package. The editable manuscript source is paper.ms; scripts/paper.py is the generating source. Do not run the historical patch/polish scripts on the final generator.

For each command use `MALLOC_ARENA_MAX=2 python3 -I scripts/capped.py LABEL COMMAND...`. The wrapper limits affinity to two available CPUs, CPU to 120 seconds and address space to 6 GiB, samples process-group RSS, enforces wall time below 140 seconds and reaps the process. Run commands serially. TMPDIR is dossier-local.

1. `python3 -I scripts/audit.py certificate` recomputes compositions, generators, lists, row counts, type and reversed flows.
2. `python3 -I scripts/hk.py` recomputes element-level matching.
3. For each A from 3 to 10, separately run `python3 -I scripts/batch.py sweep A`.
4. For each b from 19 through 43, separately run `python3 -I scripts/audit.py family b`. Do not put the entire family into one capped process: a development batch reached its CPU cap after b=42. b=43 subsequently completed in its own capped process.
5. `python3 -I scripts/metadata.py` verifies seven definitions, module count and every Lean row numeral by reading text only.
6. `python3 -I scripts/paper.py` regenerates paper.ms, paper.ps and paper.pdf. To edit manuscript text, edit the generator or edit paper.ms directly and run groff -e -t -Tps macros.tmac paper.ms, then Ghostscript pdfwrite, saving both outputs only inside this directory.
7. `pdftoppm -r 110 -png paper.pdf qa/page` renders all pages. Inspect each page again after any edit. The supplied final render was visually reviewed page by page.

The packet safe-extraction receipt and stage.py document traversal, symlink, duplicate-name, size, content and required SHA-256 checks. Source ZIP is never regenerated. No Lean execution is part of this manuscript workflow. The upstream packet REPRODUCE.md records Lean 4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612; running its replay belongs to root. Supplied formal and root reports are evidence, not worker replays.

Evidence copies retain source-relative paths and receipts. Exact MathDB line is evidence/expanded-corpus-r151/raw/332037.jsonl. Its SHA-256 is recorded in audit-correspondence.json. Before/after manifests hash all selected frozen inputs, and a separate pair binds the final root receipts when they appeared.

Dossier packaging is performed by scripts/package.py after QA and all receipts settle. MANIFEST.sha256 excludes itself and the outer ZIP/ZIP hash receipt to avoid self-reference. full-dossier.zip includes the manifest; full-dossier.zip.sha256 binds the outer ZIP. Hash identity checks also ensure the copied sources match their originals.
''')
(R/'INCIDENTS.md').write_text('''# Development record

- Initial staging lacked the receipts directory; data copying and safe extraction completed before receipt writing failed. The directory was created and staging was rerun. No input was altered.
- System reportlab and TeX engines were unavailable. Groff had no PDF device or installed ms macros. Failed authoring calls are recorded in receipts. The final build uses a local macro file, groff PostScript and Ghostscript; no installation or network access was used.
- Initial render review caught absent section headings and incorrect superscript/subscript grouping. These were corrected and all final pages were rendered and inspected again. Historical generator patch scripts remain for provenance; do not rerun them.
- The b=31..43 family batch reached its existing CPU cap after completing b=42. It exited without a b=43 result; no cap was increased. A separate capped b=43 run succeeded. That batch's negative exit and sampled RSS are preserved in receipts/family31-43.json. No job was left running.
- All authored files are within this lane. No git, network, messages, browser, Lean, lake, leanchecker, child agents or shared-ledger edits were used. The PDF skill's marker was run successfully; its standard reportlab recommendation was replaced by the available local toolchain.
''')
(R/'SUMMARY.md').write_text('''# MathDB 332037 manuscript handback

DRAFT, AI-assisted. Zero accepted credit; root alone accepts. No priority claim.

- Six-page paper: paper.pdf; editable source paper.ms, macros.tmac and scripts/paper.py.
- Complete pigeonhole proof and eight-generator certificate: PROOF.md, S.json, T.json, audit-certificate.json.
- Fresh numeric audit: 1137 > 1134; matching 4407 by HK/flow, reverse 4050, stated finite sweep and family reproduced. See numeric-claim-ledger.json and resource receipts.
- source-only.zip is byte-identical to the required Lean packet (82e134f245cd795d51695f1a1be8a15b4167212ff4742d18f2a2f0c5ce7ac0c2). Safe extraction passed. No Lean tool was run here.
- Seven statement definitions and every row numeral textually checked. All 48 packet modules retained unchanged.
- Copied root replay-result.json reports PASS; registry-refresh.json reports bounded path/header screening. Neither is pending at handback.
- Positive retention evidence is the author-hosted submitted manuscript's Conjecture 6 and Theorem 7. The final printed body is unread. Significance is modest and no worldwide novelty claim is made.
- Every final PDF page was rendered and visually inspected. QA images and receipt are in qa/.
- Complete dossier: full-dossier.zip, MANIFEST.sha256, outer ZIP SHA-256, before/after input manifests, evidence copies and receipts. See REPRODUCE.md and INCIDENTS.md.
''')
results={'status':'DRAFT; ready for root review; not accepted','mathdb_id':332037,'accepted_credit':0,'root_alone_accepts':True,'ai_assistance':'OpenAI Codex','paper':'paper.pdf','paper_source':['paper.ms','macros.tmac','scripts/paper.py'],'pages':6,'central_counts':[1137,1134],'lean_packet_sha256':h(R/'source-only.zip'),'endpoint':'Smyth1512.not_conjecture15 : ¬ Smyth1512.Conjecture15','lean_executed_here':False,'root_replay':'supplied PASS','registry_refresh':'supplied bounded path/header screen','retention':'author-hosted submitted manuscript retains Conjecture 6; final printed body UNREAD','priority_claim':False,'significance':'modest; low-profile, non-load-bearing conjecture','jobs_at_handback':0,'dossier':'full-dossier.zip','numerical_audit':'numeric-claim-ledger.json'}
(R/'results.json').write_text(json.dumps(results,indent=2)+'\n')
print('Dossier prose and numeric ledger written')
