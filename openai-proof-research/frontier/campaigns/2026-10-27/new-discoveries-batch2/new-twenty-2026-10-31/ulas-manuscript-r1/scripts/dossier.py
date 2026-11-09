from pathlib import Path
import json,hashlib,shutil,datetime,sys,zipfile
root=Path(__file__).resolve().parents[1];b=root.parent
workspace=next(p for p in root.parents if p.name=='math')
resolve=lambda p:Path(p) if Path(p).is_absolute() else workspace/Path(p)
sha=lambda p:hashlib.sha256(resolve(p).read_bytes()).hexdigest()
def write(name,obj):
 p=root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
old=json.loads((root/'frozen-inputs-before.json').read_text())
assert all(sha(Path(p))==h for p,h in old.items())
paths=[resolve(p) for p in old]
for sub in ['expanded-corpus-r130/sources','ulas-review-r1/downloads','ulas-review-r1/receipts']:
 paths.extend(p for p in (b/sub).rglob('*') if p.is_file())
for n in ['ulas-fidelity-r1/REVIEW.md','ulas-fidelity-r1/review.json','ulas-parent-final-r1/replay-result.json','ulas-parent-final-r1/registry-refresh.json']:
 if (b/n).exists():paths.append(b/n)
write('supplemental-inputs-before.json',{str(p):sha(p) for p in paths if str(p) not in old})
copy_map={}
for p in paths:
 rel=p.relative_to(b)
 if rel.parts[0]=='expanded-corpus-r130':
  dst=root/('sources/'+str(Path(*rel.parts[2:])) if rel.parts[1]=='sources' else 'evidence/'+str(rel))
 elif p.suffix=='.zip':continue
 else:dst=root/'evidence'/rel
 dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dst);copy_map[str(dst.relative_to(root))]=dict(original=str(p),sha256=sha(p))
raw=b/'expanded-corpus-r130/raw/342364.jsonl';(root/'raw').mkdir(exist_ok=True);shutil.copyfile(raw,root/'raw/342364.jsonl')
assert sha(raw)=='048b23cc8020ed78fcc5bf7fdd19b35cb335dee81d47f914b77bfd5c69d31baa'
write('raw/provenance.json',dict(mathdb_id=342364,sha256=sha(raw),includes_trailing_newline=True,raw_copy='raw/342364.jsonl',upstream_chunk='lanes/pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-0006.jsonl',one_based_line=1759,provenance_source='ulas-review-r1/REVIEW.md; no new chunk reread claimed'))
write('COPY-MANIFEST.json',copy_map)
s=(root/'paper.md').read_text();proof=s[:s.index('---PAGE---')]+s[s.index('## 2.'):s.index('## 10.')];(root/'PROOF.md').write_text(proof.replace('---PAGE---',''))
shutil.copyfile(b/'ulas-assembly-r1/STATEMENT-CORRESPONDENCE.md',root/'STATEMENT-CORRESPONDENCE.md')
gate={
 'E.1':dict(location='paper §§1–2',resolution='All seven clauses, all ranges, P1 false and P2 true; not a finite-example refutation.'),
 'E.2':dict(location='paper §§1,3,6,10; raw/provenance.json',resolution='Literal product, colours, stability, actual coefficients and strict nonzero differences.'),
 'E.3':dict(location='paper §§3–9',resolution='Integral transfer with corrected V=sum and W=difference; Lemmas R/W, zero weight convention, Pell/Kummer invariant, half-angle, readout.'),
 'E.4':dict(location='paper §§8–10; low-coefficient-certificate.json; scripts/verify.py',resolution='No interpolation. Exact rational-polynomial identities and expanded integer residue witnesses suffice at >=8. Formal branch uses multiplication induction through index 12 and proves stronger >=11; exposition explicitly distinguishes these routes.'),
 'E.5':dict(location='paper §§2,10–11',resolution='Sufficient infinite equality families throughout; universal never family. Historical exact wording reserved for root reconciliation, no iff claim.'),
 'E.6':dict(location='paper §§10–11; evidence; receipts; toolchain-hashes.json',resolution='Assembly reports, fidelity spot check and root replay distinct from own non-Lean checks; three allowed axioms, audits and controls explained.'),
 'E.7':dict(location='paper §11',resolution='Bounded prior-art record, paywall, 403, excluded services, citation-graph and path-screen limits retained; no new clearance or priority.'),
}
write('gate-E-map.json',gate)
tools={}
for p in [Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'),Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/leanchecker')]:
 if p.is_file():tools[str(p)]=sha(p)
write('toolchain-hashes.json',dict(read_only_executable_hashes=tools,executed=False,version_as_reported='4.34.1',mathlib_revision_as_reported='d13f23b723b8a846827a245b89c10fc7d3f11612'))
write('qa/receipt.json',dict(pdf_sha256=sha(root/'paper.pdf'),pages=10,all_pages_rendered=True,all_pages_visually_inspected=True,inspector='Codex primary agent; direct view_image of pages 01–10 after final status update',findings='Legible glyph fallback; no missing glyphs, clipping, overlapping text, or unexpected page breaks. Plain-text algebra notation retained.',images={p.name:sha(p) for p in sorted((root/'qa').glob('page-*.png'))}))
write('operations.json',dict(no_child_agents=True,no_lean_lake_leanchecker=True,no_git=True,no_network=True,no_external_messages=True,no_browser=True,no_shared_edits=True,writes_only_in_lane=True,background_jobs_left=0,process_notes=['Initial short read-only and authoring calls were not all invoked through the resource wrapper; they completed immediately. Do not interpret wrapper receipts as covering those calls.','All heavy verification/render/raster/packaging jobs serially use scripts/capped.py, two CPUs, CPU 120 s, wall 140 s, sampled RSS 6 GiB and MALLOC_ARENA_MAX=2.','Initial ReportLab lookup and font-glyph attempts failed; their receipts are retained. Local dependencies/fonts copied from supplied Chan-Levine model and system Noto math, no installation.','Some broad early read outputs were truncated; focused reads covered the actual proof and reviews. Supplemental source evidence bound before copying.']))
(root/'REPRODUCE.md').write_text('''# Reproduction and trust boundaries

Run from this dossier directory. This manuscript lane has NOT run Lean, lake or leanchecker. The source-only packet is byte-identical to the assembly, SHA-256 bafc3b63f6baba271680f2eed29334603149cee7c17a714bb7b4b1a04c37d3a1.

Ordinary verification (Python 3 with SymPy; local observed version recorded in results):

    python3 -B scripts/capped.py reverify python3 -B scripts/verify.py

This checks the exact polynomial identities and symbolic residue witnesses, regenerates the table from the colour product and safely extracts the source ZIP into safe-extraction/. No proof tools are invoked. It regenerates artifacts; do so on a review copy if preserving delivery hashes.

PDF regeneration (local ReportLab/Pillow dependencies and fonts are bundled in vendor/ and fonts/):

    python3 -B scripts/capped.py rerender python3 -B scripts/render.py
    python3 -B scripts/capped.py reraster pdftoppm -scale-to 1400 -png paper.pdf qa/page

Inspect every regenerated page; the delivered QA receipt binds the delivered PDF and images only. ReportLab timestamps can change the PDF hash while retaining content. Poppler is a system dependency.

For formal replay instructions ONLY, read evidence/ulas-assembly-r1/REPRODUCE.md and the archived scripts/replay.py and module-order.json. The pinned Lean version is 4.34.1; mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612. The source packet does not vendor upstream mathlib. Binary hashes are in toolchain-hashes.json; these programs were read for hashing, never executed here. Root's separate replay-result.json reports PASS for all 43 builds/checkers, declaration audit and 11 controls. The independent fidelity review reran all 43 builds and endpoint checker, but did not independently rerun the full declaration audit or controls. The assembly and root did those checks. No worldwide priority claim follows.

The dossier ZIP contains the files listed in DOSSIER-MANIFEST.json plus the manifest itself. Safe-extraction/ and vendor bytecode caches are omitted as redundant; ulas-source.zip and renderer runtime sources/binaries are included. The packaging process's own completion receipt and delivery hash receipt necessarily sit outside that ZIP snapshot. Archive CRC and every member hash are verified after creation. DELIVERY.json binds both delivered ZIPs. Before/after frozen-input maps and copy provenance are included. No manifest hashes itself.

Only propext, Classical.choice and Quot.sound are permitted proof axioms. Root must read the paper and decide. Zero accepted credit.
''')
replay=json.loads((b/'ulas-parent-final-r1/replay-result.json').read_text())
fidelity=json.loads((b/'ulas-fidelity-r1/review.json').read_text())
import sympy
write('results.json',dict(lane='ulas-manuscript-r1',mathdb_id=342364,status='DRAFT_FOR_ROOT_REVIEW',credit=0,self_accepted=False,root_decides=True,paper_pages=10,archive_sha256=sha(root/'ulas-source.zip'),ordinary_checks='PASS: exact symbolic low identities and coefficientwise residue certificates, eight exact product examples',sympy_version=sympy.__version__,safe_extraction='PASS; no proof tools executed',qa='All ten final pages rendered and visually inspected',fidelity=dict(status=fidelity['verdicts'],gate_E_applied='gate-E-map.json',limitations=fidelity['limitations']),root_replay=dict(status=replay['status'],utc=replay['utc'],reported_not_executed_here=True),pending=['Root manuscript review and acceptance','Root reconciliation of historical exact equality sets wording','Root novelty/access/substantive-credit adjudication'],operations='operations.json'))
(root/'SUMMARY.md').write_text('''# DRAFT manuscript and reproducible dossier — root review required

MathDB 342364 / Ulas–Żmija Conjecture 6.1. Zero accepted credit; no self-acceptance.

Delivered the ten-page paper.pdf and editable paper.md, PROOF.md, literal raw MathDB line and hash provenance, cached source copies and receipts, assembly/round/review evidence, byte-identical ulas-source.zip, safe-extraction receipt, exact low-coefficient certificates and example verification, REPRODUCE.md, manifests, all page images and QA receipt, and ulas-full-dossier.zip.

The full theorem includes all universal bounds, sufficient infinite equality families, the universal +7 fifteen-family bound and never equality. P1 is refuted; P2 is proved. The ordinary proof includes the actual-series integral operator bridge, Lemmas R/W, Pell/Kummer invariant, odd half-angle initialization, exact low polynomials, residue witnesses, readout and positivity. A sign in inherited transfer-integrality prose was corrected: the odd transfer uses U_N+U_(N−1), whereas the half-angle polynomial uses U_N−U_(N−1). There is no interpolation oracle. The exposition uses sufficient >=8 residue witnesses; the formal packet proves stronger >=11 by its distinct symbolic route.

All ten final PDF pages were rendered and visually inspected. Safe extraction and exact ordinary checks passed; no Lean, lake or leanchecker was run. Initial dependency/font failures are retained. Local renderer dependencies/fonts were copied read-only from the supplied Chan-Levine model and system font; no network installation.

The independent fidelity review is present: A–D PASS, E QUALIFIED_PASS, no required formal-source fixes; all seven manuscript items are mapped in gate-E-map.json. The root replay receipt is present and reports PASS for all 43 builds/checkers, audit, and 11 negative controls. This is an attributed report, not a replay by this lane. Root must still review the paper, reconcile the older exact equality sets wording with sufficient families, and decide novelty/access/substantive credit. No priority claim or new access clearance is made.

Original, supplemental, and renderer frozen inputs are hash-bound before and after and unchanged. Source packet SHA-256: bafc3b63f6baba271680f2eed29334603149cee7c17a714bb7b4b1a04c37d3a1. Full ZIP hash is in DELIVERY.json. No children, git, network, external communication, browser, upload, publication, shared ledger edits, or other-lane writes. Heavy jobs were serial and capped; operations.json records that not every initial short read/authoring call used the wrapper. No running jobs remain. Root reads the paper and decides.
''')
for before,after in [('frozen-inputs-before.json','frozen-inputs-after.json'),('supplemental-inputs-before.json','supplemental-inputs-after.json'),('renderer-inputs-before.json','renderer-inputs-after.json')]:
 d=json.loads((root/before).read_text());a={p:sha(Path(p)) for p in d};assert a==d;write(after,a)
write('receipts/input-integrity.json',dict(all_original_supplemental_renderer_inputs_unchanged=True,utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
print('Dossier evidence and reports prepared; frozen inputs unchanged.')
