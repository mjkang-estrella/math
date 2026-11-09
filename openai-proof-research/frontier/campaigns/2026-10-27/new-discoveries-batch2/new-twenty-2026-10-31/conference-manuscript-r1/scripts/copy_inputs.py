"""Copy frozen inputs into the dossier byte-identically and record a copy receipt.
   python3 -I -B scripts/copy_inputs.py RECEIPT.json"""
import hashlib, json, os, shutil, sys
NT = '..'
S = NT + '/fresh-corpus-r3/sources'
F1 = NT + '/conference-significance-review-r1/web-untrusted/f1'
R3 = NT + '/conference-primary-comparison-r3'
PF = NT + '/conference-parent-final-r1'
RF = NT + '/replay-fit-r1'
M = [  # (source, destination under dossier/)
    (RF + '/324342-replay-fit-source.zip', 'lean/324342-replay-fit-source.zip'),
    (RF + '/324342-imports.diff', 'lean/324342-imports.diff'),
    (RF + '/statement-preservation.json', 'lean/statement-preservation.json'),
    (RF + '/324342-packet.sha256', 'lean/324342-packet.sha256'),
    (NT + '/conference-mds-resume-r4/lean/ConferenceMDS324342.lean', 'lean/frozen-r4/ConferenceMDS324342.lean'),
    (NT + '/conference-mds-resume-r4/provenance/pins.json', 'lean/pins.json'),
    (S + '/1210.5725.pdf', 'sources/arxiv-1210.5725v2.pdf'),
    (S + '/1210.5725.txt', 'sources/arxiv-1210.5725v2.txt'),
    (S + '/1210.5725v1.pdf', 'sources/arxiv-1210.5725v1.pdf'),
    (S + '/1210.5725v1.txt', 'sources/arxiv-1210.5725v1.txt'),
    (S + '/web/28_Lee_Manhattan_ISIT13.pdf', 'sources/isit2013-author-copy.pdf'),
    (S + '/web/28_Lee_Manhattan_ISIT13.txt', 'sources/isit2013-author-copy.txt'),
    (S + '/web/arxiv-abs-1210.5725.html', 'sources/arxiv-abs-1210.5725.html'),
    (S + '/receipts.json', 'sources/receipts/fresh-corpus-r3-receipts.json'),
    (NT + '/conference-mds-resume-r4/web-untrusted/r4/IT13.pdf', 'sources/tit2013-author-posted-ieee-copy.pdf'),
    (NT + '/conference-mds-resume-r4/web-untrusted/r1/b7f762b1.body', 'sources/receipts/crossref-tit-10.1109-TIT.2013.2268156.json'),
    (NT + '/conference-mds-resume-r4/logs/fetch-r1.log', 'sources/receipts/r4-fetch-r1.log'),
    (R3 + '/web-untrusted/r1/ag-crossref.body', 'sources/receipts/crossref-ag-10.1109-18.930940.json'),
    (R3 + '/web-untrusted/r1/gg-crossref.body', 'sources/receipts/crossref-gg-10.1109-ISIT.2008.4595330.json'),
    (R3 + '/receipts/http-receipts.jsonl', 'sources/receipts/r3-http-receipts.jsonl'),
    (NT + '/conference-fidelity-review-r1/sources/source-receipts.json', 'sources/receipts/fidelity-r1-source-receipts.json'),
    (NT + '/conference-significance-review-r1/work/fetch.log', 'sources/receipts/significance-r1-fetch.log'),
    (R3 + '/work/it13-render-sha256.txt', 'sources/tit2013-rendering/it13-render-sha256.txt'),
    (R3 + '/scripts/rebuild_pages.py', 'sources/tit2013-rendering/rebuild_pages.py'),
    (R3 + '/scripts/orphan_page.py', 'sources/tit2013-rendering/orphan_page.py'),
    (R3 + '/scripts/pdf_objs.py', 'sources/tit2013-rendering/pdf_objs.py'),
    (R3 + '/work/it13-rebuild/p6715.png', 'sources/tit2013-rendering/p6715.png'),
    (R3 + '/work/it13-rebuild/q11.png', 'sources/tit2013-rendering/p6712-q11.png'),
    (R3 + '/work/it13-rebuild/q04.png', 'sources/tit2013-rendering/p6722-q04.png'),
    (R3 + '/work/it13-rebuild/r.txt', 'sources/tit2013-rendering/repaired-text-r.txt'),
    (F1 + '/1311.2637.txt', 'sources/secondary/armario-frau-arxiv-1311.2637v1.txt'),
    (F1 + '/ball-jems.txt', 'sources/secondary/ball-author-revised-2012-01-17.txt'),
    (F1 + '/2402.11074.txt', 'sources/secondary/araya-et-al-arxiv-2402.11074v1.txt'),
    (F1 + '/hm.txt', 'sources/secondary/harada-munemasa-arxiv-1011.5382v2.txt'),
    (NT + '/held-reopen-r1/324342.raw.jsonl', 'mathdb/held-reopen-r1-324342.raw.jsonl'),
    (NT + '/held-reopen-r1/literal-bindings.json', 'mathdb/held-reopen-r1-literal-bindings.json'),
    (NT + '/held-reopen-r1/independent-conference-check.json', 'receipts/held-reopen-r1-independent-conference-check.json'),
    (PF + '/replay-result.json', 'receipts/root-replay/replay-result.json'),
    (PF + '/registry-refresh.json', 'receipts/root-replay/registry-refresh.json'),
    (PF + '/root-independent-check.txt', 'receipts/root-replay/root-independent-check.txt'),
    (PF + '/root-replay.out', 'receipts/root-replay/root-replay.out'),
    (PF + '/rootcheck/replay.sh', 'receipts/root-replay/rootcheck-replay.sh'),
    (PF + '/rootcheck/RootMeta.lean', 'receipts/root-replay/RootMeta.lean'),
    (PF + '/replay/packet/extraction-receipt.json', 'receipts/root-replay/extraction-receipt.json'),
    (PF + '/replay/packet/metadata.tsv', 'receipts/root-replay/metadata.tsv'),
    (RF + '/RESULT.md', 'receipts/replay-fit-r1/RESULT.md'),
    (RF + '/REPRODUCE.md', 'receipts/replay-fit-r1/REPRODUCE.md'),
    (RF + '/324342-timings.md', 'receipts/replay-fit-r1/324342-timings.md'),
    (RF + '/final324342.sh', 'receipts/replay-fit-r1/final324342.sh'),
    (RF + '/extract324342.py', 'receipts/replay-fit-r1/extract324342.py'),
    (RF + '/package324342.py', 'receipts/replay-fit-r1/package324342.py'),
    (NT + '/held-reopen-root-ruling-r1.json', 'reviews/held-reopen-root-ruling-r1.json'),
    (NT + '/held-reopen-r1/REVIEW.md', 'reviews/held-reopen-r1/REVIEW.md'),
    (NT + '/held-reopen-r1/review.json', 'reviews/held-reopen-r1/review.json'),
    (NT + '/conference-fidelity-review-r1/REVIEW.md', 'reviews/conference-fidelity-review-r1/REVIEW.md'),
    (NT + '/conference-fidelity-review-r1/review.json', 'reviews/conference-fidelity-review-r1/review.json'),
    (NT + '/conference-fidelity-review-r1/independent-checks/witness.py', 'reviews/conference-fidelity-review-r1/witness.py'),
    (NT + '/conference-fidelity-review-r1/independent-checks/witness.json', 'reviews/conference-fidelity-review-r1/witness.json'),
    (NT + '/conference-significance-review-r1/REVIEW.md', 'reviews/conference-significance-review-r1/REVIEW.md'),
    (NT + '/conference-significance-review-r1/review.json', 'reviews/conference-significance-review-r1/review.json'),
    (NT + '/conference-significance-objections-r1.json', 'reviews/conference-significance-objections-r1.json'),
    (NT + '/conference-significance-adjudication-r2/REVIEW.md', 'reviews/conference-significance-adjudication-r2/REVIEW.md'),
    (NT + '/conference-significance-adjudication-r2/review.json', 'reviews/conference-significance-adjudication-r2/review.json'),
    (NT + '/conference-significance-adjudication-r2/work/sparse_combo_diag.json', 'reviews/conference-significance-adjudication-r2/sparse_combo_diag.json'),
    (NT + '/conference-adjudication-parent-integration-r2.json', 'reviews/conference-adjudication-parent-integration-r2.json'),
    (R3 + '/REVIEW.md', 'reviews/conference-primary-comparison-r3/REVIEW.md'),
    (R3 + '/review.json', 'reviews/conference-primary-comparison-r3/review.json'),
    (R3 + '/work/ag_arith.json', 'reviews/conference-primary-comparison-r3/ag_arith.json'),
    (NT + '/conference-primary-parent-integration-r3.json', 'reviews/conference-primary-parent-integration-r3.json'),
    (NT + '/conference-parent-revision-r1/SUMMARY.md', 'history/conference-parent-revision-r1/SUMMARY.md'),
    (NT + '/conference-parent-revision-r1/PROOF.md', 'history/conference-parent-revision-r1/PROOF.md'),
    (NT + '/conference-parent-revision-r1/review.json', 'history/conference-parent-revision-r1/review.json'),
    (NT + '/conference-mds-resume-r4/SUMMARY.md', 'history/conference-mds-resume-r4/SUMMARY.md'),
    (NT + '/conference-mds-resume-r4/PROOF.md', 'history/conference-mds-resume-r4/PROOF.md'),
    (NT + '/conference-mds-resume-r4/results.json', 'history/conference-mds-resume-r4/results.json'),
    (NT + '/conference-mds-resume-r4/MANIFEST.json', 'history/conference-mds-resume-r4/MANIFEST.json'),
    (NT + '/conference-mds-resume-r4/data/cex_20.json', 'history/conference-mds-resume-r4/data/cex_20.json'),
    (NT + '/conference-mds-resume-r4/data/cex20_certificate.json', 'history/conference-mds-resume-r4/data/cex20_certificate.json'),
    (NT + '/conference-mds-resume-r4/data/lean_cert.json', 'history/conference-mds-resume-r4/data/lean_cert.json'),
    (NT + '/conference-mds-resume-r4/data/verify_from_scratch.json', 'history/conference-mds-resume-r4/data/verify_from_scratch.json'),
    (NT + '/conference-mds-resume-r4/logs/low_weight_count.log', 'history/conference-mds-resume-r4/logs/low_weight_count.log'),
    (NT + '/conference-mds-resume-r4/logs/verify_from_scratch.log', 'history/conference-mds-resume-r4/logs/verify_from_scratch.log'),
    (NT + '/conference-mds-resume-r4/logs/paley_control.log', 'history/conference-mds-resume-r4/logs/paley_control.log'),
    (NT + '/conference-mds-resume-r4/logs/gs_reconstruct.log', 'history/conference-mds-resume-r4/logs/gs_reconstruct.log'),
    (NT + '/conference-mds-resume-r4/scripts/verify_from_scratch.py', 'history/conference-mds-resume-r4/scripts/verify_from_scratch.py'),
    (NT + '/conference-mds-resume-r4/scripts/low_weight_count.py', 'history/conference-mds-resume-r4/scripts/low_weight_count.py'),
    (NT + '/conference-mds-resume-r4/scripts/paley_control.py', 'history/conference-mds-resume-r4/scripts/paley_control.py'),
    (NT + '/conference-mds-resume-r4/scripts/gs_reconstruct.py', 'history/conference-mds-resume-r4/scripts/gs_reconstruct.py'),
]
for d in ('ConferenceMDS324342.lean', 'Controls.lean', 'Audit.lean', 'MetadataAudit.lean'):
    M.append(('tmp/lean-extract-test/' + d, 'lean/packet/' + d))
for n in sorted(os.listdir(PF + '/logs')):
    M.append((PF + '/logs/' + n, 'receipts/root-replay/logs/' + n))
for n in sorted(os.listdir(RF + '/logs')):
    if n.startswith('final324342-'):
        M.append((RF + '/logs/' + n, 'receipts/replay-fit-r1/logs/' + n))
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
rec = []
for s, d in M:
    dst = os.path.join('dossier', d)
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    if os.path.exists(dst):
        assert sha(dst) == sha(s), dst
    else:
        shutil.copyfile(s, dst)
    h = sha(s)
    assert sha(dst) == h, d
    rec.append({'source': os.path.normpath(os.path.abspath(s)), 'dossier_path': d, 'sha256': h, 'bytes': os.path.getsize(s)})
json.dump({'copies': len(rec), 'all_byte_identical': True, 'files': rec}, open(sys.argv[1], 'w'), indent=1)
print(len(rec), 'files copied byte-identically')
