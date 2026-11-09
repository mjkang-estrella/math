"""Copy 355956-only evidence verbatim (hash identity recorded) and write labelled
extracts of joint files (which also cover the HELD 355701 candidate) so that no
355701 material is bundled.  Originals stay untouched and hash-bound in frozen-*.json."""
import hashlib, json, pathlib, re, shutil
L = pathlib.Path(__file__).resolve().parents[1]
B = L.parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
COPY = {
 'evidence/author': ['expanded-corpus-r49/' + x for x in [
   'scripts/yip_fast.py', 'scripts/yip_search.py', 'scripts/yip_sweep.sh', 'scripts/gen_yip_lean.py',
   'lean/Audit.lean', 'lean/certificates.json', 'logs/audit.log', 'logs/replay-audit-yip.log',
   'logs/yip-sweep-all.jsonl', 'logs/yip-sweep-lane0.jsonl', 'logs/yip-sweep-lane1.jsonl', 'logs/yip-case-list.txt',
   'logs/yip-small.log', 'logs/yip-3-4.log', 'logs/yip-3-8.log', 'logs/yipfast-3-8.log']],
 'evidence/technical': ['paley-config-fidelity-review-r1/' + x for x in [
   'flags-Yip355956.log', 'origin-Yip355956.log', 'negative-FalseYip.log', 'negative-FalseYipFinite.log']],
 'evidence/root': ['paley-config-parent-integration-r1/full-types-Yip.log'],
 'evidence/source': ['paley-config-source-review-r2/' + x for x in [
   'checks/yip-verify.json', 'scripts/yip_verify.py', 'logs/yip-verify.log']],
}
ident = {'verbatim_copies': {}, 'extracts': {}, 'not_copied_reference_only': {}}
for dest, srcs in COPY.items():
    (L / dest).mkdir(parents=True, exist_ok=True)
    for s in srcs:
        src = B / s
        out = L / dest / src.name
        shutil.copyfile(src, out)
        assert sha(src) == sha(out)
        ident['verbatim_copies'][str(out.relative_to(L))] = {'source': s, 'sha256': sha(out)}

def extract(name, source, payload):
    out = L / 'evidence/extracts' / name
    out.parent.mkdir(parents=True, exist_ok=True)
    doc = {'DERIVED_EXTRACT': True, 'note': 'Selected 355956 content of a joint file; the original also covers the '
           'HELD candidate 355701, which is excluded from this dossier. Original unchanged; see source_sha256.',
           'source': source, 'source_sha256': sha(B / source), 'content': payload}
    out.write_text(json.dumps(doc, indent=1, ensure_ascii=False))
    ident['extracts'][str(out.relative_to(L))] = {'source': source, 'source_sha256': doc['source_sha256'], 'sha256': sha(out)}

tr = json.loads((B / 'paley-config-fidelity-review-r1/review.json').read_text())
extract('technical-review-355956.json', 'paley-config-fidelity-review-r1/review.json',
        {k: tr[k] for k in ('utc', 'role', 'packet_sha256', 'integrity_bindings', 'manifest_bindings')} | {'355956': tr['results']['355956']})
md = (B / 'paley-config-fidelity-review-r1/REVIEW.md').read_text()
extract('technical-review-355956-section.json', 'paley-config-fidelity-review-r1/REVIEW.md',
        md[md.index('## 355956: exact source'):md.index('## 355701: exact source')])
adj = json.loads((B / 'paley-config-parent-integration-r1/ADJUDICATION.json').read_text())
extract('root-adjudication-355956.json', 'paley-config-parent-integration-r1/ADJUDICATION.json',
        {k: adj[k] for k in ('utc', 'frozen_bindings_reverified', 'evidence_format_adjudication', 'root_replay', 'credit')}
        | {'root_technical_verdict_355956': adj['root_technical_verdicts']['355956']})
sr = json.loads((B / 'paley-config-source-review-r2/review.json').read_text())
extract('source-review-355956.json', 'paley-config-source-review-r2/review.json',
        {k: sr[k] for k in ('review', 'utc_completed', 'reviewer', 'registries') if k in sr} | {'355956': sr['355956']})
smd = (B / 'paley-config-source-review-r2/REVIEW.md').read_text()
extract('source-review-355956-section.json', 'paley-config-source-review-r2/REVIEW.md',
        smd[smd.index('## 355956'):smd.index('## 355701')])
ws = json.loads((B / 'paley-config-source-review-r2/logs/web-searches.json').read_text())
extract('source-review-web-searches-355956.json', 'paley-config-source-review-r2/logs/web-searches.json',
        {'tool': ws.get('tool'), 'queries': [q for q in ws['queries'] if re.search(r'yip|paley|subfield|clique', json.dumps(q), re.I)]})
for s, why in {
    'paley-config-fidelity-review-r1/full-origin-Yip355956.log': 'incomplete 117 MB unabridged proof dump (CPU cap); superseded by root adjudication; reference only',
    'expanded-corpus-r49/proof-packet.zip': 'author packet; also contains 355701 material',
    'expanded-corpus-r49/PROOF.md': 'author ordinary proofs for 355956 and 355701 (joint)',
    'expanded-corpus-r49/SUMMARY.md': 'joint author summary',
    'expanded-corpus-r49/PRIOR-ART.md': 'joint author prior-art notes',
    'expanded-corpus-r49/ATTEMPTS.md': 'joint author attempts',
    'expanded-corpus-r49/replay-receipt.json': 'joint author replay receipt',
}.items():
    ident['not_copied_reference_only'][s] = {'sha256': sha(B / s), 'reason': why}
(L / 'receipts').mkdir(exist_ok=True)
(L / 'receipts/copied-evidence-identity.json').write_text(json.dumps(ident, indent=1))
print(len(ident['verbatim_copies']), 'copies,', len(ident['extracts']), 'extracts')
