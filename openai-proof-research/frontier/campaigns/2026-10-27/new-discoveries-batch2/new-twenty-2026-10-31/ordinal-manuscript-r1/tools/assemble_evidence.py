"""Write labelled 366371-only extracts of joint frozen files and a copy-identity receipt.
Usage: python3 -I tools/assemble_evidence.py"""
import hashlib, json, pathlib
L = pathlib.Path(__file__).resolve().parents[1]; B = L.parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
R, V = 'expanded-corpus-r61', 'r61-candidates-review-r1'
ex = L / 'evidence/extracts'; ex.mkdir(parents=True, exist_ok=True)
hdr = 'LABELLED EXTRACT (366371 only) of frozen file {} (sha256 {}); 366834 content omitted (root HOLD).'
# review.json key 366371
src = B / V / 'review.json'; d = json.loads(src.read_text())
(ex / 'review-366371.json').write_text(json.dumps({'_extract_note': hdr.format(f'{V}/review.json', sha(src)), '366371': d['366371']}, indent=1))
# REVIEW.md: 366371 section only
src = B / V / 'REVIEW.md'; t = src.read_text()
sec = t[t.index('## MathDB 366371'):t.index('## Files')]
(ex / 'REVIEW-366371-section.md').write_text('<!-- ' + hdr.format(f'{V}/REVIEW.md', sha(src)) + ' -->\n\n' + sec)
# root adjudication key 366371
src = B / 'r61-candidates-root-adjudication-r1.json'; d = json.loads(src.read_text())
(ex / 'root-adjudication-366371.json').write_text(json.dumps({'_extract_note': hdr.format('r61-candidates-root-adjudication-r1.json', sha(src)),
                                                              'utc': d['utc'], 'review': d['review'], 'review_sha256': d['review_sha256'], '366371': d['366371'], 'credit': d['credit']}, indent=1))
# author replay-result: OrdinalLine module only
src = B / R / 'replay/replay-result.json'; d = json.loads(src.read_text())
keep = {k: d[k] for k in ('status', 'utc', 'strict', 'leanchecker', 'allowed_axioms', 'lean_binary_sha256', 'leanchecker_binary_sha256', 'environment', 'trust_limit')}
keep['OrdinalLine'] = d['modules']['OrdinalLine']; keep['OrdinalLine.lean_sha256'] = d['source_sha256']['OrdinalLine.lean']
(ex / 'author-replay-OrdinalLine.json').write_text(json.dumps({'_extract_note': hdr.format(f'{R}/replay/replay-result.json', sha(src)), **keep}, indent=1))
# copy identity for verbatim evidence and sources
ident = {}
pairs = {'proof/OrdinalLine.lean': f'{R}/formal/OrdinalLine.lean', 'evidence/author/PROOF-366371.md': f'{R}/PROOF-366371.md',
         'evidence/review/RevAuditOrdinalLine.lean': f'{V}/fresh/RevAuditOrdinalLine.lean'}
for sub, root in (('evidence/author/scripts', f'{R}/scripts'), ('evidence/author/outputs', f'{R}/outputs'), ('evidence/author/logs', f'{R}/logs'),
                  ('evidence/review/scripts', f'{V}/scripts'), ('evidence/review/logs', f'{V}/logs'), ('evidence/review/sources', f'{V}/sources')):
    for p in sorted((L / sub).iterdir()):
        pairs[f'{sub}/{p.name}'] = f'{root}/{p.name}'
for n in json.loads((L / 'sources/RECEIPTS.json').read_text())['files']:
    pairs[f'sources/{n}'] = json.loads((L / 'sources/RECEIPTS.json').read_text())['files'][n]['copied_from']
for mine, theirs in sorted(pairs.items()):
    a, b = sha(L / mine), sha(B / theirs)
    assert a == b, mine
    ident[mine] = {'sha256': a, 'frozen_source': theirs}
(L / 'receipts/copied-evidence-identity.json').write_text(json.dumps({'all_identical': True, 'count': len(ident), 'files': ident}, indent=1))
for p in sorted(ex.iterdir()):
    assert 'Caterpillar366834' not in p.read_text() and 'caterpillar' not in p.read_text().lower(), p
print(len(ident), 'verbatim copies identical;', len(list(ex.iterdir())), 'extracts')
