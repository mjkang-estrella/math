from pathlib import Path
import hashlib, json, shutil

B = Path(__file__).resolve().parents[2]
C = B / 'candidates/jacobi-shifted-denominator'
R = B / 'lanes/sol-jacobi-full-final-review-r1'

def replace(name, old, new):
    p = C / name
    s = p.read_text()
    assert s.count(old) == 1, (name, old)
    p.write_text(s.replace(old, new))

replace('main.tex', "Area's published binomial-sum valuation", "Area's public-preprint binomial-sum valuation")
replace('main.tex', 'This is preparation for independent final review; candidate credit is zero.',
        'Independent final review and source-only replay have passed within the documented review limits.')
replace('main.tex', r'''This packet is an implementation and manuscript preparation, not independent acceptance. The proposed outcome is one family: the full shifted all-coefficient law. Candidate credit remains \textbf{0}; campaign counts remain 2/30 additional and 32/60 total. A distinct independent final review and current novelty adjudication remain pending. The preliminary source/ordinary-math review supported investment with a bounded literature screen; it did not establish worldwide priority.''',
        r'''Independent final review passed source fidelity, mathematics, the literal certificate, the manuscript and a fresh extracted replay. The counted proposition is one family: the full shifted all-coefficient law. The separate root acceptance record binds the final archive and accounting. The current literature and public-proof screen is bounded; no worldwide priority is established. Classical Riccati methods, binary arithmetic, normalized primitive inversion and the known binomial valuation receive no separate novelty credit.''')
replace('README.md', '''Research candidate preparation, not independent review or acceptance. One family;
Jacobi credit 0. Counts remain 2/30 additional, 32/60 total. Distinct independent
final review and current novelty/subsumption adjudication remain root's gates.''',
'''Independent final review passed all gates within documented limits. This packet
contains one family: the full shifted all-coefficient denominator law. The
separate root acceptance record binds this final archive and its accounting.
The final review and its receipt are retained under provenance/.''')
replace('README.md', '''is not a current final acceptance. Primary bodies/titles/versions are in primary/.''',
'''is historical evidence, supplemented by provenance/final-review.md. Primary
bodies/titles/versions are in primary/.''')
replace('README.md', 'From this lane, with a destination that does not exist:',
'''From this extracted packet, pass the final archive path and a destination that
does not exist (the archive itself is external to its payload):''')
replace('README.md', 'python3 scripts/replay.py packet/jacobi-shifted-source-proof.zip verification/another-fresh-replay',
        'python3 scripts/replay.py /path/to/2026-remark38-jacobi-shifted-denominator-proof.zip /path/to/new-replay')
replace('README.md', '''python3 scripts/build_packet.py packet/regenerated.zip
cmp packet/jacobi-shifted-source-proof.zip packet/regenerated.zip''',
'''python3 scripts/build_packet.py /path/to/regenerated.zip
cmp /path/to/2026-remark38-jacobi-shifted-denominator-proof.zip /path/to/regenerated.zip''')
replace('SUMMARY.md', '''Preparation only: Jacobi credit 0, counts 2/30 and 32/60 unchanged. One proposed
family. Distinct independent final review, current novelty/subsumption review,
root integration and acceptance remain pending.''',
'''Independent final review and current bounded novelty/subsumption adjudication
passed. Root final packaging changes only status/publication wording and adds
review evidence; all mathematical sources remain unchanged. One family only.
The separate root acceptance record supplies the final archive-bound decision.''')
replace('PROOF.md', 'Research candidate; preparation only, credit 0.',
        'Independently reviewed research theorem; final accounting is in the separate root acceptance record.')
p=C/'PROOF.md';s=p.read_text();start=s.index('Final independent review/current novelty adjudication remain pending.')
print('OLD PROOF STATUS',repr(s[start:]))
s=s[:start]+'''Independent final review passed all gates within its documented limits. Final
archive-bound acceptance and accounting are recorded separately by root. Finite
checks are falsification diagnostics, not the proof. One family only; classical
helpers and the original-variable law receive no separate credit. No analytic
phase identification or worldwide priority claim is made.
'''
p.write_text(s)
for src,dst in [('review.md','final-review.md'),('provenance.json','final-review-provenance.json'),
                ('fresh-replay/extraction-receipt.json','final-review-extraction-receipt.json')]:
    shutil.copyfile(R/src,C/'provenance'/dst)
original=json.loads((Path(__file__).parent/'reviewed-payload-manifest.json').read_text())
unchanged={n:h for n,h in original.items() if n.startswith('formal/') or n.startswith('scripts/') or n in ['component.json','pins.json','FORMAL-MAP.md']}
for n,h in unchanged.items(): assert hashlib.sha256((C/n).read_bytes()).hexdigest()==h,n
(C/'provenance/postreview-changes.json').write_text(json.dumps({
    'reviewed_archive_sha256':'c4853d632e2c3a0dbf832fac6f84eee37f022e4655c415dce4b3e3a112510d14',
    'changes':'Status prose and published -> public-preprint wording only; added independent final review evidence; rebuilt PDF/render/manifest. No mathematical source or proof script changes.',
    'unchanged_formal_and_verifier_hashes':unchanged,
    'accounting':'Separate root acceptance record; no archive hash stored inside its own payload.'
},indent=2,sort_keys=True)+'\n')
