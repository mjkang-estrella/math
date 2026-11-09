"""Write flat immutable references (absolute path, sha256, size) for every external
original this lane read or relied on. No copies are made. usage: bind_inputs.py OUT.json"""
import datetime, hashlib, json, os, sys

LANES = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes'
ROOT = '/home/mj-kang/Documents/Dev/math/openai-proof-research'
INTAKE = LANES + '/root-mathdb-circulant-13-review-intake-r467'
R382 = LANES + '/sol-mathdb-circulant-15-source-prior-review-r382'
refs = [
    (LANES + '/../AGENTS.md', 'campaign rules (read first)'),
    (ROOT + '/AGENTS.md', 'ancestor rules'),
    (LANES + '/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py', 'mandated guard'),
    (ROOT + '/sources/upstream.json', 'pinned registry snapshot id (openai/math fd4aeeb, 2026-10-08)'),
    (ROOT + '/sources/CONTENTS.md', 'pinned registry catalogue grep (no L(3,2,1) entry)'),
    (ROOT + '/sources/overview.tex', 'pinned registry overview grep'),
    (ROOT + '/sources/preprints-tree.json', 'pinned preprint path listing grep'),
    (R382 + '/http/source-v2.body', 'Holub-Kopriva arXiv 2601.12574v2 PDF (same bytes as r376 freeze)'),
    (R382 + '/http/source-v2.txt', 'r382 layout extraction of source (read: pp.2-11, refs)'),
    (R382 + '/http/cada-pdf.body', '[4] arXiv 1207.4219v2 PDF'),
    (R382 + '/http/cada-pdf.txt', '[4] extraction (read: defs, Lemma 3, Prop 2, Sec 4 Table 8)'),
    (R382 + '/http/korze-table.body', '[13] authors supplement PDF'),
    (R382 + '/http/korze-table.txt', '[13] supplement extraction (read: D(1,t) table, D(1,3) constructions)'),
]
for r, _, fs in os.walk(INTAKE):
    for f in sorted(fs):
        refs.append((os.path.join(r, f), 'r467 intake payload (validated, see logs/validate_intake.json)'))
out = []
for p, why in refs:
    p = os.path.normpath(p)
    b = open(p, 'rb').read()
    out.append({'path': p, 'sha256': hashlib.sha256(b).hexdigest(), 'size': len(b), 'role': why})
json.dump({'written_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'note': ('Consolidated binding written after reading. Freeze order: intake pre-hashed '
                    'logs/intake-prehash.sha256 (11:26:11Z) and validated before content; r382 '
                    'originals validated against r382 manifest in validate_intake before reading; '
                    'each new HTTP body hashed into http/*.meta.json at save, before reading.'),
           'refs': out}, open(sys.argv[1], 'w'), indent=1)
print(len(out))
