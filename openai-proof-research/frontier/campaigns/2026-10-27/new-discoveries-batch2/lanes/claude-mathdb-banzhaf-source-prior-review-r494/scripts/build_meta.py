"""Build bindings.json (flat original refs) from input-freeze.tsv and fetch-log.tsv; no network."""
import json, os, sys
lane = sys.argv[1]
B = os.path.dirname(os.path.dirname(lane))
inputs = []
for line in open(os.path.join(lane, 'input-freeze.tsv')):
    sha, size, rel = line.rstrip('\n').split('\t')
    e = {'path_from_batch': rel, 'sha256': sha, 'size': int(size)}
    pre = 'lanes/root-mathdb-three-candidate-intake-r493/frozen/claude-mathdb-primary-qualified-breadth-r480/'
    if rel.startswith(pre):
        e['original_path_from_batch'] = 'lanes/claude-mathdb-primary-qualified-breadth-r480/' + rel[len(pre):]
    inputs.append(e)
fetched = []
for line in open(os.path.join(lane, 'fetch-log.tsv')):
    t, url, code, ctype, final, sha, size, path = line.rstrip('\n').split('\t')
    present = os.path.exists(os.path.join(lane, path))
    fetched.append({'utc': t, 'url': url, 'http_status': int(code), 'content_type': ctype, 'final_url': final,
                    'sha256': sha, 'size': int(size), 'lane_path': path, 'retained': present,
                    'note': None if present else 'deleted after byte-identical cmp with retained r480 PDF (see failures D01)'})
out = {'lane': 'claude-mathdb-banzhaf-source-prior-review-r494', 'batch_root': 'frontier/campaigns/2026-10-27/new-discoveries-batch2',
       'input_freeze_utc': open(os.path.join(lane, 'input-freeze-time.txt')).read().strip(),
       'inputs': inputs, 'fetched': fetched,
       'derived': [{'lane_path': 'derived/' + f, 'from': f.split('.layout')[0] if '.layout' in f else f, 'tool': 'pdftotext 26.01.0 -layout' if 'layout' in f else 'pdfinfo 26.01.0'}
                   for f in sorted(os.listdir(os.path.join(lane, 'derived'))) if f != 'pdftotext.stderr'],
       'equalities': ['retained r480 1801.08029.pdf == fresh arxiv.org/pdf/1801.08029v2 (cmp)',
                      'retained r480 1801.08029.txt == pdftotext -layout of retained PDF (sha 6a9432d9...)'],
       'mathdb_requests': 0, 'upstream_verifiers_executed': 0}
json.dump(out, open(os.path.join(lane, 'bindings.json'), 'w'), indent=1)
print('inputs', len(inputs), 'fetched', len(fetched))
