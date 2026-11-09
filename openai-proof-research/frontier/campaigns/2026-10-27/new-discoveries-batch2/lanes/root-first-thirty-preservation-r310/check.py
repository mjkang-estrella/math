import hashlib
import json
from pathlib import Path
import sys

D = Path(__file__).resolve().parent
B = D.parent.parent
F = B.parent.parent / '2026-10-26/new-discoveries'
EXPECTED_LEDGER = '4b2b8556921bb11448e76e0653060ab89d9b2107f3be0338c238ba66038bc385'

def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

def write(name, value):
    (D / name).write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')

def build():
    inputs = [('first-ledger.json', F / 'ledger.json'),
              ('prior-context.json', B / 'prior-campaign-context.json'),
              ('accepted-index.json', B / 'lanes/root-mathdb-accepted-exclusions-r304/accepted-exclusions.json')]
    bindings = []
    for name, p in inputs:
        digest = sha(p)
        (D / name).write_bytes(p.read_bytes())
        assert sha(D / name) == digest == sha(p)
        bindings.append({'original': str(p), 'copy': name, 'sha256': digest})
    assert sha(D / 'first-ledger.json') == EXPECTED_LEDGER
    ledger = json.loads((D / 'first-ledger.json').read_text())
    prior = json.loads((D / 'prior-context.json').read_text())
    index = json.loads((D / 'accepted-index.json').read_text())
    assert ledger['accepted'] == prior['accepted']
    assert prior['first_campaign_ledger_sha256'] == EXPECTED_LEDGER
    assert {x['number'] for x in ledger['accepted']} == set(range(1,31))
    pubs = {x['number']: x for x in prior['published_papers']}
    indexed = {x['number']: x for x in index['families'] if x['number'] <= 30}
    assert set(pubs) == set(indexed) == set(range(1,31))
    packets = []
    for x in ledger['accepted']:
        n = x['number']
        p = F / x['packet']
        digest = sha(p)
        assert digest == x['packet_sha256'], n
        assert indexed[n]['packet_sha256'] == digest
        assert indexed[n]['publication'] == pubs[n], n
        assert pubs[n]['doi'] and pubs[n]['paper_url'] and pubs[n]['problem_ids']
        packets.append({'number': n, 'path': str(p), 'sha256': digest, 'bytes': p.stat().st_size})
    write('bindings.json', bindings)
    write('packets.json', packets)
    write('publication-problem-links.json', [pubs[n] for n in range(1,31)])
    write('result.json', {'ledger_sha256': EXPECTED_LEDGER, 'accepted_records_identical': 30,
                         'packets_hash_match': 30, 'publication_problem_mappings_preserved': 30,
                         'live_external_link_availability_checked': False,
                         'mathematics_reaudited': False, 'credit_added': 0})
    write('manifest.json', {p.name: sha(p) for p in sorted(D.iterdir()) if p.is_file()
                           and p.name not in {'manifest.json', 'verification-receipt.json'}})

def verify():
    manifest = json.loads((D / 'manifest.json').read_text())
    assert set(manifest) == {p.name for p in D.iterdir() if p.is_file()
                            and p.name not in {'manifest.json', 'verification-receipt.json'}}
    for n, digest in manifest.items():
        assert sha(D / n) == digest, n
    bindings = json.loads((D / 'bindings.json').read_text())
    for x in bindings:
        assert sha(Path(x['original'])) == sha(D / x['copy']) == x['sha256']
    packets = json.loads((D / 'packets.json').read_text())
    assert {p['number'] for p in packets} == set(range(1,31))
    for p in packets:
        assert sha(Path(p['path'])) == p['sha256']
    write('verification-receipt.json', {'result': 'PASS', 'manifest_files': len(manifest),
          'administrative_original_copy_bindings': len(bindings), 'unchanged_packets': len(packets),
          'live_link_availability_or_mathematical_validity_certified': False})
    print((D / 'result.json').read_text())
    print((D / 'verification-receipt.json').read_text())

if __name__ == '__main__':
    {'build': build, 'verify': verify}[sys.argv[1]]()
