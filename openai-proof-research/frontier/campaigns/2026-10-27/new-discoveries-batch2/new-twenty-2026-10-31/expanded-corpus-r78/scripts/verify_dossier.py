from pathlib import Path
import json, hashlib, datetime, collections, zipfile, re
D = Path(__file__).resolve().parents[1]; sha = lambda b: hashlib.sha256(b).hexdigest()
x = json.loads((D / 'results.json').read_text()); ids = json.loads((D / 'reservation.json').read_text())['ids']
assert set(x) == set(map(str, ids)) and len(x) == 40
for i, v in x.items():
    raw = (D / f'raw/{i}.jsonl').read_bytes(); assert raw.endswith(b'\n'); assert sha(raw) == v['provenance']['raw_sha256']
    assert sha(v['statement'].encode()) == v['provenance']['statement_utf8_sha256']
    chunk = Path(v['provenance']['chunk']).read_bytes()
    assert sha(chunk) == v['provenance']['chunk_sha256']
    assert chunk.splitlines(keepends=True)[v['provenance']['line_1based'] - 1] == raw
nrec = 0
for f in (D / 'sources').glob('*.receipt.json'):
    a = json.loads(f.read_text())
    if 'sha256' in a: assert sha(Path(a['path']).read_bytes()) == a['sha256'], f; nrec += 1
receipts = {n: json.loads((D / f'logs/{n}.receipt.json').read_text()) for n in ['lean-B7', 'fresh-bsymbol', 'fresh-kernel', 'fresh-audit', 'fresh-kernel-fresh']}
assert all(receipts[n]['returncode'] == 0 for n in ['lean-B7', 'fresh-bsymbol', 'fresh-kernel', 'fresh-audit'])
assert (D / 'logs/lean-B7.log').read_text().strip() == '' and (D / 'logs/fresh-bsymbol.log').read_text().strip() == ''
assert 'replaying BSymbol' in (D / 'logs/fresh-kernel.log').read_text()
audit = (D / 'logs/fresh-audit.log').read_text(); rows = [l for l in audit.splitlines() if l.startswith('INVENTORY|')]
assert len(rows) == 157 and 'AUDITED_LOCAL_DECLARATIONS|157' in audit
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for r in rows:
    parts = r.split('|'); assert parts[4] == 'false' and parts[3] != 'axiom'
    ax = [a.strip() for a in parts[5].strip('[]').split(',') if a.strip()]; assert set(ax) <= allowed, r
assert "'BSym334207.dzg_conjecture2' depends on axioms: [propext, Classical.choice, Quot.sound]" in audit
src = (D / 'formal/BSymbol.lean').read_bytes(); assert src == (D / 'fresh-replay/BSymbol.lean').read_bytes()
toks = re.findall(r'[A-Za-z_]+', src.decode())
assert not any(w in toks for w in ['sorry', 'admit', 'axiom', 'unsafe', 'native_decide', 'ofReduceBool', 'implemented_by', 'extern'])
BIN = Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin')
zp = D / '334207-proof-source.zip'
with zipfile.ZipFile(zp, 'w', zipfile.ZIP_DEFLATED) as z:
    for f in ['formal/BSymbol.lean', 'fresh-replay/Audit.lean', 'LEAN-PACKET-334207.md', 'BSYMBOL-ORDINARY-PROOF.md']:
        info = zipfile.ZipInfo(f, date_time=(2026, 11, 1, 0, 0, 0)); z.writestr(info, (D / f).read_bytes())
result = {'archived_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'status': 'strict_fresh_build_leanchecker_module_replay_full_local_audit_PASS',
          'endpoint': ['BSym334207.dzg_conjecture2', 'BSym334207.dzg_conjecture2_field'],
          'local_declarations': len(rows), 'axioms': sorted(allowed), 'receipts': receipts,
          'leanchecker_fresh_mode': 'attempted; killed by the 120 s CPU cap (returncode -9); not claimed',
          'binaries': {n: sha((BIN / n).read_bytes()) for n in ['lean', 'leanchecker']},
          'lean_source_sha256': sha(src), 'expected_mathlib_revision': 'd13f23b723b8a846827a245b89c10fc7d3f11612',
          'dependency_trust': 'Cached upstream oleans; no source-to-olean attestation or full upstream rebuild. Sampled RSS caps, not cgroup/transient-peak guarantees.',
          'registries': {'openai_math_HEAD': '4eaee87548250b2682affda7d05d947c05554bae (21:50 and 23:16 UTC 2026-11-01)',
                         'omega_HEAD': 'e307ede5b6d5d591f8bc44a4ec150d302e7f31a6 (21:50 UTC); 6e37b782cf6cfe60366783f4272ac2ab8645a3e6 (23:16 UTC recheck); full D5/Problems trees fetched both times; no b-symbol/MDS path (path screen)'},
          'source_receipts_hash_checked': nrec, 'packet_sha256': sha(zp.read_bytes()),
          'accepted_credit': 0, 'counts_unchanged': True,
          'outcomes': dict(collections.Counter(v['outcome'] for v in x.values()))}
(D / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
manifest = {str(f.relative_to(D)): sha(f.read_bytes()) for f in sorted(D.rglob('*')) if f.is_file() and f.name != 'SHA256SUMS.json' and '__pycache__' not in str(f) and f.suffix not in ['.olean', '.ilean', '.trace']}
(D / 'SHA256SUMS.json').write_text(json.dumps(manifest, indent=1) + '\n')
print(result['status'], result['local_declarations'], result['outcomes'], 'files', len(manifest), 'receipts', nrec)
