#!/usr/bin/env python3
"""Package sources and replay sequentially in a fresh extraction in this lane."""
import argparse
import gzip
import hashlib
import io
import json
import re
import subprocess
import sys
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
LEAN = Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
LEAN_SHA = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
MATHLIB = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib')
MATHLIB_REV = 'd13f23b723b8a846827a245b89c10fc7d3f11612'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
FORBIDDEN = re.compile(r'\b(?:sorry|admit|axiom|unsafe|native_decide|run_tac|implemented_by)\b')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_audit(path, expected):
    raw = path.read_text()
    assert not re.search(r'\b(?:error|warning):', raw), path
    reports = {}
    pattern = r"^'([^']+)' (?:depends on axioms: (\[[^\]]*\])|does not depend on any axioms)"
    for match in re.finditer(pattern, raw, re.M):
        name = match.group(1)
        axioms = set(re.findall(r'[A-Za-z_][A-Za-z0-9_.]*', match.group(2) or ''))
        assert name not in reports and axioms <= ALLOWED, (name, axioms)
        reports[name] = sorted(axioms)
    assert set(reports) == set(expected), ('audit mismatch', set(expected) ^ set(reports))
    for name in expected:
        assert re.search(r'^' + re.escape(name) + r'(?:\.\{[^}]*\})?(?:\s|:)', raw, re.M), ('missing type', name)
    return reports


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', default='verification/fresh')
    args = parser.parse_args()
    output = (ROOT / args.output).resolve()
    assert output.is_relative_to(ROOT) and not output.exists(), 'Fresh lane-local destination required.'
    assert sha(LEAN) == LEAN_SHA
    gitdir = MATHLIB / '.git'
    head = (gitdir / 'HEAD').read_text().strip()
    if head.startswith('ref: '):
        head = (gitdir / head[5:]).read_text().strip()
    assert head == MATHLIB_REV
    order = json.loads((ROOT / 'build-order.json').read_text())
    files = sorted([*(ROOT / 'formal').glob('*.lean'), ROOT / 'formal/run_lean.py', ROOT / 'formal/guard.py'], key=lambda p: p.name)
    manifest = {p.name: sha(p) for p in files}
    for path in files:
        if path.suffix == '.lean':
            assert not FORBIDDEN.search(path.read_text()), ('forbidden token', path)
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode='w', format=tarfile.USTAR_FORMAT) as archive:
        for path in files:
            data = path.read_bytes()
            member = tarfile.TarInfo(path.name)
            member.size = len(data)
            member.mode = 0o644
            member.uid = member.gid = member.mtime = 0
            archive.addfile(member, io.BytesIO(data))
    archive_path = ROOT / 'formal-source.tar.gz'
    with archive_path.open('wb') as stream:
        with gzip.GzipFile(filename='', fileobj=stream, mode='wb', mtime=0) as compressed:
            compressed.write(buffer.getvalue())
    (ROOT / 'source-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    output.mkdir(parents=True)
    source = output / 'source'
    logs = output / 'logs'
    source.mkdir()
    logs.mkdir()
    receipt = {'success': False, 'lean_sha256': sha(LEAN), 'mathlib_revision': head,
               'source_archive_sha256': sha(archive_path), 'initial_local_oleans': [], 'builds': []}

    def save():
        (output / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')

    with tarfile.open(archive_path, 'r:gz') as archive:
        for member in archive.getmembers():
            assert member.isfile() and member.name in manifest and Path(member.name).name == member.name
            (source / member.name).write_bytes(archive.extractfile(member).read())
    assert not list(source.rglob('*.olean'))
    assert {p.name: sha(p) for p in source.iterdir()} == manifest
    save()
    for module in order['modules'] + order['audits']:
        log = logs / (module + '.log')
        lean_args = [module + '.lean']
        if module in order['modules']:
            lean_args += ['-o', module + '.olean']
        with (logs / (module + '.runner.log')).open('w') as stream:
            process = subprocess.run([sys.executable, 'guard.py', str(log), *lean_args], cwd=source, stdout=stream, stderr=subprocess.STDOUT)
        stats = json.loads(log.with_suffix(log.suffix + '.json').read_text())
        receipt['builds'].append({'module': module, **stats})
        save()
        assert process.returncode == 0 and stats['exit_code'] == 0 and not stats['guard_killed'], module
        if module in order['modules']:
            assert not log.read_text(), ('nonempty proof log', module)
        print(module + ': PASS', flush=True)
    declarations = json.loads((ROOT / 'declarations.json').read_text())
    names = [entry['name'] for entry in declarations]
    receipt['new_declaration_axioms'] = parse_audit(logs / 'SourceBridgeAudit.log', names)
    inventory = (logs / 'SourceBridgeInventory.log').read_text()
    actual = set(re.findall(r'^SOURCE_BRIDGE_DECL (\S+)$', inventory, re.M))
    origins = dict(re.findall(r'^SOURCE_BRIDGE_MODULE (\S+) (\S+)$', inventory, re.M))
    safety = dict(re.findall(r'^SOURCE_BRIDGE_SAFETY (\S+) (true|false)$', inventory, re.M))
    assert actual == set(names) == set(safety)
    assert origins == {entry['name']: entry['source_module'] for entry in declarations}
    assert all(value == 'false' for value in safety.values())
    receipt['all_new_declarations_safe'] = True
    receipt['module_origin_inventory_exact'] = True
    for module in ['FiltrationAudit', 'MidpointAudit', 'OddPrimitiveAudit']:
        expected = re.findall(r'^#check (\S+)', (source / (module + '.lean')).read_text(), re.M)
        receipt[module] = parse_audit(logs / (module + '.log'), expected)
    source_checks = (logs / 'SourceChecks.log').read_text()
    assert not re.search(r'\b(?:error|warning):', source_checks)
    assert not re.search(r'(?<![A-Za-z_])sorryAx(?![A-Za-z_])', source_checks)
    receipt['final_source_hashes_unchanged'] = all(sha(source / name) == digest for name, digest in manifest.items())
    assert receipt['final_source_hashes_unchanged']
    receipt['sampled_peak_rss_kib'] = max(entry['sampled_peak_rss_kib'] for entry in receipt['builds'])
    receipt['success'] = True
    save()
    print('Fresh source-only strict replay: PASS', flush=True)


if __name__ == '__main__':
    main()
