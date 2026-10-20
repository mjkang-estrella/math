#!/usr/bin/env python3
"""Independent parent clean-extraction/reproduction/reassembly of local release."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[4]
BASE = PROJECT / 'frontier/campaigns/2026-10-14'
ROOT = BASE / 't088p133-release-v1'
DRAFT = BASE / 't088p133-manuscript-r2'
ANCHORS = {
    'final': '6e0fef720ba9e2bc067ce3fcf334c36eb19c7f738c7750d50873b706a8002652',
    'manifest': '018d81cc1895f6fdaa4c2429403b2811e2f7b2428df60696ca6497e4f5e22d95',
    'report': 'd6238a8ce2b7fa19f7ed6482bf5548fd1ab3477a338a433f5956ab698464507c',
    'archive': '0248221680c2c06a7031c98105b837562b5f184bab5c0bbdbde955f1b36ee096',
}
NAMES = {'final': 'FINAL.json', 'manifest': 'MANIFEST.json', 'report': 'REPORT.md', 'archive': 'release.zip'}
PDF_SHA = 'c4e15a10f86623abe2919c36f4863971cea611d705dd3bcbc9684cff260a8647'
LEAN = PROJECT.parent / 'dlp-research/.tools/lean-4.34.1-linux/bin/lean'
CACHE = BASE / 'formal/.lake/packages'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def record(p):
    s = p.lstat()
    d = {'mode': stat.S_IMODE(s.st_mode), 'kind': 'dir', 'links': None}
    if stat.S_ISLNK(s.st_mode):
        d.update(kind='link', links=s.st_nlink, target=str(p.readlink()))
    elif stat.S_ISREG(s.st_mode):
        d.update(kind='file', links=s.st_nlink, bytes=s.st_size, sha256=sha(p))
    else:
        assert stat.S_ISDIR(s.st_mode), p
    return d


def snap(root):
    return {str(p.relative_to(root)): record(p) for p in root.rglob('*')}


def run(args, label):
    p = subprocess.run(args, text=True, capture_output=True,
                       env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
    (HERE / (label + '.log')).write_text(p.stdout + p.stderr)
    assert p.returncode == 0, (args, p.returncode, p.stderr)
    return {'exit': p.returncode, 'stdout': p.stdout, 'stderr': p.stderr}


def anchored_args():
    args = []
    for k, v in ANCHORS.items():
        args += ['--' + k, str(ROOT / NAMES[k]), '--' + k + '-sha256', v]
    return args


def main():
    # Standard-library trust bootstrap precedes execution of every shipped writer.
    for k, name in NAMES.items():
        p = ROOT / name
        assert p.is_file() and not p.is_symlink() and p.stat().st_nlink == 1 and sha(p) == ANCHORS[k]
    final = json.loads((ROOT / 'FINAL.json').read_text())
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    public = ROOT / 'public-source'
    assert sha(public / 'verify.py') == final['verifier_sha256']
    for rel, m in manifest['files'].items():
        assert sha(public / rel) == m['sha256'] and (public / rel).stat().st_size == m['bytes']
    assert len(manifest['files']) == 75 and len(manifest['directories']) == 19
    assert (public / 'MANIFEST.json').read_bytes() == (ROOT / 'MANIFEST.json').read_bytes()
    assert sha(ROOT / 'verification/MANIFEST.json') == final['verification_manifest_sha256']
    evidence = json.loads((ROOT / 'verification/MANIFEST.json').read_text())['files']
    assert len(evidence) == 13
    for rel, m in evidence.items():
        p = ROOT / 'verification' / rel
        assert p.stat().st_nlink == 1 and sha(p) == m['sha256'] and p.stat().st_size == m['bytes']
    original_before = json.loads((ROOT / 'work/originals-before.json').read_text())
    assert len(original_before) == 8 and sum(map(len, original_before.values())) == 9519
    for name, state in original_before.items():
        assert snap(BASE / name) == state, name
    release_before = snap(ROOT)
    named = json.loads((ROOT / 'work/named-parent-before.json').read_text())
    assert len(named) == 12 and all(sha(Path(p)) == h for p, h in named.items())
    assembly = json.loads((public / 'assembly-map.json').read_text())
    assert len(assembly['copied']) == 68 and len(assembly['generated']) == 6
    assert set(assembly['copied']) | set(assembly['generated']) | {'assembly-map.json'} == set(manifest['files'])
    for rel, m in assembly['copied'].items():
        assert (BASE / m['origin']).is_relative_to(BASE)
        assert sha(BASE / m['origin']) == m['sha256'] == sha(public / rel)
    result = {'kind': 'PARENT_INDEPENDENT_CLEAN_EXTRACTION_RELEASE_REPLAY', 'anchors': ANCHORS,
              'original_stage_verification': run([sys.executable, '-B', str(public / 'verify.py'),
                  *anchored_args(), '--root', str(public)], 'original-stage-verification')}
    with tempfile.TemporaryDirectory(prefix='clean-', dir=HERE) as td:
        temp = Path(td)
        extraction = temp / 'extracted'
        result['clean_extraction'] = run([sys.executable, '-B', str(public / 'archive.py'), 'extract',
            '--archive', str(ROOT / 'release.zip'), '--manifest', str(ROOT / 'MANIFEST.json'),
            '--output', str(extraction)], 'clean-extraction')
        result['extraction_verification'] = run([sys.executable, '-B', str(extraction / 'verify.py'),
            *anchored_args(), '--root', str(extraction)], 'extraction-verification')
        initial = snap(extraction)
        output = temp / 'reproduction'
        argv = [sys.executable, '-B', str(extraction / 'reproduce.py'), 'all', '--output', str(output),
            '--python-path', str(ROOT / 'tools/python-packages'), '--lean', str(LEAN), '--cache', str(CACHE),
            '--tectonic', str(DRAFT / 'tools/tectonic'), '--tex-cache', str(DRAFT / 'build/cache')]
        result['full_portable_reproduction'] = run(argv, 'portable-reproduction')
        receipt = json.loads((output / 'receipt.json').read_text())
        assert receipt['status'] == 'REPRODUCED' and receipt['immutable_release_unchanged']
        assert receipt['table_bytes_identical']
        independent = receipt['independent_exact']
        assert len(independent['patterns']) == 10 and independent['total_terms'] == 248
        assert independent['universal_slack_and_residual_identities'] == 'EXACT_ZERO'
        formal = receipt['formal']
        assert formal['status'] == 'REPRODUCED_56_DECLARATIONS'
        assert (formal['support'], formal['controls'], formal['audit']) == (21, 20, 15)
        assert len(formal['exact_configurations']) == 10 and len(formal['semantic_mutations']) == 2
        assert formal['historical_type_logs_byte_identical']
        assert all(m['support_compiled'] and m['contract_rejected'] for m in formal['semantic_mutations'])
        pdf = receipt['pdf']
        assert pdf['matches_reviewed_pdf'] and pdf['borrowed_cache_unchanged'] and pdf['sha256'] == PDF_SHA
        expected_renders = {p.name: sha(p) for p in (DRAFT / 'packet/public/renders').glob('page-*.png')}
        assert len(expected_renders) == 20 and pdf['renders'] == expected_renders
        shutil.copy2(output / 'receipt.json', HERE / 'reproduction.json')
        shutil.copy2(output / 'logs/formal.log', HERE / 'formal-types-axioms.log')
        (HERE / 'independent-exact.json').write_text(json.dumps(independent, indent=2) + '\n')
        (HERE / 'exact-results.json').write_text(json.dumps(receipt['exact'], indent=2) + '\n')
        (HERE / 'tex-qa.json').write_text(json.dumps(pdf['qa'], indent=2) + '\n')
        result['copied_integrity_and_parser_controls'] = run([sys.executable, '-B', str(extraction / 'integrity_controls.py'),
            '--root', str(extraction), '--output', str(temp / 'controls'), *anchored_args()], 'copied-controls')
        controls = json.loads((temp / 'controls/receipt.json').read_text())
        assert controls['all_expected'] and controls['real_extraction_unchanged']
        assert len(controls['cases']) == 14 and len(controls['parser_controls']) == 7
        assert all(c['fixture_unchanged'] and ((c['exit'] == 0) == c['expected_pass']) for c in controls['cases'])
        assert all(c['rejected'] and c['archive_unchanged'] for c in controls['parser_controls'])
        shutil.copy2(temp / 'controls/receipt.json', HERE / 'artifact-controls.json')
        result['deterministic_reassembly'] = run([sys.executable, '-B', str(extraction / 'archive.py'), 'assemble',
            '--source', str(extraction), '--output', str(temp / 'reassembly')], 'deterministic-reassembly')
        assert sha(temp / 'reassembly/release.zip') == ANCHORS['archive']
        assert (temp / 'reassembly/release.zip').read_bytes() == (ROOT / 'release.zip').read_bytes()
        assert snap(extraction) == initial
        result['post_reproduction_extraction_verification'] = run([sys.executable, '-B', str(extraction / 'verify.py'),
            *anchored_args(), '--root', str(extraction)], 'post-reproduction-verification')
    assert snap(ROOT) == release_before
    for name, state in original_before.items():
        assert snap(BASE / name) == state, name
    assert all(sha(Path(p)) == h for p, h in named.items())
    for rel, m in assembly['copied'].items():
        assert sha(BASE / m['origin']) == m['sha256']
    result.update(all_expected=True, archive_bytes=824512, archive_members=95, archive_files=76,
        archive_directories=19, payload_files=75, original_entries_unchanged=9519,
        original_roots_unchanged=8, entire_actual_release_root_unchanged=True, named_parent_inputs_unchanged=12,
        unchanged_selected_origins=68, verification_named_files_authenticated=13,
        exact_patterns=10, exact_printed_terms=248, formal_declarations={'support':21,'controls':20,'audit':15},
        rational_cases=10, semantic_mutation_rejections=2, artifact_controls=14, zip_parser_controls=7,
        pdf_sha256=PDF_SHA, all20_render_bytes_identical=True, extraction_unchanged=True,
        archive_reassembly_byte_identical=True, full_theorem_formalized=False,
        source_path_portable_with_declared_dependencies=True)
    result['limits'] = (
        'Parent read full release report/README/new verifier/archive/reproduction/controls,parsed assembly/tool/evidence metadata, '
        'and independently runs complete clean-extraction exact/formal/PDF reproduction and deterministic archive reassembly. '
        'Explicit trusted dependencies: supplied Lean4.34.1/pinned precompiled cache,Tectonic0.17.0/hash-bound415-file cache, '
        'release-local SymPy1.14.0/mpmath1.3.0,systemPython/Poppler/runtime. Only own Lean sources rebuilt,no full Lean-cache '
        'authentication,clean dependency-source build,OS sandbox or full supply-chain audit. No old author/manuscript/formal '
        'source/project/private body is an executable input;declared tool/cache paths remain explicit. All20render/PDF bytes '
        'match reviewed artifacts,not another new all-page visual manuscript review. Fourteen external-anchor/file/archive '
        'controls plus seven direct ZIP-parser cases pass;duplicate-member warning is expected. Eight current original roots '
        '/9519 entries,12 named parent inputs,68 selected origins and complete actual release root stay unchanged. '
        'Local verification13-file inventory is separately authenticated,not public-verifier coverage or wholeworktree '
        'history/semantic-read evidence. Frozen preacceptance metadata stays unchanged;separate parent decision controls '
        'release adoption and any acceptance/count. Initial parent snapshot comparison used a different symlink '
        'record spelling/link-count field;only that parent reader was corrected,with original paths/bytes/targets '
        'unchanged and no payload execution before the correction. Publication remains stopped.')
    (HERE / 'replay.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('all_expected', 'archive_members', 'archive_files', 'archive_directories',
        'exact_printed_terms', 'formal_declarations', 'artifact_controls', 'zip_parser_controls',
        'all20_render_bytes_identical', 'archive_reassembly_byte_identical', 'original_entries_unchanged')}))


if __name__ == '__main__':
    main()
