"""Lane tooling: post-replay receipts, frozen re-binding, full dossier, results.json.

    python3 -I finalize.py
"""
import datetime, hashlib, json, shutil, subprocess, sys
from pathlib import Path

L = Path(__file__).resolve().parents[1]
BASE = L.parent
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
now = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat()
R = L / 'receipts'

run = L / 'fresh-replay' / 'run'
rec = json.loads((run / 'replay-receipt.json').read_text())
assert rec['all_ok'], rec['problems']
fr = L / 'fresh-replay' / 'receipts'
shutil.copyfile(run / 'replay-receipt.json', fr / 'replay-receipt.json')
for sub in ('logs', 'audit'):
    if (fr / sub).exists():
        shutil.rmtree(fr / sub)
    shutil.copytree(run / sub, fr / sub)
shutil.copyfile(run / 'src' / 'perm-order.txt', fr / 'perm-order.txt')

# frozen inputs re-bound after all work
subprocess.run([sys.executable, '-I', '-B', str(L / 'scripts' / 'hashbind.py'), str(R / 'frozen-after.json')], check=True)
b = json.loads((R / 'frozen-before.json').read_text())
a = json.loads((R / 'frozen-after.json').read_text())
changed = sorted(k for k in set(a['files']) | set(b['files']) if a['files'].get(k) != b['files'].get(k))
(R / 'frozen-bindings.json').write_text(json.dumps({
    'utc': now(), 'roots': b['roots'], 'file_count_before': b['file_count'], 'file_count_after': a['file_count'],
    'aggregate_before': b['aggregate_sha256'], 'aggregate_after': a['aggregate_sha256'],
    'changed_or_missing': changed, 'unchanged': not changed}, indent=1))

# Lean identity: frozen lean/, dossier/lean, extracted copy
frozen = BASE / 'expanded-corpus-r96' / 'lean'
ext = L / 'fresh-replay' / 'extract' / 'lean'
ident = {f.name: {'frozen': sha(f), 'dossier': sha(L / 'dossier' / 'lean' / f.name), 'extracted': sha(ext / f.name)}
         for f in sorted(frozen.glob('*.lean'))}
ident_ok = all(len(set(v.values())) == 1 for v in ident.values()) and len(ident) == 22 and \
    sorted(p.name for p in (L / 'dossier' / 'lean').glob('*.lean')) == sorted(ident)
(R / 'lean-identity.json').write_text(json.dumps({'utc': now(), 'modules': ident, 'count': len(ident),
                                                  'byte_identical': ident_ok}, indent=1))

# MathDB binding
raw = L / 'dossier' / 'mathdb' / '368807.jsonl'
line = json.loads(raw.read_text())
mb = {'utc': now(), 'file': 'dossier/mathdb/368807.jsonl', 'raw_line_sha256': sha(raw),
      'expected_raw_line_sha256': 'c215c90f1c340a3c289ccffc287ce0af7f9eb7bca8273ba6e1a9140a682f1067',
      'frozen_copy_sha256': b['files']['expanded-corpus-r96/raw/368807.jsonl'],
      'statement_sha256': hashlib.sha256(line['statement'].encode()).hexdigest(),
      'mathdb_id': line['mathdb_id'], 'title': line['title'], 'canonical_url': line['canonical_url']}
mb['ok'] = mb['raw_line_sha256'] == mb['expected_raw_line_sha256'] == mb['frozen_copy_sha256']
(R / 'mathdb-binding.json').write_text(json.dumps(mb, indent=1))

# full dossier and its verification by a fresh safe extraction
subprocess.run([sys.executable, '-I', '-B', str(L / 'scripts' / 'assemble.py'), 'full'], check=True)
ver = L / 'tmp' / 'full-verify'
if ver.exists():
    shutil.rmtree(ver)
subprocess.run([sys.executable, '-I', '-B', str(L / 'dossier' / 'tools' / 'safe_extract.py'),
                str(L / 'asep-368807-full-dossier.zip'), str(ver), str(L / 'tmp' / 'full-verify-extraction.json')], check=True)
man = json.loads((ver / 'full-dossier-manifest.json').read_text())
got = {str(p.relative_to(ver)): sha(p) for p in ver.rglob('*') if p.is_file() and p.name != 'full-dossier-manifest.json'}
inner_src = sha(ver / 'asep-368807-source.zip')
fv = {'utc': now(), 'full_zip_sha256': sha(L / 'asep-368807-full-dossier.zip'), 'members_checked': len(got),
      'manifest_matches': got == man['files'], 'inner_source_zip_matches': inner_src == sha(L / 'asep-368807-source.zip'),
      'pdf_matches': sha(ver / 'asep-368807-draft.pdf') == sha(L / 'asep-368807-draft.pdf')}
fv['ok'] = fv['manifest_matches'] and fv['inner_source_zip_matches'] and fv['pdf_matches']
shutil.rmtree(ver)
(L / 'full-dossier-verification.json').write_text(json.dumps(fv, indent=1))

src_ext = json.loads((fr / 'source-extraction.json').read_text())
arith = json.loads((R / 'check-arith.json').read_text())
pdfqa = json.loads((R / 'pdf-qa.json').read_text())
audit = rec['audit']
archives = {'asep-368807-source.zip': sha(L / 'asep-368807-source.zip'),
            'asep-368807-full-dossier.zip': sha(L / 'asep-368807-full-dossier.zip'),
            'asep-368807-draft.pdf': sha(L / 'asep-368807-draft.pdf')}
(L / 'ARCHIVES-SHA256.json').write_text(json.dumps(archives, indent=1))
shutil.copyfile(L / 'dossier' / 'MANIFEST.json', L / 'source-manifest.json')
results = {
    'utc': now(), 'lane': 'asep-manuscript-r1', 'mathdb_id': 368807,
    'source': 'Vercesi-Barta-Gambardella-Gualandi-Mastrolilli, arXiv:2506.10671v1, Conjecture 1',
    'claim': 'x* = X/4 is a fractional vertex of P_ASEP^8 (19 support arcs, 8 tight cuts, tight rank 56) adjacent to no tour; Conjecture 1 is false. n = 7 (and n = 6) open.',
    'status': 'DRAFT manuscript and dossier; zero accepted credit; root alone accepts', 'credit': 0,
    'campaign_count': '15/20 beyond 39 (unchanged by this lane)',
    'deliverables': {'pdf': 'asep-368807-draft.pdf', 'paper_source': ['dossier/paper/manuscript.md', 'dossier/paper/build_paper.py'],
                     'proof': 'dossier/PROOF.md', 'reproduce': 'dossier/REPRODUCE.md',
                     'source_zip': 'asep-368807-source.zip', 'full_zip': 'asep-368807-full-dossier.zip',
                     'source_manifest': 'source-manifest.json', 'full_manifest': 'full-dossier-manifest.json',
                     'archive_hashes': 'ARCHIVES-SHA256.json'},
    'archives_sha256': archives,
    'pdf': {'pages': pdfqa['pages'], 'all_pages_rendered_and_inspected': pdfqa['visual_inspection']['all_pages_inspected'],
            'mechanical_ok': pdfqa['mechanical']['mechanical_ok'], 'qa': 'qa/, receipts/pdf-qa.json'},
    'fresh_replay': {'source_zip_sha256': src_ext['archive_sha256'], 'extracted_members': src_ext['num_members'],
                     'all_ok': rec['all_ok'], 'lean_calls': rec['num_lean_calls'],
                     'strict_builds_passed': sum(1 for s in rec['steps'] if s['check'].startswith('strict build ') and s['ok']),
                     'strict_builds_note': '21 proof modules + PermOrder helper + AuditLib',
                     'leanchecker_modules_passed': sum(1 for s in rec['steps'] if s['check'].startswith('leanchecker ASEP') or s['check'] == 'leanchecker PermOrder'),
                     'declarations_audited': audit['num_declarations'], 'kinds': audit['kinds'],
                     'unsafe_rec_helpers': audit['unsafe_rec_helpers'],
                     'endpoints': {e['endpoint']: {'collectAxioms': e['collectAxioms'], 'walk_axioms': e['walk_axioms'],
                                                   'closure_size': e['closure_size'], 'ok': e['ok']}
                                   for e in audit['summary']['endpoints']},
                     'controls': rec['controls'],
                     'max_cpu_seconds': rec['max_cpu_seconds'], 'max_wall_seconds': rec['max_wall_seconds'],
                     'peak_sampled_rss_bytes': rec['peak_sampled_rss_bytes'],
                     'peak_sampled_private_rss_bytes': rec['peak_sampled_private_rss_bytes'],
                     'receipt': 'fresh-replay/receipts/replay-receipt.json'},
    'exact_arithmetic_crosscheck': {'all_ok': arith['all_ok'], 'tight_rank': arith['vertex']['tight_system_rank'],
                                    'certificates_failing': arith['certificates']['num_failing'],
                                    'n4_adjacent_tours': arith['n4_control']['num_adjacent_tours']},
    'lean_byte_identical': ident_ok, 'mathdb_binding_ok': mb['ok'],
    'frozen_inputs_unchanged': not changed, 'frozen_file_count': b['file_count'],
    'full_dossier_verified': fv['ok'],
    'superseded': 'receipts/superseded-replay.json (earlier passing replay of the pre-heading-fix ZIP)',
}
(L / 'results.json').write_text(json.dumps(results, indent=1))
print(json.dumps({k: results[k] for k in ('lean_byte_identical', 'mathdb_binding_ok', 'frozen_inputs_unchanged', 'full_dossier_verified')}),
      json.dumps(archives))
