#!/usr/bin/env python3
"""Write pins, raw-line receipt, manifests, both ZIPs, a safe extraction test of the source-only
ZIP (no Lean), the PDF QA receipt, and the frozen-input comparison. Pure Python; no Lean."""
from pathlib import Path
import hashlib, json, zipfile, shutil, subprocess, datetime, sys, os, stat
W = Path(__file__).resolve().parents[1]
R = W.parent
os.chdir(W)
now = datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds')
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(p, d): Path(p).write_text(json.dumps(d, indent=2, ensure_ascii=False) + '\n')

# Byte identity with the root-fixed acceptance files.
SRC = R / 'tabminors-parent-check-r1/fixed2/src'
ident = {}
for m, d in [('TabMinors', 'formal'), ('Controls', 'formal'), ('AuditFull', 'formal'), ('NegControl1', 'negative'), ('NegControl2', 'negative')]:
    a, b = sha(SRC / f'{m}.lean'), sha(W / d / f'{m}.lean')
    ident[f'{d}/{m}.lean'] = dict(sha256=b, root_fixed2_sha256=a, identical=a == b)
assert all(v['identical'] for v in ident.values())
assert ident['formal/TabMinors.lean']['sha256'] == '66fee9a4b0c59e62fc176ef52eca1a55480593b493cdeaee2024091b0cbb5fd7'
dump('MODULE-HASHES.json', dict(utc=now, modules=ident, lane_original_TabMinors_sha256='88bb95043b39fc679081ce62ba9101b1d2c8193c216c0db2517b2fb36af55af2',
                                note='Acceptance file is root fixed2 (annotation-only: seven noncomputable additions).'))

pins = dict(lean_version='4.34.1', lean_commit='5045d0056413266e57c625dcd7c365b10e377c52',
            lean_bin='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin',
            mathlib_commit='d13f23b723b8a846827a245b89c10fc7d3f11612',
            lean_packages='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages',
            package_manifest='evidence/lake-manifest.json', package_manifest_sha256=sha('evidence/lake-manifest.json'),
            lean_toolchain_file_sha256=sha('evidence/lean-toolchain'),
            trust_limit='Pinned cached upstream oleans trusted; not source-attested or rebuilt')
dump('pins.json', pins)

raw = Path('sources/mathdb-359279.jsonl').read_bytes()
rec = json.loads(raw)
dump('receipts/raw-line.json', dict(file='sources/mathdb-359279.jsonl', origin='expanded-corpus-r118/raw/359279.jsonl',
     sha256=hashlib.sha256(raw).hexdigest(), bytes=len(raw), lines=raw.count(b'\n') or 1, mathdb_id=rec['mathdb_id'], title=rec['title'],
     statement=rec['statement'], canonical_url=rec['canonical_url'], source_url=rec['source_url'], status=rec['status']))

# Source-only file set (these are what root's replay needs, plus the readable proof and paper source).
source_files = ['formal/TabMinors.lean', 'formal/Controls.lean', 'formal/AuditFull.lean', 'negative/NegControl1.lean', 'negative/NegControl2.lean',
                'replay.py', 'REPRODUCE.md', 'PROOF.md', 'STATEMENT-CORRESPONDENCE.md', 'pins.json', 'MODULE-HASHES.json',
                'sources/mathdb-359279.jsonl', 'evidence/lake-manifest.json', 'evidence/lean-toolchain',
                'scripts/check_pair.py', 'paper/build_paper.py']
dump('SOURCE-MANIFEST.json', dict(utc=now, files={f: sha(f) for f in source_files}))
source_files.append('SOURCE-MANIFEST.json')

def make_zip(name, files):
    with zipfile.ZipFile(name, 'w', zipfile.ZIP_DEFLATED) as z:
        for f in sorted(files):
            zi = zipfile.ZipInfo(f, date_time=(2026, 11, 2, 0, 0, 0)); zi.external_attr = 0o644 << 16; zi.compress_type = zipfile.ZIP_DEFLATED
            z.writestr(zi, Path(f).read_bytes())
make_zip('tabminors-source-only.zip', source_files)

# Safe extraction test (no Lean): path sanity, no links, hash equality, no build products.
X = W / 'tmp/extract-test'
shutil.rmtree(X, ignore_errors=True); X.mkdir(parents=True)
problems = []
with zipfile.ZipFile('tabminors-source-only.zip') as z:
    names = z.namelist()
    for zi in z.infolist():
        n = zi.filename
        if n.startswith('/') or '..' in Path(n).parts or '\\' in n or ':' in n: problems.append('unsafe path ' + n)
        if stat.S_ISLNK(zi.external_attr >> 16): problems.append('symlink ' + n)
        if (X / n).resolve().is_relative_to(X.resolve()) is False: problems.append('escape ' + n)
    if not problems: z.extractall(X)
man = json.loads((X / 'SOURCE-MANIFEST.json').read_text())['files']
mism = [f for f, h in man.items() if sha(X / f) != h]
build_products = [str(p.relative_to(X)) for p in X.rglob('*') if p.suffix in ('.olean', '.ilean', '.c')]
ident_x = {f: sha(X / f) == ident[f]['root_fixed2_sha256'] for f in ident}
compile_ok = subprocess.run([sys.executable, '-I', '-B', '-c', 'import ast,sys;ast.parse(open(sys.argv[1]).read())', str(X / 'replay.py')]).returncode == 0
ext = dict(utc=now, zip='tabminors-source-only.zip', zip_sha256=sha('tabminors-source-only.zip'), entries=len(names), unsafe=problems,
           manifest_files=len(man), manifest_mismatches=mism, build_products=build_products, lean_modules_identical_to_root_fixed2=ident_x,
           replay_py_parses=compile_ok, lean_run=False, note='Extraction test only; root performs the Lean replay.',
           status='PASS' if not problems and not mism and not build_products and all(ident_x.values()) and compile_ok else 'FAIL')
dump('receipts/extraction.json', ext)
shutil.rmtree(X)
assert ext['status'] == 'PASS', ext

# PDF QA receipt (pages rendered by pdftoppm, inspected visually by the lane).
pdf = Path('paper/tabminors-draft.pdf')
pages = sorted(Path('qa').glob('page-*.png'))
info = subprocess.run(['pdfinfo', str(pdf)], capture_output=True, text=True).stdout
Path('receipts/pdfinfo.txt').write_text(info)
npages = int([l for l in info.splitlines() if l.startswith('Pages:')][0].split()[1])
dump('receipts/pdf-visual-qa.json', dict(utc=now, pdf=str(pdf), pdf_sha256=sha(pdf), pages=npages, rendered=[p.name for p in pages],
     rendered_sha256={p.name: sha(p) for p in pages}, renderer='pdftoppm -r 80 -png', all_pages_rendered=len(pages) == npages,
     visual_inspection='Each page image was opened and inspected by the lane: text spaced and legible, sub/superscripts and symbols render (Symbola fallback), both tables fit the text width, no overflow or clipped text; page 5 holds the last three references.'))

# Frozen inputs after.
before = Path('receipts/frozen-inputs-sha256-before.txt').read_text().splitlines()
after, changed = [], []
for line in before:
    h, p = line.split('  ', 1)
    q = R / p
    hh = sha(q) if q.is_file() else 'MISSING'
    after.append(f'{hh}  {p}')
    if hh != h: changed.append(p)
Path('receipts/frozen-inputs-sha256-after.txt').write_text('\n'.join(after) + '\n')
new_files = sorted(set(str(p.relative_to(R)) for d in ['tabminors-parent-check-r1', 'expanded-corpus-r118', 'tabminors-review-r1'] for p in (R / d).rglob('*') if p.is_file())
                   - set(l.split('  ', 1)[1] for l in before))
dump('receipts/frozen-bindings.json', dict(utc=now, files=len(before), changed=changed, new_files_in_input_trees=new_files[:50],
     unchanged=not changed, note='Inputs were read-only; new files under input trees, if any, were not written by this lane.'))

# Full dossier ZIP (everything except tmp/ and the ZIPs themselves).
full = [str(p.relative_to(W)) for p in W.rglob('*') if p.is_file() and not str(p.relative_to(W)).startswith('tmp/')
        and p.suffix != '.zip' and p.name not in ('DOSSIER-MANIFEST.json', 'archive-hashes.json')]
dump('DOSSIER-MANIFEST.json', dict(utc=now, files={f: sha(f) for f in sorted(full)}))
full.append('DOSSIER-MANIFEST.json')
make_zip('tabminors-full-dossier.zip', full)
with zipfile.ZipFile('tabminors-full-dossier.zip') as z: bad = z.testzip(); nfull = len(z.namelist())
dump('archive-hashes.json', {'tabminors-source-only.zip': dict(sha256=sha('tabminors-source-only.zip'), entries=len(names)),
                             'tabminors-full-dossier.zip': dict(sha256=sha('tabminors-full-dossier.zip'), entries=nfull, testzip=bad)})
print(json.dumps(dict(extraction=ext['status'], frozen_unchanged=not changed, pdf_pages=npages, source_entries=len(names), full_entries=nfull)))
