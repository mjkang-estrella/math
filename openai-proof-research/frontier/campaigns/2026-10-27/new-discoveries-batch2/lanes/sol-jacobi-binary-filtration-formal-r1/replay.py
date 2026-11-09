#!/usr/bin/env python3
"""Extract a deterministic source-only packet and strictly rebuild it in a fresh directory."""
from pathlib import Path
import datetime, gzip, hashlib, io, json, re, subprocess, sys, tarfile

lane = Path(__file__).resolve().parent
formal = lane / 'formal'
destination = (lane / (sys.argv[1] if len(sys.argv) > 1 else 'replay/fresh')).resolve()
if not destination.is_relative_to(lane) or destination.exists():
    raise SystemExit('Destination must be a nonexistent directory inside this lane.')
modules = ['BinaryDigits', 'Filtration', 'Riccati', 'NonSubring', 'Audit']
files = [m+'.lean' for m in modules] + ['run_lean.py', 'guard.py']
sha = lambda b: hashlib.sha256(b).hexdigest()
source_hashes = {f: sha((formal/f).read_bytes()) for f in files}
archive = lane/'replay/formal-source.tar.gz'
with archive.open('wb') as raw:
    with gzip.GzipFile(fileobj=raw, mode='wb', filename='', mtime=0) as gz:
        with tarfile.open(fileobj=gz, mode='w') as tar:
            for f in sorted(files):
                data = (formal/f).read_bytes()
                entry = tarfile.TarInfo('source/'+f)
                entry.size = len(data); entry.mtime = 0; entry.mode = 0o644
                tar.addfile(entry, io.BytesIO(data))
destination.mkdir(parents=True)
with tarfile.open(archive, 'r:gz') as tar:
    tar.extractall(destination, filter='data')
source = destination/'source'
logs = destination/'logs'; logs.mkdir()
assert not list(source.rglob('*.olean'))
assert all(sha((source/f).read_bytes())==source_hashes[f] for f in files)
results=[]
started=datetime.datetime.now(datetime.timezone.utc).isoformat()
for idx, module in enumerate(modules, 1):
    log = logs/f'{idx:02d}-{module}.log'
    command=[sys.executable,'guard.py',str(log),'-o',module+'.olean',module+'.lean']
    run=subprocess.run(command, cwd=source, capture_output=True, text=True)
    (logs/f'{idx:02d}-{module}.runner.log').write_text(run.stdout+run.stderr)
    record=json.loads(log.with_suffix('.log.json').read_text())
    results.append({'module':module,**record})
    print(module, 'exit',run.returncode,'sampled RSS KiB',record['sampled_peak_rss_kib'])
    if run.returncode:
        raise SystemExit(run.stdout+run.stderr)
audit=(logs/'05-Audit.log').read_text()
reports={}
for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",audit):
    reports[m.group(1)]=[x.strip() for x in (m.group(2) or '').split(',') if x.strip()]
expected=json.loads((lane/'logs/declarations.json').read_text())
allowed={'propext','Classical.choice','Quot.sound'}
assert set(reports)=={d['name'] for d in expected}
assert all(set(v)<=allowed for v in reports.values())
assert all(sha((source/f).read_bytes())==source_hashes[f] for f in files)
receipt={
    'status':'PASS', 'started_utc':started,
    'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'source_archive':str(archive.relative_to(lane)),
    'source_archive_sha256':sha(archive.read_bytes()),
    'isolated_source_directory':str(source.relative_to(lane)),
    'preexisting_local_olean_count':0,
    'source_hashes_sha256':source_hashes,
    'all_extracted_sources_byte_identical':True,
    'local_source_import_order':modules,
    'lean_path_first_entry':str(source),
    'external_lean_path_only':'Pinned 2026-10-14/formal/.lake/packages/*/.lake/build/lib/lean',
    'strict_options':['-j1','-M4096','-DwarningAsError=true','-DautoImplicit=false'],
    'rss_guard_kib':3*1024*1024,
    'maximum_sampled_rss_kib':max(r['sampled_peak_rss_kib'] for r in results),
    'builds':results,
    'audited_declarations':len(reports),
    'actual_axiom_reports':reports,
    'allowed_axioms':sorted(allowed),
    'unexpected_axioms':[],
    'output_olean_sha256':{m:sha((source/(m+'.olean')).read_bytes()) for m in modules},
    'audit_log_sha256':sha(audit.encode()),
}
(destination/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS: fresh source replay and',len(reports),'actual axiom reports')
print('Receipt:',destination/'receipt.json')
