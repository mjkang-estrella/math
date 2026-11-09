"""Seal coverage/checker evidence and append the final section of the Codex note."""
import sys
sys.dont_write_bytecode = True
import os, json, glob, hashlib, collections, datetime
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
sys.path.insert(0,HERE)
from breadth import atomic_json

def sha256(fn):
    h=hashlib.sha256()
    with open(fn,'rb') as f:
        for b in iter(lambda:f.read(1<<20),b''): h.update(b)
    return h.hexdigest()

audit=json.load(open(os.path.join(HERE,'coverage_summary.json')))
checks=json.load(open(os.path.join(HERE,'checker_results.json')))
assert audit['final'] and not audit['problems']
assert audit['certificates']==audit['both_checker_pass']
for r in audit['coverage'].values(): assert r['closed_now']==r['checked_closed']
manifest={}
for pat in ('*.py','*.json','certs/**/*.jsonl'):
    for fn in glob.glob(os.path.join(HERE,pat),recursive=True):
        if os.path.basename(fn)=='manifest.json': continue
        manifest[os.path.relpath(fn,HERE)]=sha256(fn)
for rel in ('verification/indep/nt.py','verification/indep2/e_enum.py',
            'verification/indep3/i3_enum.py','verification/v14_checknd_hd.py'):
    manifest['../../../'+rel]=sha256(os.path.join(ROOT,rel))
atomic_json(os.path.join(HERE,'manifest.json'),{
    'label':'COMPUTED','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'sha256':manifest})

lines=['## Codex final report','','**PROVED (certificate covers); COMPUTED (counts and execution).**',
       'Every closed configuration below has a complete E/E2 slice cover, every distinct',
       'far-digit ordering is covered, and every local certificate passed both checkers.',
       'Every other configuration was attempted and is explicitly BUDGET.','',
       '| target | open before | closed now | still open |',
       '|---:|---:|---:|---:|']
for t in ('16','24','32','14112'):
    r=audit['coverage'][t]
    lines.append(f'| {t} | {r["open_before"]} | {r["closed_now"]} | {r["still_open"]} |')
lines += ['',f'**COMPUTED.** {audit["certificates"]} certificates passed `checkhd.py` and',
          f'`verification/v14_checknd_hd.py`: {2*audit["certificates"]} PASS verdicts, no failures.',
          'The checker sources execute through `checker_entry.py`, which suppresses bytecode',
          'writes and memoizes the original trial-division primality verdict and Python builtin',
          'modular powers. These caches change neither arithmetic nor acceptance rules.',
          'The full residue trees and exact-size leaves are checked; supplementary brute boxes',
          'are L<=100 (dim 1), 60 (dim 2), 30 (dim 3), and 12 (higher dimensions).','',
          f'The independently replayed E/E2 slice cover has maximum floor {audit["max_independent_slice_floor"]}.',
          'Finite exceptional lengths are therefore covered by E/E2\'s existing complete',
          '7-smooth lattice sweeps through 600 digits (not rerun here). Those input JSONs are',
          'hashed and included in `coverage_summary.json`. No new actual member occurs in the',
          'closed configurations. Combined with E2\'s repaired earlier covers, t=16 and t=24',
          'are now closed for all lengths. Their member lists remain respectively',
          '{28,128,144,224,441} and {64,243,324,432,4116}.','',
          'For 14112, the baseline is the 870 configurations with at least three far digits.',
          'S387 {54,54} was already closed by E2\'s separate pin2 work and is excluded here.',
          'The known member 33718272 lies in a configuration that remains BUDGET.','',
          '**COMPUTED budgets.** The small-target initial pass used 180 s/configuration,',
          '600000 nodes/attempt and 30000000 lifts/configuration. The t=32 continuation used',
          '600 s, 600000 nodes and 150000000 lifts. The final 14112 breadth pass used 20 s,',
          '100000 nodes and 2000000 lifts. Configuration preparation and writing are also',
          'included in reported elapsed times; the alarm guards certification. The original',
          'depth limit (40) and modulus limit (10^12) remain. A level is rejected before',
          'expansion if its full lift count would exceed the remaining budget. Incomplete',
          'trees are never emitted as certificates. A BUDGET result is not a nonexistence proof.','',
          'Remaining t=32 configurations:']
for r in audit['configurations']['32']:
    if r['status']!='CLOSED': lines.append(f'- `{r["key"]}`: {r["reason"]}')
lines += ['', 'Files (all under `verification/highdim/codex/`):',
          '- `results_t16.json`, `results_t24.json`, `results_t32.json`, `results_t14112.json`: every authoritative configuration.',
          '- `coverage_summary.json`: configuration-by-configuration slice/ordering audit, with certificate paths.',
          '- `checker_results.json`, `logs/checks/`: certificate SHA-256, both checker verdicts, logs and timings.',
          '- `certs/t*/`: all complete certificates, including certificates from configurations still BUDGET.',
          '- `manifest.json`: hashes of scripts, data, certificates and independent checker/enumerators.',
          '- `logs/breadth_t14112_finalpass.log`, `logs/breadth_t32_resume.log`: final generation passes.',
          '', 'Reproduction from the repository root (stdlib only; no commits):',
          '', '```sh',
          "timeout 1700 bash -c 'ulimit -v 6000000; python3 -I verification/highdim/codex/breadth.py 14112 12 20 100000 2000000'",
          "timeout 650 bash -c 'ulimit -v 6000000; python3 -I verification/highdim/codex/breadth.py 32 3 600 600000 150000000'",
          "timeout 1700 bash -c 'ulimit -v 6000000; python3 -I verification/highdim/codex/check_batch.py 20 all 1200'",
          "timeout 120 bash -c 'ulimit -v 6000000; python3 -I verification/highdim/codex/audit_results.py --final'",
          '```', '',
          '**CONJECTURAL.** Further schedules or larger budgets may close more of the remaining',
          'configurations. No claim is made here about 111132, the original author\'s ongoing',
          'hd2 work, or a proof of the general persistence conjecture.','']
note=os.path.join(ROOT,'notes','highdim_codex.md')
old=open(note).read().split('## Codex final report')[0]
with open(note,'w') as f: f.write(old.rstrip()+'\n\n'+'\n'.join(lines))
with open(os.path.join(HERE,'REPORT.md'),'w') as f: f.write('\n'.join(lines))
print('\n'.join(lines[:15]))
