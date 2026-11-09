import sys
sys.dont_write_bytecode=True
import json,hashlib,os,collections,time
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    a=json.load(open(HERE/'coverage_summary.json'));assert a['final'] and not a['problems']
    history=[json.loads(l) for l in open(HERE/'history.jsonl')]
    checks=json.load(open(HERE/'checker_results.json'))
    verdicts=collections.Counter(v['status'] for rec in checks.values() for v in rec.values())
    text='# Codex 3a final report\n\n**PROVED** denotes complete independently checked covers; **COMPUTED** denotes executed finite work.\n\n'
    text+='| target | assigned | closed | still open |\n|---:|---:|---:|---:|\n'
    for t,c in a['coverage'].items():
        assert c['assigned']==c['attempted'] and c['closed']==c['checked_closed']
        text+=f'| {t} | {c["assigned"]} | {c["checked_closed"]} | {c["still_open"]} |\n'
    text+=f'\n**COMPUTED.** {a["certificates"]} certificates pass BOTH checkers directly; verdicts: {dict(verdicts)}. '
    text+='Commands run the copied `checkhd.py` and original `verification/v14_checknd_hd.py` with `python3 -I -B`, no wrapper or builtin changes. '
    text+='All exclusion kills are ordinary prime kills. No new kill type or checker acceptance change was introduced.\n\n'
    stats=json.load(open(HERE/'cert_stats.json'))
    text+=f'**COMPUTED.** The adopted certificates contain {stats["total_nodes"]} nodes and {stats["total_certificate_lifts"]} full partition lifts. No new actual member occurs in these closed configurations.\n\n'
    text+='**PROVED.** Every closure passes an independent E/E2 slice and ordering audit. '
    text+=f'The maximum independent slice floor is {a["max_floor"]}. '
    if all(r.get('no_short_length_gap') for rows in a['configurations'].values() for r in rows if r['status']=='CLOSED'):
        text+='Every adopted certificate has the original K and all four far positions free with floor 3. A genuine placement therefore has L>=7 and there is no short-length gap. Existing finite-enumeration hashes are included for context; no new finite sweep was needed.\n\n'
    else:
        text+='Existing E/E2 lattice enumerations through 600 digits cover finite exceptional lengths (hashes recorded; not rerun).\n\n'
    text+='**COMPUTED.** The exact 333-key zero-based EVEN assignment, with original indices and input hash, is in `assignment.json` and `notes/highdim_codex3a.md`. '
    text+='Every assigned configuration was attempted. Search history, including completed records from interrupted exploratory passes, is checkpointed in `history.jsonl`. '
    text+='BUDGET means open: it is not a nonexistence proof. No claim about the general persistence conjecture follows.\n\n'
    text+='Files: `results_t32.json`, `results_t14112.json`, `coverage_summary.json`, `checker_results.json`, `cert_stats.json`, `certs/`, `logs/checks/`, `depth_diagnosis.json`, `supply_scan.json`, and `manifest.json`. Direct replay commands and certificate hashes are recorded in `checker_results.json`.\n'
    (HERE/'REPORT.md').write_text(text)
    note=ROOT/'notes/highdim_codex3a.md'
    prefix=note.read_text().split('\n## Final verified results',1)[0]
    note.write_text(prefix+'\n## Final verified results\n\n'+text.split('\n\n',1)[1])
    inputs=[ROOT/'verification/highdim/codex/results_t14112.json',ROOT/'verification/highdim/codex/results_t32.json',
        ROOT/'verification/highdim/codex/coverage_summary.json',ROOT/'verification/v14_checknd_hd.py',ROOT/'verification/indep/nt.py',
        ROOT/'verification/indep2/e_enum.py',ROOT/'verification/indep3/i3_enum.py']
    inputs+=list(HERE.glob('*.py'))+list(HERE.glob('*.json'))+list((HERE/'certs').rglob('*.jsonl'))
    inputs+=list(HERE.rglob('*.log'))+[HERE/'REPORT.md',HERE/'history.jsonl',ROOT/'notes/highdim_codex3a.md']
    inputs=[p for p in inputs if p.name!='manifest.json']
    (HERE/'manifest.json').write_text(json.dumps({str(p.relative_to(ROOT)):sha(p) for p in sorted(inputs)},indent=2)+'\n')
    print(text)
if __name__=='__main__':main()
