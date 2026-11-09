"""Publish final computed counts in the sole permitted note; bind evidence hashes."""
import hashlib
import json
import pathlib

H=pathlib.Path(__file__).resolve().parent
ROOT=H.parents[2]
note=ROOT/'notes/highdim_sym5.md'
summary=json.loads((H/'summary.json').read_text())
mark='\n## Executed results\n'
text=note.read_text().split(mark)[0]+mark+'\n'
text+='Counts concern only the 95 assigned sym4-open configurations. A closure\n'
text+='has a checked full cover plus the finite short-length scan.\n\n'
text+='| Target | Dimension | Assigned | Closed | Open | Deep-pin closures | Independently checked covers |\n'
text+='|---|---:|---:|---:|---:|---:|---:|\n'
for t,ds in summary['counts_by_target_dimension'].items():
    for d,r in ds.items():
        text+=f"| {t} | {d} | {r['assigned']} | {r['closed']} | {r['open']} | {r['deep_pin_closures']} | {r['independently_checked']} |\n"
text+=f"\nTotal: **{len(summary['closed'])} closed, {len(summary['open'])} open**. "
text+=f"**{summary['deep_pin_closures']} closures use k>3** in the retained proof. "
text+='This is a certificate/cover dependency, not a claim that no alternative\n'
text+='depth-three proof exists. For every deep tree, the same tree is also\n'
text+='tested with k=3; successful downgrades receive a fresh unmodified-F\n'
text+='replay. Coverage is then attempted using only those and original k<=3\n'
text+='certificates. The deep count is the number without such a legacy-only\n'
text+='cover in the available library.\n\n'
text+=f"Checker results on original retained/search certificates: `{summary['checker_counts']}`.\n"
text+=f"Depth-three tree ablations: `{summary['downgrades']}`. Original-F results\n"
text+=f"including successful new k=3 downgrades: `{summary['original_F_including_downgrades']}`.\n"
text+=f"Hash-bound inherited M/F passes: `{summary['inherited_checker_passes']}`; all other passes are fresh CLI replays.\n"
text+=f"Closure certificates: {summary['closure_certificates']}; deep closure certificates: {summary['closure_deep_certificates']}.\n"
text+=f"Finite scan: `{summary['finite_exception_scan']}`. Source hashes verified unchanged.\n\n"
if summary['F5_available']:
    text+='The independent extension `verification/indep5/check_sym_F5.py` was\n'
    text+='available and its direct CLI results are included above. Consult the\n'
    text+='per-configuration independent-cover flag; no F5 failure is silently\n'
    text+='promoted to independent verification.\n\n'
else:
    text+='**Independent deep-pin replay is pending.** F5 did not exist at the\n'
    text+='final availability check. The closed counts use the sym5 checker and\n'
    text+='the independent copied cover auditor; they must not be read as F5\n'
    text+='confirmation. Inherited k<=3 pieces use their original M/F records.\n'
    text+='`deep_pin_certs.txt` lists every full search certificate\n'
    text+='with k>3. `closure_deep_pin_certs.txt` is the smaller subset used by\n'
    text+='retained complete covers. Both use absolute paths.\n\n'
text+='| Stage | Attempts | Complete candidate covers | Budget-limited | Worker seconds |\n'
text+='|---|---:|---:|---:|---:|\n'
for stage,r in summary['stages'].items():
    text+=f"| {stage} | {r['attempts']} | {r['statuses'].get('COMPLETE_PENDING_CHECKS',0)} | {r['statuses'].get('BUDGET',0)} | {r['worker_seconds']} |\n"
text+='\nAll 95 were attempted, and every still-unfinished configuration received\n'
text+='the next escalating budget. Completed individual slice certificates\n'
text+='from unfinished configurations are retained and checked too. OPEN means\n'
text+='the recorded finite search failed to finish a complete cover, not that\n'
text+='a smooth point was found. Partial generator trees are never emitted.\n\n'
text+='Reproduction (all Python invocations preserve the memory limit):\n\n```sh\n'
for stage,secs,k in (('pin4_10',10,4),('pin5_30',30,5),('pin6_60',60,6)):
    extra=' --extra-floor 2' if k>4 else ''
    text+=f"timeout 1200 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym5/continue_sym2.py search --stage {stage} --seconds {secs} --workers 8 --pin-digits {k} --position-slices --precompute --schedule 2,3,5,2,3,2,7{extra} --modulus-digits {90 if k==4 else 100 if k==5 else 120} --depth {280 if k==4 else 320 if k==5 else 400}'\n"
text+="timeout 1500 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym5/replay5.py --workers 8 --seconds 900 --downgrade'\n"
text+="timeout 900 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym5/finalize5.py'\n"
text+="timeout 600 bash -c 'ulimit -v 8000000; python3 -I verification/highdim/sym5/test_sym5.py'\n```\n\n"
text+='Main evidence: `summary.json`, `checks5.json`, `checks5_journal.jsonl`,\n'
text+='`test_results.json`, `source_hashes.json`, `input_*.json`, `search_*.json`,\n'
text+='`closure_certs.txt`, `deep_pin_certs.txt`, `closure_deep_pin_certs.txt`,\n'
text+='`certs/`, and `k3_certs/`, all under `verification/highdim/sym5/`.\n'
text+='The marked generator/checker `.diff` files identify the minimal arithmetic\n'
text+='extension. `manifest5.json` binds scripts, ledgers, this note, and all\n'
text+='retained closure certificates. No git commit was made.\n'
note.write_text(text)
files=[p for p in H.iterdir() if p.suffix in ('.py','.json','.diff','.txt') and p.name!='manifest5.json']
files += [note]+[pathlib.Path(p) for p in summary['certificate_sha256']]
files += list((H/'controls').glob('*.jsonl'))+list((H/'tamper').glob('*.jsonl'))
manifest={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(files))}
(H/'manifest5.json').write_text(json.dumps(manifest,indent=1)+'\n')
print(json.dumps({'note':str(note),'manifest_files':len(manifest)}))
