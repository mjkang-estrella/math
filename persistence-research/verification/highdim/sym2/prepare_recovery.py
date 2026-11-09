"""Select only unfinished configurations that already saved complete pieces."""
import sys
sys.dont_write_bytecode = True
import json
import pathlib

HERE = pathlib.Path(__file__).resolve().parent


def main():
    done = set()
    candidates = {}
    for path in sorted(HERE.glob('search_*.json')):
        for key, rec in json.loads(path.read_text()).items():
            if rec['status'] == 'COMPLETE_PENDING_CHECKS':
                done.add(key)
            elif rec['status'] == 'BUDGET' and rec['jobs']:
                candidates.setdefault(key, []).append({'stage': path.stem, 'saved_pieces': len(rec['jobs'])})
    if (HERE / 'summary.json').exists():
        done.update(json.loads((HERE / 'summary.json').read_text())['closed'])
    chosen = sorted(set(candidates) - done)
    out = {'reason': 'unfinished cover with at least one saved complete piece; test inherited-cache recovery',
           'keys': chosen, 'evidence': {k: candidates[k] for k in chosen}}
    (HERE / 'recovery_selection.json').write_text(json.dumps(out, indent=1) + '\n')
    print(json.dumps({'selected': len(chosen), 'keys': chosen}))


if __name__ == '__main__':
    main()
