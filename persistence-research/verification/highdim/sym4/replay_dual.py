"""Orchestrate DIRECT original checker CLIs; never import checker code."""
import sys
sys.dont_write_bytecode = True
import argparse
import collections
import concurrent.futures
import hashlib
import json
import pathlib
import subprocess
import time

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[2]
CHECKERS = {'M': ROOT/'verification/highdim/sym/check_sym.py',
            'F': ROOT/'verification/indep4/check_sym_F.py'}


def digest(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def save(p, obj):
    tmp = p.with_suffix(p.suffix+'.tmp')
    tmp.write_text(json.dumps(obj, indent=1)+'\n')
    tmp.replace(p)


def one(path, who, brute, seconds):
    checker = CHECKERS[who]
    before, code = digest(path), digest(checker)
    command = ['bash', '-c', 'ulimit -v 8000000; python3 -I "$@"',
               'sym4-direct', str(checker), str(path), str(brute)]
    if who == 'F':
        command.append('--json')
    start = time.monotonic()
    try:
        proc = subprocess.run(command, text=True, capture_output=True, timeout=seconds)
        result = json.loads(proc.stdout.strip().splitlines()[-1])
        assert proc.returncode == 0 and result['result'] == 'PASS', (proc.returncode, result, proc.stderr[-1000:])
        assert before == digest(path) and code == digest(checker), 'changed input'
        out = {'result':'PASS', 'check':result}
    except Exception as e:
        out = {'result':'FAIL', 'error':repr(e)}
    out.update(command=command, sha256=before, checker_sha256=code,
               brute_Lmax=brute,
               seconds=round(time.monotonic()-start,3))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--workers', type=int, default=12)
    ap.add_argument('--brute', type=int, default=10)
    ap.add_argument('--seconds', type=int, default=900)
    args = ap.parse_args()
    assert 1 <= args.workers <= 12 and args.seconds < 1700
    paths = set((HERE/'certs').rglob('*.jsonl'))
    paths.update((HERE/'controls').glob('*.jsonl'))
    for p in HERE.glob('search_*.json'):
        for row in json.loads(p.read_text()).values():
            paths.update(pathlib.Path(j['file']) for j in row['jobs'])
    ledgerpath = HERE/'dual_checks.json'
    ledger = json.loads(ledgerpath.read_text()) if ledgerpath.exists() else {'files':{}}
    journal = HERE/'dual_journal.jsonl'
    if journal.exists():
        for line in journal.read_text().splitlines():
            row = json.loads(line)
            ledger['files'].setdefault(row['file'],{})[row['who']] = row['record']
    pending = []
    for path in sorted(paths):
        for who, checker in CHECKERS.items():
            old = ledger['files'].get(str(path),{}).get(who,{})
            if (old.get('result') == 'PASS' and old['sha256'] == digest(path)
                and old['checker_sha256'] == digest(checker)
                and old.get('brute_Lmax',old['check'].get('brute_Lmax',ledger.get('brute_Lmax'))) == args.brute):
                continue
            pending.append((path,who))
    print('certificates',len(paths),'pending direct checks',len(pending),flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool, journal.open('a') as log:
        fs = {pool.submit(one,path,who,args.brute,args.seconds):(path,who) for path,who in pending}
        completed = 0
        for f in concurrent.futures.as_completed(fs):
            path,who = fs[f]
            rec = f.result()
            ledger['files'].setdefault(str(path),{})[who] = rec
            log.write(json.dumps({'file':str(path),'who':who,'record':rec},separators=(',',':'))+'\n')
            log.flush()
            completed += 1
            if completed % 100 == 0:
                save(ledgerpath,ledger)
            print(who,path.name,rec['result'],rec['seconds'],flush=True)
    for file in paths:
        records = ledger['files'][str(file)]
        if all(records[w]['result']=='PASS' for w in CHECKERS):
            a,b = records['M']['check'],records['F']['check']
            assert sorted(a['solutions']) == sorted(b['claimed']), file
    ledger['brute_Lmax'] = args.brute
    ledger['checker_hashes'] = {w:digest(p) for w,p in CHECKERS.items()}
    ledger['counts'] = {w:dict(collections.Counter(v[w]['result'] for v in ledger['files'].values())) for w in CHECKERS}
    save(ledgerpath,ledger)
    print(json.dumps(ledger['counts']))


if __name__ == '__main__':
    main()
