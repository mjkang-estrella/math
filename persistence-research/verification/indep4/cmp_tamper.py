# Run M's check_sym.py and my check_sym_F.py on every tamper file and compare verdicts.  python3 -I cmp_tamper.py
import subprocess, glob, json, os, sys
from concurrent.futures import ThreadPoolExecutor
files = sorted(f for f in glob.glob('tamper/*.jsonl') if not os.path.basename(f).startswith('tmp'))
def run(f):
    env = dict(os.environ)
    m = subprocess.run(['bash', '-c', 'ulimit -v 8000000; timeout 1500 python3 -I ../highdim/sym/check_sym.py %s 8' % f], capture_output=True, text=True)
    mine = subprocess.run(['bash', '-c', 'ulimit -v 8000000; timeout 1500 python3 -I check_sym_F.py %s 8 --json' % f], capture_output=True, text=True)
    try: mv = json.loads(m.stdout.strip().splitlines()[-1]); mres = mv.get('result'); mwhy = mv.get('error', '')
    except Exception: mres = 'ERR'; mwhy = (m.stdout + m.stderr)[-200:]
    try: fv = json.loads(mine.stdout.strip().splitlines()[-1]); fres = fv['result']; fwhy = (fv['problems'] or [''])[0]
    except Exception: fres = 'ERR'; fwhy = (mine.stdout + mine.stderr)[-200:]
    return dict(file=f, M=mres, M_why=mwhy[:140], F=fres, F_why=fwhy[:140])
with ThreadPoolExecutor(6) as ex: rows = list(ex.map(run, files))
json.dump(rows, open('cmp_tamper.json', 'w'), indent=1)
for r in rows: print('%-44s M=%-5s F=%-5s %s' % (os.path.basename(r['file']), r['M'], r['F'], 'AGREE' if r['M'] == r['F'] else '*** DISAGREE ***'))
