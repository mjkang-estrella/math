"""Serial Lean invocation with a sampled 3 GiB RSS ceiling and receipts."""
import hashlib, json, os, pathlib, signal, subprocess, sys, time
base = pathlib.Path(__file__).resolve().parent
wd = base / sys.argv[1]
args = sys.argv[2:]
logs = base / 'logs'
logs.mkdir(exist_ok=True)
stem = sys.argv[1].replace('/', '_') + '-' + pathlib.Path(args[-1]).stem
log = logs / (stem + '.log')
env = dict(os.environ, OPENBLAS_NUM_THREADS='1', OMP_NUM_THREADS='1',
           MKL_NUM_THREADS='1', NUMEXPR_NUM_THREADS='1')
start = time.monotonic()
peak = 0
reason = None
with log.open('w') as out:
    p = subprocess.Popen([sys.executable, str(wd / 'run_lean.py'), *args], cwd=wd,
        stdout=out, stderr=subprocess.STDOUT, env=env, start_new_session=True)
    while p.poll() is None:
        group_rss = 0
        for d in pathlib.Path('/proc').iterdir():
            if not d.name.isdigit():
                continue
            try:
                if os.getpgid(int(d.name)) == p.pid:
                    for line in (d / 'status').read_text().splitlines():
                        if line.startswith('VmRSS:'):
                            group_rss += int(line.split()[1]) * 1024
            except (ProcessLookupError, FileNotFoundError, PermissionError):
                pass
        peak = max(peak, group_rss)
        if peak >= 3 * 1024**3 or time.monotonic() - start > 180:
            reason = 'RSS ceiling' if peak >= 3 * 1024**3 else 'wall limit'
            os.killpg(p.pid, signal.SIGKILL)
            break
        time.sleep(.1)
    code = p.wait()
receipt = dict(args=args, cwd=str(wd), exit=code, elapsed=time.monotonic()-start,
    sampled_group_peak_rss=peak, termination_reason=reason,
    source_sha256=hashlib.sha256((wd / args[-1]).read_bytes()).hexdigest())
(logs / (stem + '.json')).write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps(receipt))
print(log.read_text(), end='')
sys.exit(code)
