#!/usr/bin/env python3
# Capped runner for this lane (one process at a time).
# Usage: python3 -I scripts/run.py NAME script.py args...   (run from the lane directory)
# Limits: first 2 CPUs (affinity), RLIMIT_CPU 120 s, wall 140 s, RLIMIT_AS 1.75 GiB,
# MALLOC_ARENA_MAX=2, OMP/BLAS threads 1, TMPDIR lane-local, python3 -I.
import os, resource, subprocess, time, sys, pathlib, json, signal, hashlib
LANE = pathlib.Path(__file__).resolve().parent.parent
name = sys.argv[1]
def pre():
    os.setsid()
    os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
    resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
    resource.setrlimit(resource.RLIMIT_AS, (1792 * 1024**2, 1792 * 1024**2))
(LANE / 'logs').mkdir(exist_ok=True)
env = {'PATH': '/usr/bin:/bin', 'MALLOC_ARENA_MAX': '2', 'PYTHONDONTWRITEBYTECODE': '1',
       'OMP_NUM_THREADS': '1', 'OPENBLAS_NUM_THREADS': '1', 'MKL_NUM_THREADS': '1',
       'TMPDIR': str(LANE / 'tmp'), 'HOME': str(LANE / 'tmp')}
t = time.monotonic(); peak = 0; reason = None
script = pathlib.Path(sys.argv[2])
with (LANE / f'logs/{name}.log').open('w') as log:
    p = subprocess.Popen([sys.executable, '-I'] + sys.argv[2:], stdout=log, stderr=subprocess.STDOUT,
                         preexec_fn=pre, env=env, cwd=str(LANE))
    while p.poll() is None:
        try:
            rss = int(next(l.split()[1] for l in pathlib.Path(f'/proc/{p.pid}/status').read_text().splitlines()
                           if l.startswith('VmRSS:'))) * 1024
            peak = max(peak, rss)
        except (OSError, StopIteration):
            pass
        if time.monotonic() - t > 140:
            reason = 'wall cap'; os.killpg(p.pid, signal.SIGKILL); break
        time.sleep(0.05)
    p.wait()
r = {'name': name, 'argv': sys.argv[2:], 'returncode': p.returncode, 'wall_seconds': round(time.monotonic() - t, 3),
     'sampled_rss_peak_bytes': peak, 'cap_reason': reason,
     'script_sha256': hashlib.sha256((LANE / script).read_bytes()).hexdigest() if (LANE / script).exists() else None,
     'log_sha256': hashlib.sha256((LANE / f'logs/{name}.log').read_bytes()).hexdigest(),
     'limits': '2-CPU affinity; RLIMIT_CPU 120 s; wall 140 s; RLIMIT_AS 1.75 GiB; MALLOC_ARENA_MAX=2; python3 -I'}
(LANE / f'logs/{name}.receipt.json').write_text(json.dumps(r, indent=2) + '\n')
print(json.dumps(r))
print((LANE / f'logs/{name}.log').read_text()[-8000:])
