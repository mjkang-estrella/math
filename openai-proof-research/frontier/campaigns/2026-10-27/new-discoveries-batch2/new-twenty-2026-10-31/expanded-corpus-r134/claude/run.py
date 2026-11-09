#!/usr/bin/env python3
# Capped runner for Claude lane computations (one process at a time).
# Usage: python3 -I claude/run.py NAME script.py args...
# Limits: 2 CPUs affinity, CPU 120 s, wall 140 s, address space 1.5 GiB, MALLOC_ARENA_MAX=2.
import os, resource, subprocess, time, sys, pathlib, json, signal
D = pathlib.Path(__file__).resolve().parent
name = sys.argv[1]
def pre():
    os.setsid()
    os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
    resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
    resource.setrlimit(resource.RLIMIT_AS, (1536 * 1024**2, 1536 * 1024**2))
(D / 'logs').mkdir(exist_ok=True)
t = time.monotonic(); peak = 0; reason = None
env = {'PATH': '/usr/bin:/bin', 'MALLOC_ARENA_MAX': '2', 'PYTHONDONTWRITEBYTECODE': '1', 'OMP_NUM_THREADS': '1'}
with (D / f'logs/{name}.log').open('w') as log:
    p = subprocess.Popen([sys.executable, '-I'] + sys.argv[2:], stdout=log, stderr=subprocess.STDOUT, preexec_fn=pre, env=env, cwd=str(D))
    while p.poll() is None:
        try:
            rss = int(next(l.split()[1] for l in pathlib.Path(f'/proc/{p.pid}/status').read_text().splitlines() if l.startswith('VmRSS:'))) * 1024
            peak = max(peak, rss)
        except (OSError, StopIteration):
            pass
        if time.monotonic() - t > 140:
            reason = 'wall cap'; os.killpg(p.pid, signal.SIGKILL); break
        time.sleep(0.05)
    p.wait()
r = {'name': name, 'argv': sys.argv[2:], 'returncode': p.returncode, 'wall_seconds': round(time.monotonic() - t, 3),
     'sampled_rss_peak_bytes': peak, 'cap_reason': reason,
     'limits': '2-CPU affinity; RLIMIT_CPU 120 s; wall 140 s; RLIMIT_AS 1.5 GiB; MALLOC_ARENA_MAX=2; python3 -I'}
(D / f'logs/{name}.receipt.json').write_text(json.dumps(r, indent=2) + '\n')
print(json.dumps(r))
print((D / f'logs/{name}.log').read_text()[-6000:])
