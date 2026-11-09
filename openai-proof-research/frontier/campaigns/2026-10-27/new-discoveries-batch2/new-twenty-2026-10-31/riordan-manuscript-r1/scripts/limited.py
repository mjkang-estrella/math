"""Capped runner (adapted from r119 scripts/limited.py; logs land in THIS lane).
usage: python3 -I scripts/limited.py NAME cmd args...
Caps: 2 CPUs (affinity), RLIMIT_CPU 120 s, RLIMIT_AS 6 GiB, sampled RSS 6 GiB, wall 140 s.
Env for the child: MALLOC_ARENA_MAX=2, TMPDIR and caches lane-local."""
import os, resource, subprocess, time, sys, pathlib, json, signal
D = pathlib.Path(__file__).resolve().parents[1]
name = sys.argv[1]
def pre():
    os.setsid()
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
    resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
    AS = 6 * 1024**3
    resource.setrlimit(resource.RLIMIT_AS, (AS, AS))
env = {'PATH': '/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:/usr/bin:/bin', 'LEAN_NUM_THREADS': '1', 'MALLOC_ARENA_MAX': '2', 'TMPDIR': str(D / 'tmp'),
       'XDG_CACHE_HOME': str(D / 'tmp' / 'cache'), 'PYTHONDONTWRITEBYTECODE': '1',
       'OPENBLAS_NUM_THREADS': '1', 'OMP_NUM_THREADS': '2'}
t = time.monotonic(); peak = 0; reason = None
with (D / f'logs/{name}.log').open('x') as log:
    p = subprocess.Popen(sys.argv[2:], stdout=log, stderr=subprocess.STDOUT, preexec_fn=pre, env=env, cwd=str(D))
    while p.poll() is None:
        try:
            rss = int(next(l.split()[1] for l in pathlib.Path(f'/proc/{p.pid}/status').read_text().splitlines() if l.startswith('VmRSS:'))) * 1024
            peak = max(peak, rss)
        except (OSError, StopIteration):
            pass
        if peak > 6 * 1024**3 or time.monotonic() - t > 140:
            reason = 'RSS or wall cap'; os.killpg(p.pid, signal.SIGKILL); break
        time.sleep(.05)
    p.wait()
r = {'name': name, 'argv': sys.argv[2:], 'returncode': p.returncode, 'wall_seconds': round(time.monotonic() - t, 3),
     'sampled_process_rss_peak_bytes': peak, 'cap_reason': reason,
     'utc_end': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
     'limits': '2 CPUs; CPU 120 s; wall 140 s; sampled RSS 6 GiB; AS 6 GiB; MALLOC_ARENA_MAX=2'}
(D / f'logs/{name}.receipt.json').write_text(json.dumps(r, indent=2) + '\n'); print(r)

sys.exit(p.returncode if p.returncode >= 0 else 1)
