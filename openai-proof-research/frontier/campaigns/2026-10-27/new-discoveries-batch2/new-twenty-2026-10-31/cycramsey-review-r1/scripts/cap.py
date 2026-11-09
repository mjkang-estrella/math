"""Resource wrapper: cap.py NAME cmd...  -> logs/NAME.log, logs/NAME.receipt.json
Limits: 2 CPUs (affinity), RLIMIT_CPU 120 s, wall 140 s, sampled RSS 6 GiB, MALLOC_ARENA_MAX=2."""
import os, resource, subprocess, time, sys, pathlib, json, signal, datetime
D = pathlib.Path(__file__).resolve().parents[1]
name = sys.argv[1]; cmd = sys.argv[2:]
def pre():
    os.setsid()
    os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
    resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
env = {**os.environ, 'MALLOC_ARENA_MAX': '2', 'OMP_NUM_THREADS': '2', 'OPENBLAS_NUM_THREADS': '1',
       'TMPDIR': str(D / 'tmp'), 'PYTHONDONTWRITEBYTECODE': '1'}
start = datetime.datetime.now(datetime.timezone.utc).isoformat()
t = time.monotonic(); peak = 0; reason = None
with (D / f'logs/{name}.log').open('w') as log:
    p = subprocess.Popen(cmd, stdout=log, stderr=subprocess.STDOUT, preexec_fn=pre, env=env)
    while p.poll() is None:
        try:
            for pid in [p.pid] + [int(x) for x in pathlib.Path(f'/proc/{p.pid}/task/{p.pid}/children').read_text().split()]:
                for l in pathlib.Path(f'/proc/{pid}/status').read_text().splitlines():
                    if l.startswith('VmRSS:'): peak = max(peak, int(l.split()[1]) * 1024)
        except (OSError, ValueError): pass
        if peak > 6 * 1024**3: reason = 'RSS cap'; os.killpg(p.pid, signal.SIGKILL); break
        if time.monotonic() - t > 140: reason = 'wall cap'; os.killpg(p.pid, signal.SIGKILL); break
        time.sleep(0.05)
    p.wait()
r = {'name': name, 'cmd': cmd, 'utc_start': start, 'returncode': p.returncode,
     'wall_seconds': round(time.monotonic() - t, 3), 'sampled_rss_peak_bytes': peak, 'cap_reason': reason,
     'limits': '2 CPUs affinity; RLIMIT_CPU 120 s; wall 140 s; sampled RSS 6 GiB; MALLOC_ARENA_MAX=2'}
(D / f'logs/{name}.receipt.json').write_text(json.dumps(r, indent=2) + '\n'); print(json.dumps(r))
