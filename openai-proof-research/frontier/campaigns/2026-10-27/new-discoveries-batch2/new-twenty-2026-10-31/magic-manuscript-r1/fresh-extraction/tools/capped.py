"""Run one command under the lane caps and write LABEL.log / LABEL.receipt.json into DIR.
Usage: python3 -I tools/capped.py DIR LABEL CWD -- CMD...
Caps: <= 2 CPUs, RLIMIT_CPU 120 s, wall 140 s, RLIMIT_AS 64 GiB, MALLOC_ARENA_MAX=2,
sampled (50 ms) private RSS (RssAnon+RssShmem of the process group) 6 GiB guard, and a
systemd user scope with MemoryMax=6G when available."""
import json, os, pathlib, resource, shutil, signal, subprocess, sys, time
out, label, cwd = pathlib.Path(sys.argv[1]), sys.argv[2], sys.argv[3]
assert sys.argv[4] == '--'
cmd = sys.argv[5:]
out.mkdir(parents=True, exist_ok=True)
PAGE = os.sysconf('SC_PAGE_SIZE'); CPUS = sorted(os.sched_getaffinity(0))[:2]
pre = []
if shutil.which('systemd-run') and 'XDG_RUNTIME_DIR' in os.environ:
    pre = ['systemd-run', '--user', '--scope', '-q', '-p', 'MemoryMax=6G', '-p', 'MemorySwapMax=0', '-p', 'CPUQuota=200%']
    if subprocess.run(pre + ['/usr/bin/true'], capture_output=True, timeout=60).returncode != 0:
        pre = []
env = dict(os.environ, MALLOC_ARENA_MAX='2', LEAN_NUM_THREADS='1')


def rss(pgid):
    total = private = 0
    for q in pathlib.Path('/proc').glob('[0-9]*'):
        try:
            s = (q / 'stat').read_text(); f = s[s.rindex(')') + 2:].split()
            if int(f[2]) != pgid: continue
            total += int(f[21]) * PAGE
            for line in (q / 'status').read_text().splitlines():
                if line.startswith(('RssAnon:', 'RssShmem:')): private += int(line.split()[1]) * 1024
        except (OSError, ValueError, IndexError):
            pass
    return total, private


def setup():
    os.setsid(); os.sched_setaffinity(0, CPUS)
    resource.setrlimit(resource.RLIMIT_CPU, (120, 120)); resource.setrlimit(resource.RLIMIT_AS, (64 << 30, 64 << 30))


t0 = time.monotonic(); peak = peakp = 0; why = None
with (out / (label + '.log')).open('w') as f:
    p = subprocess.Popen(pre + cmd, cwd=cwd, env=env, stdout=f, stderr=subprocess.STDOUT, preexec_fn=setup)
    while p.poll() is None:
        a, b = rss(p.pid); peak, peakp = max(peak, a), max(peakp, b)
        if b > 6 << 30 or time.monotonic() - t0 > 140:
            why = 'RSS' if b > 6 << 30 else 'wall'; os.killpg(p.pid, signal.SIGKILL); break
        time.sleep(0.05)
    p.wait()
ru = resource.getrusage(resource.RUSAGE_CHILDREN)
r = {'label': label, 'command': pre + cmd, 'cwd': cwd, 'cpus': CPUS, 'exit': p.returncode, 'killed_reason': why,
     'wall_seconds': round(time.monotonic() - t0, 3), 'cpu_seconds': round(ru.ru_utime + ru.ru_stime, 2),
     'peak_sampled_private_rss_bytes': peakp, 'peak_sampled_total_vmrss_bytes': peak, 'systemd_scope': bool(pre),
     'limits': '2 CPUs; RLIMIT_CPU 120 s; wall 140 s; AS 64 GiB; private RSS 6 GiB sampled; MemoryMax=6G scope if available',
     'utc_end': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}
(out / (label + '.receipt.json')).write_text(json.dumps(r, indent=2))
print(json.dumps({k: r[k] for k in ('label', 'exit', 'killed_reason', 'wall_seconds', 'peak_sampled_private_rss_bytes')}))
