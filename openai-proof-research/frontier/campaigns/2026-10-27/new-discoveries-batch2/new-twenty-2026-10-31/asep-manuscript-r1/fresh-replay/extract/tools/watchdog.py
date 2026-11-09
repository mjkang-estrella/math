"""Resource-capped runner for one command (used for every Lean call of the replay).

    python3 -I watchdog.py RECEIPT.json STDOUT STDERR CWD -- cmd args...

Caps per call: 2 CPUs (sched affinity), RLIMIT_CPU 120 s, wall 140 s, MALLOC_ARENA_MAX=2 and a
sampled RSS watchdog that kills the whole process group when the summed RSS of the process tree
exceeds 6 GiB.  When a systemd user manager is reachable the command also runs in a transient scope
with MemoryMax=6G and MemorySwapMax=0 as a hard backstop (set ASEP_NO_SCOPE=1 to disable).
The environment of the child is exactly the environment of this process plus MALLOC_ARENA_MAX=2;
the replay driver passes a minimal environment.
"""
import json, os, resource, shutil, signal, subprocess, sys, time, datetime

RSS_CAP = 6 * 1024 ** 3
CPU_CAP = 120
WALL_CAP = 140
SAMPLE = 0.05


def proc_tree(root):
    kids = {}
    for d in os.listdir('/proc'):
        if not d.isdigit():
            continue
        try:
            with open(f'/proc/{d}/stat') as f:
                s = f.read()
            ppid = int(s[s.rindex(')') + 2:].split()[1])
            kids.setdefault(ppid, []).append(int(d))
        except (OSError, ValueError, IndexError):
            pass
    out, todo = [], [root]
    while todo:
        p = todo.pop()
        out.append(p)
        todo.extend(kids.get(p, []))
    return out


def mem(pid):
    rss = priv = 0
    try:
        with open(f'/proc/{pid}/smaps_rollup') as f:
            for line in f:
                if line.startswith('Rss:'):
                    rss += int(line.split()[1]) * 1024
                elif line.startswith(('Private_Clean:', 'Private_Dirty:')):
                    priv += int(line.split()[1]) * 1024
    except (OSError, ValueError):
        pass
    return rss, priv


def scope_available(env):
    if os.environ.get('ASEP_NO_SCOPE') == '1' or not shutil.which('systemd-run'):
        return False
    try:
        r = subprocess.run(['systemd-run', '--user', '--scope', '--quiet', '-p', 'MemoryMax=6G', 'true'],
                           env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=10)
        return r.returncode == 0
    except (OSError, subprocess.TimeoutExpired):
        return False


def main():
    receipt, out, err, cwd = sys.argv[1:5]
    assert sys.argv[5] == '--'
    cmd = sys.argv[6:]
    env = dict(os.environ, MALLOC_ARENA_MAX='2')
    cpus = sorted(os.sched_getaffinity(0))[:2]
    scope = scope_available(env)
    full = (['systemd-run', '--user', '--scope', '--quiet', '-p', 'MemoryMax=6G', '-p', 'MemorySwapMax=0']
            if scope else []) + cmd

    def pre():
        os.setsid()
        os.sched_setaffinity(0, set(cpus))
        resource.setrlimit(resource.RLIMIT_CPU, (CPU_CAP, CPU_CAP))

    t0 = time.monotonic()
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    killed = None
    peak_rss = peak_priv = samples = 0
    with open(out, 'wb') as fo, open(err, 'wb') as fe:
        p = subprocess.Popen(full, cwd=cwd, env=env, stdout=fo, stderr=fe, preexec_fn=pre)
        while p.poll() is None:
            rss = priv = 0
            for q in proc_tree(p.pid):
                a, b = mem(q)
                rss += a
                priv += b
            samples += 1
            peak_rss = max(peak_rss, rss)
            peak_priv = max(peak_priv, priv)
            if rss > RSS_CAP:
                killed = 'rss'
            elif time.monotonic() - t0 > WALL_CAP:
                killed = 'wall'
            if killed:
                try:
                    os.killpg(p.pid, signal.SIGKILL)
                except OSError:
                    pass
                p.wait()
                break
            time.sleep(SAMPLE)
    wall = time.monotonic() - t0
    ru = resource.getrusage(resource.RUSAGE_CHILDREN)
    rec = {
        'command': cmd, 'cwd': cwd, 'rc': p.returncode, 'killed': killed,
        'utc_start': start, 'utc_end': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'wall_seconds': round(wall, 3), 'cpu_seconds': round(ru.ru_utime + ru.ru_stime, 3),
        'peak_sampled_rss_bytes': peak_rss, 'peak_sampled_private_rss_bytes': peak_priv,
        'rusage_maxrss_bytes': ru.ru_maxrss * 1024, 'samples': samples, 'sample_interval_seconds': SAMPLE,
        'caps': {'cpus': cpus, 'rlimit_cpu_seconds': CPU_CAP, 'wall_seconds': WALL_CAP,
                 'sampled_rss_bytes': RSS_CAP, 'MALLOC_ARENA_MAX': '2',
                 'systemd_scope_MemoryMax': '6G' if scope else None},
    }
    with open(receipt, 'w') as f:
        json.dump(rec, f, indent=1)
    sys.exit(p.returncode if p.returncode is not None else 1)


if __name__ == '__main__':
    main()
