#!/usr/bin/env python3
"""Run ONE command under the lane resource caps and write a JSON receipt.

Caps: CPU affinity {0,1}; RLIMIT_CPU 120 s; wall 140 s; MALLOC_ARENA_MAX=2;
sampled descendant RSS kill threshold 1.5 GiB (well under the 2 GiB lane bound
and the 6 GiB campaign bound). TMPDIR points inside the lane.
Usage: python3 -I scripts/cap.py <label> -- <cmd> [args...]
"""
import json, os, resource, signal, subprocess, sys, time
from pathlib import Path

LANE = Path(__file__).resolve().parent.parent
RSS_KILL_KIB = 1536 * 1024
CPU_S, WALL_S = 120, 140


def tree_rss_kib(root):
    pids, total = {root}, 0
    changed = True
    while changed:
        changed = False
        for d in os.listdir('/proc'):
            if not d.isdigit() or int(d) in pids:
                continue
            try:
                with open(f'/proc/{d}/stat') as f:
                    ppid = int(f.read().rsplit(')', 1)[1].split()[1])
            except OSError:
                continue
            if ppid in pids:
                pids.add(int(d)); changed = True
    for p in pids:
        try:
            with open(f'/proc/{p}/status') as f:
                for line in f:
                    if line.startswith('VmRSS:'):
                        total += int(line.split()[1])
        except OSError:
            pass
    return total


def main():
    label = sys.argv[1]
    assert sys.argv[2] == '--'
    cmd = sys.argv[3:]
    env = dict(os.environ, MALLOC_ARENA_MAX='2', TMPDIR=str(LANE / 'tmp'),
               PYTHONDONTWRITEBYTECODE='1', OMP_NUM_THREADS='1')

    def pre():
        os.sched_setaffinity(0, {0, 1})
        resource.setrlimit(resource.RLIMIT_CPU, (CPU_S, CPU_S))
        os.setsid()

    t0 = time.time(); peak = 0; killed = None
    out = open(LANE / 'logs' / f'{label}.stdout', 'wb')
    err = open(LANE / 'logs' / f'{label}.stderr', 'wb')
    p = subprocess.Popen(cmd, cwd=LANE, env=env, stdout=out, stderr=err, preexec_fn=pre)
    while p.poll() is None:
        rss = tree_rss_kib(p.pid); peak = max(peak, rss)
        if rss > RSS_KILL_KIB:
            killed = 'rss'; os.killpg(p.pid, signal.SIGKILL)
        elif time.time() - t0 > WALL_S:
            killed = 'wall'; os.killpg(p.pid, signal.SIGKILL)
        time.sleep(0.1)
    ru = resource.getrusage(resource.RUSAGE_CHILDREN)
    rec = {'label': label, 'cmd': cmd, 'exit': p.returncode, 'killed': killed,
           'wall_s': round(time.time() - t0, 3), 'cpu_s': round(ru.ru_utime + ru.ru_stime, 3),
           'sampled_peak_rss_kib': peak, 'maxrss_kib_getrusage': ru.ru_maxrss,
           'caps': {'affinity': [0, 1], 'rlimit_cpu_s': CPU_S, 'wall_s': WALL_S,
                    'rss_kill_kib': RSS_KILL_KIB, 'MALLOC_ARENA_MAX': 2},
           'utc_end': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}
    (LANE / 'logs' / f'{label}.cap.json').write_text(json.dumps(rec, indent=1) + '\n')
    print(json.dumps(rec))
    sys.exit(0 if p.returncode == 0 else 1)


if __name__ == '__main__':
    main()
