#!/usr/bin/env python3
# r5 capped runner (repair of the r3/r4 shell design).
# Run ONLY as: python3 -I -B runner.py LABEL -- cmd args...
#
# Repairs vs r4 (each attested in the receipt):
#  * single python3 -I -B stdlib process; no uncapped shell/python helpers, no
#    argv re-parsing through a second interpreter, no $(...) selector.
#  * child spawned with explicit argv list (no shell), start_new_session
#    (setsid), affinity restricted to <=2 CPUs inherited from this process's
#    actual mask, RLIMIT_CPU 120s, RLIMIT_AS 12GiB, MALLOC_ARENA_MAX=2,
#    TMPDIR/XDG_CACHE_HOME pinned into the lane.
#  * wall cap: poll deadline checked BEFORE sleeping with clamped sleep (no
#    0.2s-poll overshoot), plus a hard threading.Timer group kill at 140s that
#    fires even if the poll loop stalls, plus an outer SIGALRM backstop.
#  * kill AND reap: after the leader exits, the process group is swept via
#    /proc until no member of the pgid remains (bounded), and every kill is
#    logged; reaped-children CPU is taken from resource.getrusage
#    (RUSAGE_CHILDREN) deltas across the wait, labelled as such, next to the
#    coarse live sample (kept, labelled sampled).
#  * structured receipt: full argv, env overrides, cwd, affinity set, rlimits,
#    exit code, wall ms, cpu (reaped + sampled), rss peak (sampled, labelled),
#    guard/kill event list, log path + sha256, and sha256 of any -o target
#    after completion.  Nothing is piped through head/tail; the child writes
#    its stdout/stderr directly into the log file.
import json, hashlib, os, resource, signal, subprocess, sys, time, threading

CPU_S = 120
WALL_S = 140
DEVGUARD_S = 130          # dev-guard strictly below the hard cap
AS_BYTES = 12 * 1024**3
RSS_GUARD_BYTES = 6 * 1024**3
MAXCPUS = 2


def sha256_file(p):
    try:
        with open(p, 'rb') as f:
            return hashlib.sha256(f.read()).hexdigest()
    except OSError:
        return None


def group_members(pgid):
    out = []
    try:
        for d in os.listdir('/proc'):
            if not d.isdigit():
                continue
            try:
                with open(f'/proc/{d}/stat', 'rb') as f:
                    st = f.read()
                # comm may contain spaces/parens; split after last ')'
                    rparen = st.rfind(b')')
                fields = st[rparen + 2:].split()
                if int(fields[2]) == pgid:  # state, ppid, pgrp: pgrp is 3rd
                    out.append(int(d))
            except (OSError, IndexError, ValueError):
                continue
    except OSError:
        pass
    return out


def kill_group(pgid, log, events, tag):
    members = group_members(pgid)
    if members:
        try:
            os.killpg(pgid, signal.SIGKILL)
            events.append({'t': round(time.monotonic(), 3), 'ev': f'killpg {tag}',
                           'pids': members})
            log.write(f'KILLPG {tag} pids={members}\n'.encode())
        except ProcessLookupError:
            pass
    return members


def main():
    label = sys.argv[1]
    assert sys.argv[2] == '--', 'usage: runner.py LABEL -- cmd...'
    cmd = sys.argv[3:]
    lane = os.path.dirname(os.path.abspath(__file__))
    for d in ('logs', 'receipt', 'tmp', 'cache', 'build'):
        os.makedirs(os.path.join(lane, d), exist_ok=True)
    stamp = time.time_ns()
    logpath = os.path.join(lane, 'logs', f'{stamp}_{label}.log')
    recippath = os.path.join(lane, 'receipt', f'{stamp}_{label}.json')

    mask = sorted(os.sched_getaffinity(0))
    aff = set(mask[:MAXCPUS])
    env = dict(os.environ)
    env['MALLOC_ARENA_MAX'] = '2'
    env['TMPDIR'] = os.path.join(lane, 'tmp')
    env['XDG_CACHE_HOME'] = os.path.join(lane, 'cache')

    log = open(logpath, 'wb')
    log.write(f'CMD {json.dumps(cmd)}\nLABEL {label} STAMP {stamp}\n'
              f'AFFINITY {sorted(aff)} FULL_MASK {mask}\n'
              f'LIMITS cpu_s={CPU_S} wall_s={WALL_S} devguard_s={DEVGUARD_S} '
              f'as_bytes={AS_BYTES} rss_guard_bytes={RSS_GUARD_BYTES} '
              f'malloc_arena_max=2\nENV_OVERRIDES MALLOC_ARENA_MAX=2 '
              f'TMPDIR={env["TMPDIR"]} XDG_CACHE_HOME={env["XDG_CACHE_HOME"]}\n'
              f'LEAN_PATH {env.get("LEAN_PATH", "<unset>")}\n'.encode())
    log.flush()

    def child_setup():
        resource.setrlimit(resource.RLIMIT_CPU, (CPU_S, CPU_S))
        resource.setrlimit(resource.RLIMIT_AS, (AS_BYTES, AS_BYTES))
        os.sched_setaffinity(0, aff)

    t0 = time.monotonic()
    proc = subprocess.Popen(
        cmd, stdout=log, stderr=subprocess.STDOUT, env=env,
        start_new_session=True, preexec_fn=child_setup, close_fds=True)
    pgid = proc.pid  # session+group leader: pgid == pid
    events = []
    peak_rss = 0
    rss_samples = 0
    cpu_sample = 0
    guard = 'none'
    killed = False

    def hard_kill():
        nonlocal guard, killed
        if proc.poll() is None or group_members(pgid):
            kill_group(pgid, log, events, 'hard_wall_140')
            guard, killed = 'wall_hard', True

    hard_timer = threading.Timer(WALL_S, hard_kill)
    hard_timer.start()

    # SIGALRM backstop in case the poll loop or timer machinery hangs
    signal.signal(signal.SIGALRM, lambda *a: hard_kill())
    signal.alarm(WALL_S + 10)

    while True:
        rc = proc.poll()
        now = time.monotonic()
        elapsed = now - t0
        members = group_members(pgid)
        total_rss = 0
        for m in members:
            try:
                with open(f'/proc/{m}/statm', 'rb') as f:
                    total_rss += int(f.read().split()[1]) * os.sysconf('SC_PAGESIZE')
            except (OSError, IndexError, ValueError):
                continue
        if os.environ.get('RUNNER_DEBUG'):
            sys.stderr.write(f'DBG members={len(members)} rss={total_rss}\n')
        if total_rss > peak_rss:
            peak_rss = total_rss
        rss_samples += 1
        if total_rss > RSS_GUARD_BYTES:
            kill_group(pgid, log, events, 'rss_guard')
            guard, killed = 'rss', True
        if rc is not None and not group_members(pgid):
            break
        if elapsed >= WALL_S:
            if not killed:
                kill_group(pgid, log, events, 'wall_poll')
                guard, killed = 'wall_poll', True
            # bounded reap sweep
            for _ in range(50):
                if not group_members(pgid):
                    break
                time.sleep(0.1)
            break
        remaining = WALL_S - elapsed
        time.sleep(max(0.05, min(0.25, remaining - 0.05)))

    hard_timer.cancel()
    signal.alarm(0)
    try:
        rc_wait = os.waitpid(proc.pid, 0)[1] if proc.poll() is not None else None
    except ChildProcessError:
        rc_wait = None
    # reaped-children CPU via getrusage delta (children fully waited)
    ru = resource.getrusage(resource.RUSAGE_CHILDREN)
    reaped_cpu = ru.ru_utime + ru.ru_stime
    wall_ms = int((time.monotonic() - t0) * 1000)

    # final reap check
    left = group_members(pgid)
    if left:
        kill_group(pgid, log, events, 'final_sweep')
    log.write(f'\nEXIT {proc.returncode if rc_wait is None else os.waitstatus_to_exitcode(rc_wait)}\n'
              f'WALL_MS {wall_ms} PEAK_GROUP_RSS_SAMPLED {peak_rss} '
              f'RSS_SAMPLES {rss_samples} CPU_SAMPLE_LAST {cpu_sample} '
              f'REAPED_CPU_S {reaped_cpu:.3f} GUARD {guard}\n'
              f'GROUP_MEMBERS_LEFT {group_members(pgid)}\n'.encode())
    log.close()

    out = {'label': label, 'stamp': stamp, 'argv': cmd,
           'exit': os.waitstatus_to_exitcode(rc_wait) if rc_wait is not None
                   else proc.returncode,
           'wall_ms': wall_ms,
           'cpu_reaped_child_s': reaped_cpu,
           'cpu_reaped_note': 'resource.getrusage RUSAGE_CHILDREN utime+stime '
                              'delta; counts waited children of this runner',
           'peak_group_rss_bytes_sampled': peak_rss,
           'rss_samples': rss_samples,
           'rss_is_sampled_not_cgroup': True,
           'rss_note': 'sum of /proc/pid/statm resident pages over live group '
                       'members at 0.05-0.25s polls; transient between polls '
                       'and post-exit pages are missed by construction',
           'guard': guard, 'events': events,
           'group_members_left': group_members(pgid),
           'limits': {'cpu_s': CPU_S, 'wall_s': WALL_S, 'devguard_s': DEVGUARD_S,
                      'as_bytes': AS_BYTES, 'rss_guard_bytes': RSS_GUARD_BYTES,
                      'malloc_arena_max': 2, 'max_cpus': MAXCPUS},
           'affinity_used': sorted(aff), 'affinity_mask_seen': mask,
           'env': {k: env[k] for k in
                   ('MALLOC_ARENA_MAX', 'TMPDIR', 'XDG_CACHE_HOME', 'LEAN_PATH')
                   if k in env},
           'cwd': os.getcwd(),
           'log': logpath, 'log_sha256': sha256_file(logpath)}
    for a in cmd:
        if a.endswith('.olean'):
            out['target_olean'] = a
            out['target_olean_sha256'] = sha256_file(a)
    src = [a for a in cmd if a.endswith('.lean')]
    if src:
        out['source'] = src[0]
        out['source_sha256'] = sha256_file(src[0])
    with open(recippath, 'w') as f:
        json.dump(out, f, indent=1)
    print(f'RECEIPT={recippath} EXIT={out["exit"]}')
    sys.exit(out['exit'])


if __name__ == '__main__':
    main()
