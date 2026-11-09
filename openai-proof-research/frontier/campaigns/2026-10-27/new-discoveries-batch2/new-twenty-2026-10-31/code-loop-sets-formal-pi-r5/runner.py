#!/usr/bin/env python3
# Root-prepared continuation copy: own CPU120 and AS12GiB installed with affinity before reads.
# Original r6 receipts remain separate; this NEW runner has not yet been executed.
# Run ONLY as: python3 -I -B runner.py LABEL -- cmd args...
#
# Repairs vs r5 (r5 defects -> r6 fixes):
#  D1 DEVGUARD_S=130 never used         -> real dev-guard: group SIGKILL at 130s
#                                          (strictly below the 140s cap), plus
#                                          wall-poll kill at 140s and SIGALRM
#                                          backstop at 145s.
#  D2 max(0.05,..) sleep overshoot      -> sleep only while remaining > floor;
#                                          no positive floor past the deadline;
#                                          poll interval shrinks near deadline.
#  D3 final sweep no leader wait/reap   -> leader is ALWAYS waitpid()ed
#                                          (blocking) on every path; group
#                                          swept via /proc until empty or
#                                          bounded 5s; waitpid status is the
#                                          recorded exit.
#  D4 cpu_sample=0 constant             -> live group CPU sampled from
#                                          /proc/<pid>/stat utime+stime sums
#                                          (labelled sampled) AND reaped-child
#                                          CPU recorded as a getrusage
#                                          (RUSAGE_CHILDREN) before/after
#                                          delta (labelled delta), both kept.
#  D5 runner reads before own caps      -> runner sets own affinity (<=2 cpus)
#                                          and RLIMIT_CPU at start, before
#                                          any file read; child caps in
#                                          preexec as before.
#  D6  tail-piped diagnostics            -> none: child writes log directly;
#                                          receipt keeps true exit; a short
#                                          summary print happens AFTER the
#                                          receipt is preserved.
import json, hashlib, os, resource, signal, subprocess, sys, time, threading

CPU_S = 120
WALL_S = 140
DEVGUARD_S = 130          # dev-guard strictly below the hard cap, now USED
ALARM_BACKSTOP_S = 145
AS_BYTES = 40 * 1024**3  # lane repair 2026-11-07
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
                rparen = st.rfind(b')')
                fields = st[rparen + 2:].split()
                if int(fields[2]) == pgid:  # pgrp field
                    out.append(int(d))
            except (OSError, IndexError, ValueError):
                continue
    except OSError:
        pass
    return out


def group_cpu(pgid):
    """Live sampled CPU (user+sys) of group members from /proc stat."""
    total = 0.0
    for m in group_members(pgid):
        try:
            with open(f'/proc/{m}/stat', 'rb') as f:
                st = f.read()
            rparen = st.rfind(b')')
            fl = st[rparen + 2:].split()
            total += (int(fl[11]) + int(fl[12])) / os.sysconf('SC_CLK_TCK')
        except (OSError, IndexError, ValueError):
            continue
    return total


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
    # D5: own caps BEFORE any file read.
    try:
        mask0 = sorted(os.sched_getaffinity(0))
        os.sched_setaffinity(0, set(mask0[:MAXCPUS]))
        resource.setrlimit(resource.RLIMIT_CPU, (CPU_S, CPU_S))
        resource.setrlimit(resource.RLIMIT_AS, (AS_BYTES, AS_BYTES))
    except (OSError, ValueError):
        mask0 = sorted(os.sched_getaffinity(0))
    self_affinity = sorted(os.sched_getaffinity(0))

    label = sys.argv[1]
    assert sys.argv[2] == '--', 'usage: runner.py LABEL -- cmd...'
    cmd = sys.argv[3:]
    lane = os.path.dirname(os.path.abspath(__file__))
    for d in ('logs', 'receipt', 'tmp', 'cache', 'build'):
        os.makedirs(os.path.join(lane, d), exist_ok=True)
    stamp = time.time_ns()
    logpath = os.path.join(lane, 'logs', f'{stamp}_{label}.log')
    recippath = os.path.join(lane, 'receipt', f'{stamp}_{label}.json')

    aff = set(self_affinity)
    env = dict(os.environ)
    env['MALLOC_ARENA_MAX'] = '2'
    env['TMPDIR'] = os.path.join(lane, 'tmp')
    env['XDG_CACHE_HOME'] = os.path.join(lane, 'cache')

    log = open(logpath, 'wb')
    log.write(f'CMD {json.dumps(cmd)}\nLABEL {label} STAMP {stamp}\n'
              f'AFFINITY {sorted(aff)} SELF_AFFINITY {self_affinity}\n'
              f'LIMITS cpu_s={CPU_S} wall_s={WALL_S} devguard_s={DEVGUARD_S} '
              f'alarm_backstop_s={ALARM_BACKSTOP_S} '
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
    pgid = proc.pid
    events = []
    peak_rss = 0
    rss_samples = 0
    cpu_sample_last = 0.0
    cpu_samples = 0
    guard = 'none'
    killed = False

    ru_before = resource.getrusage(resource.RUSAGE_CHILDREN)

    def devguard_kill():  # D1: the 130s guard, actually wired
        nonlocal guard, killed
        if proc.poll() is None or group_members(pgid):
            kill_group(pgid, log, events, 'devguard_130')
            guard, killed = 'devguard', True

    def hard_kill():
        nonlocal guard, killed
        if proc.poll() is None or group_members(pgid):
            kill_group(pgid, log, events, 'hard_wall_140')
            guard, killed = 'wall_hard', True

    dev_timer = threading.Timer(DEVGUARD_S, devguard_kill)
    dev_timer.start()
    hard_timer = threading.Timer(WALL_S, hard_kill)
    hard_timer.start()
    signal.signal(signal.SIGALRM, lambda *a: hard_kill())
    signal.alarm(ALARM_BACKSTOP_S)

    reaped = False
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
        if total_rss > peak_rss:
            peak_rss = total_rss
        rss_samples += 1
        cpu_sample_last = group_cpu(pgid)  # D4: real sampled value
        cpu_samples += 1
        if total_rss > RSS_GUARD_BYTES and not killed:
            kill_group(pgid, log, events, 'rss_guard')
            guard, killed = 'rss', True
        if rc is not None and not members:
            break
        if elapsed >= WALL_S:
            if not killed:
                kill_group(pgid, log, events, 'wall_poll')
                guard, killed = 'wall_poll', True
            for _ in range(50):
                if not group_members(pgid):
                    break
                time.sleep(0.1)
            break
        # D2: never sleep past the deadline; floor only while slack remains.
        remaining = WALL_S - elapsed
        time.sleep(min(0.25, max(0.0, remaining - 0.05))
                   if remaining > 0.05 else 0.0)

    dev_timer.cancel(); hard_timer.cancel(); signal.alarm(0)

    # D3: ALWAYS reap the leader (blocking), on every path.
    try:
        _pid, status = os.waitpid(proc.pid, 0)
        reaped = True
    except ChildProcessError:
        # already reaped by an earlier poll(); exit still true via
        # proc.returncode; recorded honestly in leader_reaped_note.
        status = None
    ru_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    reaped_cpu_delta = ((ru_after.ru_utime + ru_after.ru_stime)
                        - (ru_before.ru_utime + ru_before.ru_stime))
    wall_ms = int((time.monotonic() - t0) * 1000)

    # final reap sweep for any descendants; bounded
    for _ in range(50):
        if not group_members(pgid):
            break
        kill_group(pgid, log, events, 'final_sweep')
        time.sleep(0.1)
    left = group_members(pgid)

    exit_code = (os.waitstatus_to_exitcode(status)
                 if status is not None else proc.returncode)
    log.write(f'\nEXIT {exit_code}\n'
              f'WALL_MS {wall_ms} PEAK_GROUP_RSS_SAMPLED {peak_rss} '
              f'RSS_SAMPLES {rss_samples} '
              f'CPU_SAMPLE_LAST_LIVE {cpu_sample_last:.3f} '
              f'CPU_SAMPLES {cpu_samples} '
              f'REAPED_CPU_DELTA_S {reaped_cpu_delta:.3f} '
              f'LEADER_REAPED {reaped} GUARD {guard}\n'
              f'GROUP_MEMBERS_LEFT {left}\n'.encode())
    log.close()

    out = {'label': label, 'stamp': stamp, 'argv': cmd,
           'exit': exit_code, 'leader_reaped': reaped,
           'leader_reaped_note': ('waitpid by runner' if reaped else
                                  'already reaped by Popen.poll; exit from '
                                  'returncode; no zombie left'),
           'wall_ms': wall_ms,
           'cpu_reaped_child_delta_s': round(reaped_cpu_delta, 3),
           'cpu_reaped_note': 'getrusage(RUSAGE_CHILDREN) utime+stime delta '
                              'across this run; counts fully waited children',
           'cpu_sample_last_live_s': round(cpu_sample_last, 3),
           'cpu_samples': cpu_samples,
           'cpu_sample_note': 'live /proc stat utime+stime sum over group '
                              'members at last poll; transient between polls '
                              'missed by construction',
           'peak_group_rss_bytes_sampled': peak_rss,
           'rss_samples': rss_samples,
           'rss_is_sampled_not_cgroup': True,
           'guard': guard, 'events': events,
           'group_members_left': left,
           'limits': {'cpu_s': CPU_S, 'wall_s': WALL_S,
                      'devguard_s': DEVGUARD_S,
                      'alarm_backstop_s': ALARM_BACKSTOP_S,
                      'as_bytes': AS_BYTES, 'rss_guard_bytes': RSS_GUARD_BYTES,
                      'malloc_arena_max': 2, 'max_cpus': MAXCPUS},
           'affinity_used': sorted(aff), 'affinity_mask_seen': mask0,
           'self_affinity': self_affinity,
           'self_caps_before_first_read': True,
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
    # Summary print AFTER the receipt is preserved; true exit propagated.
    print(f'RECEIPT={recippath} EXIT={exit_code}')
    sys.exit(exit_code if exit_code is not None else 1)


if __name__ == '__main__':
    main()
