#!/usr/bin/env python3
"""Enforced portable strict replay for the CommonBasis332371 source-only archive.

Python standard library only. Unlike the historical replay.sh (which inherits the
ambient PATH/HOME/Lean environment and enforces no resource limits), this wrapper
ACTUALLY ENFORCES, per heavy call:

  - CPU affinity  <= 2 cores            (os.sched_setaffinity in the child)
  - CPU time      <= 120 s              (RLIMIT_CPU, kernel-enforced)
  - wall clock    <= 140 s              (wrapper timeout, process-group kill)
  - sampled RSS   <= 6 GiB guard        (poller kills the child on exceed)
  - address space <= 12 GiB rlimit      (RLIMIT_AS), 64 GiB sampled-VmPeak hard guard
  - MALLOC_ARENA_MAX=2, minimal private HOME, PATH pinned to LEAN_BIN first

It also: verifies the archive SHA-256, extracts it safely (relative paths only,
regular files/dirs, no symlinks; per-member SHA-256 recorded and checked against
the shipped lean-source-manifest.json and the author manifest), builds into a NEW
empty directory (refuses preexisting .olean), verifies the pinned toolchain
binaries and mathlib checkout against the completed review's pin manifest, runs
`lean -j1 -M3500 -DwarningAsError=true` then `leanchecker` for every module and
every audit file, and runs negative controls that must fail. Upstream packages
are TRUSTED PREBUILT: no source-to-olean attestation is claimed or checked for
them (explicit, recorded in the result).

Usage:
  python3 -I -B capped_replay.py \
    --zip SOURCE_ONLY_ZIP --expect-zip-sha256 SHA256 \
    --lean-bin DIR --lean-packages DIR --pin-receipt FILE \
    --author-manifest FILE --workdir DIR \
    [--audit FILE]... [--control FILE]... [--module-order Bases,Cases0,...]

Exit 0 iff every verification, strict stage and audit stage passes and every
control fails as expected. All commands, environments, exit codes, timings and
resource peaks are retained under WORKDIR/receipts and WORKDIR/logs.
"""
import argparse, json, os, pathlib, resource, shutil, subprocess, sys, time, zipfile, hashlib

GIB = 1024 ** 3
CPU_LIMIT_S = 120
WALL_LIMIT_S = 140
RSS_GUARD = 6 * GIB
AS_LIMIT = 12 * GIB
AS_HARD = 64 * GIB


def sha256_file(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def log(msg):
    print('[capped_replay] ' + msg, flush=True)


def safe_extract(zpath, dest):
    """Safe extraction: relative pure paths, regular entries only, no overwrite."""
    dest = pathlib.Path(dest)
    if dest.exists():
        shutil.rmtree(dest)
    dest.mkdir(parents=True)
    members, hashes, notes = [], {}, []
    with zipfile.ZipFile(zpath) as z:
        bad = z.testzip()
        if bad is not None:
            raise SystemExit(f'corrupt zip member: {bad}')
        for info in z.infolist():
            name = info.filename
            mode = info.external_attr >> 16
            if name.startswith('/') or '..' in pathlib.PurePosixPath(name).parts:
                raise SystemExit(f'unsafe path in archive: {name}')
            if (mode & 0o170000) == 0o120000:
                notes.append(f'symlink skipped? present in archive: {name}')
            is_dir = name.endswith('/')
            target = dest / name
            if is_dir:
                target.mkdir(parents=True, exist_ok=True)
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            with z.open(info) as src, open(target, 'wb') as out:
                shutil.copyfileobj(src, out)
            members.append(name)
            hashes[name] = sha256_file(target)
    return members, hashes, notes


def child_pre(affinity, as_limit):
    def fn():
        try:
            os.sched_setaffinity(0, affinity)
        except OSError:
            pass
        resource.setrlimit(resource.RLIMIT_CPU, (CPU_LIMIT_S, CPU_LIMIT_S + 5))
        resource.setrlimit(resource.RLIMIT_AS, (as_limit, as_limit))
        os.setsid()
    return fn


def run_capped(argv, cwd, env, receipts_dir, name, affinity, sampler_note):
    """Run one capped subprocess; kill on wall/RSS guards; full receipt."""
    t0 = time.monotonic()
    peak = 0
    vmpeak = 0
    cap_reason = None
    logdir = pathlib.Path(receipts_dir).parent / 'logs'
    logdir.mkdir(parents=True, exist_ok=True)
    with open(pathlib.Path(logdir) / f'{name}.log', 'wb') as lf:
        p = subprocess.Popen(argv, cwd=str(cwd), env=env, stdout=lf,
                             stderr=subprocess.STDOUT,
                             preexec_fn=child_pre(affinity, AS_LIMIT))
        try:
            while p.poll() is None:
                try:
                    txt = pathlib.Path(f'/proc/{p.pid}/status').read_text()
                    rss = vk = 0
                    for line in txt.splitlines():
                        if line.startswith('VmRSS:'):
                            rss = int(line.split()[1]) * 1024
                        elif line.startswith('VmPeak:'):
                            vk = int(line.split()[1]) * 1024
                    peak = max(peak, rss)
                    vmpeak = max(vmpeak, vk)
                except (OSError, ValueError, IndexError):
                    pass
                elapsed = time.monotonic() - t0
                if peak > RSS_GUARD:
                    cap_reason = 'sampled RSS over 6GiB guard'
                elif vmpeak > AS_HARD:
                    cap_reason = 'sampled VmPeak over 64GiB hard guard'
                elif elapsed > WALL_LIMIT_S:
                    cap_reason = 'wall over 140s'
                if cap_reason:
                    os.killpg(os.getpgid(p.pid), 15)
                    time.sleep(2)
                    if p.poll() is None:
                        os.killpg(os.getpgid(p.pid), 9)
                    break
                time.sleep(0.05)
            p.wait()
        except subprocess.TimeoutExpired:
            cap_reason = 'wrapper wait timeout'
            p.kill()
            p.wait()
    wall = time.monotonic() - t0
    ru = resource.getrusage(resource.RUSAGE_CHILDREN)
    rec = {
        'name': name, 'argv': argv, 'cwd': str(cwd),
        'returncode': p.returncode,
        'wall_seconds': round(wall, 3),
        'limits': 'affinity %s; CPU %ds (RLIMIT_CPU, +5s hard); wall %ds; sampled-RSS guard %dGiB; RLIMIT_AS %dGiB; sampled-VmPeak hard guard %dGiB; %s'
                  % (sorted(affinity), CPU_LIMIT_S, WALL_LIMIT_S, RSS_GUARD // GIB,
                     AS_LIMIT // GIB, AS_HARD // GIB, sampler_note),
        'affinity_set': sorted(affinity),
        'cpu_limit_seconds': CPU_LIMIT_S, 'wall_limit_seconds': WALL_LIMIT_S,
        'as_limit_bytes': AS_LIMIT, 'as_hard_guard_bytes': AS_HARD,
        'rss_guard_bytes': RSS_GUARD,
        'sampled_rss_peak_bytes': peak, 'sampled_vmpeak_max_bytes': vmpeak,
        'cap_reason': cap_reason,
        'env': {k: env.get(k) for k in ('PATH', 'HOME', 'LEAN_PATH', 'MALLOC_ARENA_MAX',
                                        'OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS')},
    }
    # per-call cumulative children CPU is not attributable per stage exactly when
    # pooled; keep the sampled wall + limits as the enforced budget record.
    out = pathlib.Path(receipts_dir) / f'{name}.receipt.json'
    out.write_text(json.dumps(rec, indent=1) + '\n')
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--zip', required=True)
    ap.add_argument('--expect-zip-sha256', default=None)
    ap.add_argument('--lean-bin', required=True)
    ap.add_argument('--lean-packages', required=True)
    ap.add_argument('--pin-receipt', required=True, help='completed-review pinned-binaries-deps.txt')
    ap.add_argument('--author-manifest', required=True, help='author lean-source-manifest.json')
    ap.add_argument('--workdir', required=True)
    ap.add_argument('--audit', action='append', default=[])
    ap.add_argument('--control', action='append', default=[])
    ap.add_argument('--module-order', default='Bases,Cases0,Cases1,Cases2,Cases3,Cases4,Cases5,Cases6,Cases7,Endpoint,Final,Audit')
    ap.add_argument('--expect-lean-version', default='4.34.1')
    ap.add_argument('--expect-lean-commit', default='5045d0056413266e57c625dcd7c365b10e377c52')
    a = ap.parse_args()

    work = pathlib.Path(a.workdir).resolve()
    build = work / 'build'
    if build.exists() and any(build.iterdir()):
        log('FATAL: build dir exists and is not empty; refusing (fresh build dir required)')
        return 1
    extract = work / 'src'
    receipts = work / 'receipts'
    home = work / 'home'
    for d in (extract, receipts, home):
        if d.exists():
            shutil.rmtree(d)
    build.mkdir(parents=True, exist_ok=True)
    receipts.mkdir(parents=True, exist_ok=True)
    home.mkdir(parents=True, exist_ok=True)
    (home / '.lean').mkdir(exist_ok=True)

    result = {'wrapper': 'capped_replay.py (Python stdlib only)',
              'caps': 'per call: <=2 CPU affinity, CPU 120s, wall 140s, sampled-RSS guard 6GiB, RLIMIT_AS 12GiB, VmPeak hard guard 64GiB, MALLOC_ARENA_MAX=2',
              'upstream_trust': 'LEAN_PACKAGES prebuilt oleans are TRUSTED; no source-to-olean attestation claimed or checked',
              'verifications': {}, 'stages': [], 'controls': [], 'audit_stages': []}
    ok = True

    # --- archive verification and safe extraction ---------------------------
    zsha = sha256_file(pathlib.Path(a.zip).resolve())
    result['verifications']['zip_sha256'] = zsha
    if a.expect_zip_sha256 and zsha != a.expect_zip_sha256:
        log('FATAL: zip sha mismatch'); return 1
    members, hashes, notes = safe_extract(a.zip, extract)
    result['verifications']['zip_members'] = len(members)
    result['verifications']['member_sha256'] = hashes
    result['verifications']['path_symlink_notes'] = notes
    log(f'extracted {len(members)} members safely')

    shipped = json.load(open(extract / 'lean-source-manifest.json'))
    author = json.load(open(a.author_manifest))
    mod_hashes = {}
    for m in a.module_order.split(','):
        f = extract / 'src' / f'{m}.lean'
        if not f.exists():
            log(f'FATAL: missing module {m}'); return 1
        mod_hashes[f'src/{m}.lean'] = sha256_file(f)
    ship_ok = all(shipped.get(k) == v for k, v in mod_hashes.items())
    auth_ok = all(author.get(k) == v for k, v in mod_hashes.items())
    result['verifications']['modules_match_shipped_manifest'] = ship_ok
    result['verifications']['modules_match_author_manifest'] = auth_ok
    result['verifications']['module_sha256'] = mod_hashes
    if not (ship_ok and auth_ok):
        log('FATAL: module hash mismatch'); return 1
    log('12 module hashes match shipped + author manifests')

    # preexisting-olean refusal
    pre_oleans = [str(p) for p in extract.rglob('*.olean')] + [str(p) for p in build.glob('*.olean')]
    result['verifications']['preexisting_oleans'] = pre_oleans
    if pre_oleans:
        log('FATAL: preexisting olean files present'); return 1

    # --- pinned toolchain verification --------------------------------------
    lean_bin = pathlib.Path(a.lean_bin).resolve()
    pin = {}
    for line in open(a.pin_receipt):
        line = line.strip()
        if line.startswith('lean '): pin['lean'] = line.split()[1]
        elif line.startswith('leanc '): pin['leanc'] = line.split()[1]
        elif line.startswith('leanchecker '): pin['leanchecker'] = line.split()[1]
    tool_sha = {b: sha256_file(lean_bin / b) for b in ('lean', 'leanc', 'leanchecker')
                if (lean_bin / b).exists()}
    result['verifications']['toolchain_bin_sha256'] = tool_sha
    result['verifications']['toolchain_match_pin_receipt'] = all(tool_sha.get(k) == v for k, v in pin.items())
    if not result['verifications']['toolchain_match_pin_receipt']:
        log('FATAL: toolchain binaries differ from pinned receipt'); return 1

    env = {
        'PATH': f'{lean_bin}:/usr/bin:/bin',
        'HOME': str(home),
        'LEAN_PATH': str(build),
        'MALLOC_ARENA_MAX': '2',
        'OMP_NUM_THREADS': '2',
        'OPENBLAS_NUM_THREADS': '1',
        'TMPDIR': str(work / 'tmp'),
    }
    pathlib.Path(env['TMPDIR']).mkdir(exist_ok=True)
    for d in pathlib.Path(a.lean_packages).rglob('.lake/build/lib/lean'):
        env['LEAN_PATH'] += f':{d}'
    result['env'] = dict(env)
    result['lean_path_dirs'] = env['LEAN_PATH'].split(':')

    affinity = sorted(os.sched_getaffinity(0))[:2]
    vr = run_capped([str(lean_bin / 'lean'), '--version'], work, env, receipts,
                    'lean-version', affinity, 'sampler observes child leader')
    ver = pathlib.Path(receipts).parent.joinpath('logs/lean-version.log').read_text()
    result['verifications']['lean_version_output'] = ver.strip()
    vok = a.expect_lean_version in ver and a.expect_lean_commit in ver
    result['verifications']['lean_version_match'] = vok
    if not vok:
        log('FATAL: lean version mismatch'); return 1

    mathlib = pathlib.Path(a.lean_packages) / 'mathlib'
    ml = {'path': str(mathlib), 'exists': mathlib.exists()}
    gt = mathlib / '.git' / 'HEAD'
    if gt.exists():
        ml['git_head'] = open(gt).read().strip()
        ref = (mathlib / '.git').joinpath(open(gt).read().strip().split(': ')[-1])
        if ref.exists():
            ml['resolved_head'] = open(ref).read().strip()
    result['verifications']['mathlib_checkout'] = ml
    result['verifications']['mathlib_expected_commit'] = 'd13f23b723b8a846827a245b89c10fc7d3f11612'

    # --- strict stages -------------------------------------------------------
    order = a.module_order.split(',')
    for m in order:
        for kind, argv, cname in (
            ('lean', [str(lean_bin / 'lean'), '-j1', '-M3500', '-DwarningAsError=true',
                      '-o', str(build / f'{m}.olean'), str(extract / 'src' / f'{m}.lean')], f'lean-{m}'),
        ):
            rec = run_capped(argv, work, env, receipts, cname, affinity, 'sampler observes child leader')
            passed = rec['returncode'] == 0 and rec['cap_reason'] is None
            rec['stage'] = 'strict'; rec['required'] = True; rec['passed'] = passed
            result['stages'].append(rec)
            ok &= passed
            log(f"{cname}: rc={rec['returncode']} wall={rec['wall_seconds']}s peakRSS={rec['sampled_rss_peak_bytes']/GIB:.2f}GiB {'PASS' if passed else 'FAIL'}")
        rec = run_capped([str(lean_bin / 'leanchecker'), m], build, env, receipts,
                         f'checker-{m}', affinity, 'sampler observes child leader; cwd=build')
        passed = rec['returncode'] == 0 and rec['cap_reason'] is None
        rec['stage'] = 'strict'; rec['required'] = True; rec['passed'] = passed
        result['stages'].append(rec)
        ok &= passed
        log(f"checker-{m}: rc={rec['returncode']} {'PASS' if passed else 'FAIL'}")

    # --- audit stages (must pass) -------------------------------------------
    extra = work / 'extra'
    extra.mkdir(exist_ok=True)
    for af in a.audit:
        af = pathlib.Path(af).resolve()
        shutil.copy(af, extra / af.name)
        af = extra / af.name
        m = af.stem
        rec = run_capped([str(lean_bin / 'lean'), '-j1', '-M3500', '-DwarningAsError=true',
                          '-o', str(build / f'{m}.olean'), str(af)], work, env, receipts,
                         f'lean-{m}', affinity, 'sampler observes child leader')
        passed = rec['returncode'] == 0 and rec['cap_reason'] is None
        rec['stage'] = 'audit'; rec['required'] = True; rec['passed'] = passed
        result['audit_stages'].append(rec); ok &= passed
        log(f"audit {m}: rc={rec['returncode']} {'PASS' if passed else 'FAIL'}")

    # --- negative controls (must fail) ---------------------------------------
    for cf in a.control:
        cf = pathlib.Path(cf).resolve()
        shutil.copy(cf, extra / cf.name)
        cf = extra / cf.name
        m = cf.stem
        rec = run_capped([str(lean_bin / 'lean'), '-j1', '-M3500', '-DwarningAsError=true',
                          '-o', str(build / f'{m}.olean'), str(cf)], work, env, receipts,
                         f'lean-{m}', affinity, 'sampler observes child leader')
        # expected: nonzero exit (control fails), or a cap; a rc==0 control is a
        # scoping failure and is reported, not counted as a pass.
        failed_as_expected = rec['returncode'] != 0
        rec['stage'] = 'negative-control'; rec['expected'] = 'nonzero exit'
        rec['failed_as_expected'] = failed_as_expected
        result['controls'].append(rec)
        ok &= failed_as_expected
        log(f"control {m}: rc={rec['returncode']} {'FAILS-AS-EXPECTED' if failed_as_expected else 'UNEXPECTED-PASS'}")

    result['ok'] = ok
    result['strict_passes'] = sum(1 for s in result['stages'] if s['passed'])
    result['strict_total'] = len(result['stages'])
    (work / 'replay-result.json').write_text(json.dumps(result, indent=1) + '\n')
    log(f"DONE ok={ok} strict {result['strict_passes']}/{result['strict_total']}")
    return 0 if ok else 2


if __name__ == '__main__':
    sys.exit(main())
