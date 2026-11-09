"""Exclusive launch marker, input/source integrity gate, single 60s execution."""
import time
START = time.monotonic()
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import traceback

ROOT = Path(__file__).resolve().parent


def main():
    with (ROOT / 'RUN-ONCE.json').open('x') as marker:
        json.dump(dict(start_monotonic=START, start_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
                       pid=os.getpid(), python=sys.version, executable=sys.executable), marker, indent=2)
        marker.write('\n')
    result = dict(status='launching', seconds_cap=60)
    try:
        manifest_bytes = (ROOT / 'freeze-manifest.json').read_bytes()
        result['freeze_manifest_sha256'] = hashlib.sha256(manifest_bytes).hexdigest()
        manifest = json.loads(manifest_bytes)
        checks = []
        for item in manifest['files']:
            path = ROOT / item['path']
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            checks.append(dict(path=item['path'], sha256=digest, matches=digest == item['sha256']))
            if digest != item['sha256']:
                raise RuntimeError('frozen payload mismatch: ' + item['path'])
        result['freeze_checks'] = checks
        env = os.environ.copy()
        env['W032_ASSAY_MONOTONIC_START'] = str(START)
        env['PYTHONDONTWRITEBYTECODE'] = '1'
        with (ROOT / 'stdout.txt').open('x') as stdout, (ROOT / 'stderr.txt').open('x') as stderr:
            process = subprocess.Popen([sys.executable, '-B', str(ROOT / 'assay.py')], cwd=ROOT,
                                       env=env, stdout=stdout, stderr=stderr)
            result['child_pid'] = process.pid
            try:
                result['returncode'] = process.wait(timeout=max(0.001, 60 - (time.monotonic() - START)))
                result['status'] = 'child_finished'
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
                result.update(status='hard_timeout', returncode=process.returncode)
    except Exception as exc:
        result.update(status='runner_failed', error=repr(exc), traceback=traceback.format_exc())
    result['elapsed_through_child_recording_s'] = time.monotonic() - START
    with (ROOT / 'runner-status.json').open('x') as out:
        json.dump(result, out, indent=2, sort_keys=True)
        out.write('\n')
    print(json.dumps(dict(status=result['status'], returncode=result.get('returncode'),
                         elapsed_through_runner_recording_s=time.monotonic() - START,
                         freeze_manifest_sha256=result.get('freeze_manifest_sha256')), sort_keys=True))


if __name__ == '__main__':
    main()
