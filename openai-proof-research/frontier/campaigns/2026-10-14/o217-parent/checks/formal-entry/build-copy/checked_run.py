#!/usr/bin/env python3
"""Copyright 2026 Myeongjin Kang. MIT. Enforce exit status AND failure output."""
import argparse
from pathlib import Path
import re
import subprocess
import sys

# In particular, the historical large checker prints SOME FAIL but exits zero.
FAILURE = re.compile(r'\b(?:SOME\s+FAIL|FAIL(?:ED)?|Traceback)\b|\berror:', re.I)


def failed(returncode, stdout, stderr):
    return returncode != 0 or bool(FAILURE.search(stdout + '\n' + stderr))


def run_checked(command, cwd, env, prefix, timeout=600):
    prefix = Path(prefix)
    prefix.parent.mkdir(parents=True, exist_ok=True)
    run = subprocess.run(command, cwd=cwd, env=env, capture_output=True,
                         text=True, timeout=timeout)
    prefix.with_suffix('.stdout').write_text(run.stdout)
    prefix.with_suffix('.stderr').write_text(run.stderr)
    if failed(run.returncode, run.stdout, run.stderr):
        raise RuntimeError(f'check rejected: exit={run.returncode}; logs={prefix}')
    return run


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log-prefix', required=True, type=Path)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if not command:
        parser.error('a command is required after --')
    import os
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    try:
        run = run_checked(command, Path.cwd(), env, args.log_prefix)
    except RuntimeError as exc:
        print(str(exc), file=sys.stderr)
        return 1
    print(run.stdout, end='')
    return 0


if __name__ == '__main__':
    sys.exit(main())
