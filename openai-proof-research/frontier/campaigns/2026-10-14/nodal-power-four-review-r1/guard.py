#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Author: Myeongjin Kang; no affiliation.
"""Read-only verifier runner; authenticate verifier code before compilation."""
import hashlib
import json
import os
from pathlib import Path
import sys

sys.dont_write_bytecode = True
code_path = Path(sys.argv[1])
code_bytes = code_path.read_bytes()
if hashlib.sha256(code_bytes).hexdigest() != sys.argv[2]:
    raise SystemExit('verifier code hash mismatch')
code = compile(code_bytes, str(code_path), 'exec')
arguments = sys.argv[3:]
parse_count = 0
denied_count = 0
original_loads = json.loads


def counted_loads(*args, **kwargs):
    global parse_count
    parse_count += 1
    return original_loads(*args, **kwargs)


def audit(event, args):
    global denied_count
    blocked = False
    if event == 'open':
        mode, flags = args[1:3]
        blocked = ((isinstance(mode, str) and any(c in mode for c in 'wax+')) or
                   (isinstance(flags, int) and flags &
                    (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND)))
    if event.startswith(('subprocess.', 'socket.', 'shutil.')) or event in {
            'os.system', 'os.remove', 'os.rename', 'os.rmdir', 'os.mkdir',
            'os.chmod', 'os.chown', 'os.link', 'os.symlink', 'os.truncate',
            'os.utime', 'os.exec', 'os.posix_spawn', 'os.fork'}:
        blocked = True
    if blocked:
        denied_count += 1
        raise PermissionError('read-only verifier guard: ' + event)


json.loads = counted_loads
sys.argv = [str(code_path)] + arguments
sys.addaudithook(audit)
try:
    exec(code, {'__name__': '__main__', '__file__': str(code_path)})
finally:
    print(json.dumps({'guard_json_parse_calls': parse_count,
                      'guard_denied_mutation_process_network_events': denied_count},
                     sort_keys=True), file=sys.stderr)
