#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""Authenticate reviewed verify.py, then execute under a read-only audit guard.

This guard never writes a receipt. The caller may capture its stdout outside
the guarded interpreter. Authentication and compilation precede guarded exec;
no imported author/experiment module is loaded.
"""
import hashlib
import os
from pathlib import Path
import sys

sys.dont_write_bytecode = True
requirement = sys.argv[1]
path = Path(__file__).resolve().with_name('verify.py')
source = path.read_bytes()
if hashlib.sha256(source).hexdigest() != requirement:
    raise SystemExit('reviewed verifier code hash mismatch')
code = compile(source, str(path), 'exec')
sys.argv = [str(path)] + sys.argv[2:]
mutations = {'os.remove', 'os.rename', 'os.rmdir', 'os.mkdir', 'os.chmod',
             'os.chown', 'os.truncate', 'os.utime', 'os.link', 'os.symlink',
             'os.system', 'os.fork', 'os.exec', 'os.posix_spawn', 'os.putenv',
             'os.unsetenv', 'os.chdir'}


def audit(event, args):
    if event == 'open':
        mode = args[1]
        flags = args[2]
        if (isinstance(mode, str) and any(c in mode for c in 'wax+')) or (
                isinstance(flags, int) and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT
                                                  | os.O_TRUNC | os.O_APPEND)):
            raise PermissionError('read-only guard: ' + event)
    if event in mutations or event.startswith(('subprocess.', 'socket.', 'shutil.')):
        raise PermissionError('read-only guard: ' + event)


sys.addaudithook(audit)
exec(code, {'__name__': '__main__', '__file__': str(path)})
