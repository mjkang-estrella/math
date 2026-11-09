#!/usr/bin/env python3
"""usage: textify.py PDF OUTTXT  -- runs `pdftotext -layout` (poppler) on an untrusted PDF; refuses to overwrite."""
import os, shutil, subprocess, sys
pdf, out = sys.argv[1], sys.argv[2]
if os.path.exists(out): sys.exit('refusing to overwrite ' + out)
exe = shutil.which('pdftotext')
if not exe: sys.exit('pdftotext not available')
subprocess.run([exe, '-layout', os.path.abspath(pdf), os.path.abspath(out)], check=True, timeout=80,
               cwd=os.path.dirname(os.path.abspath(out)))
print('ok', out, os.path.getsize(out))
