#!/usr/bin/env python3
"""Extract text of given 0-based pages of a PDF with pypdf if installed; write to a new file.
Usage: pdfpage.py PDF OUTTXT PAGE [PAGE ...]"""
import os, sys
try:
    import pypdf
except Exception as e:
    sys.exit('pypdf unavailable: %r' % e)
pdf, outp = sys.argv[1], sys.argv[2]
if os.path.exists(outp):
    sys.exit('refusing to overwrite')
r = pypdf.PdfReader(pdf)
with open(outp, 'x') as f:
    for p in sys.argv[3:]:
        f.write(f'=== page index {p} ===\n' + (r.pages[int(p)].extract_text() or '') + '\n')
print('pages', len(r.pages), 'written', outp)
