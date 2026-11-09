"""Convert an (untrusted) PDF body to text with a pure-python library; refuses to overwrite.
usage: pdf2txt.py IN.body OUT.txt"""
import os
import sys

src, dst = sys.argv[1], sys.argv[2]
if os.path.exists(dst):
    raise SystemExit('refusing to overwrite ' + dst)
text = None
try:
    import fitz  # PyMuPDF
    doc = fitz.open(src)
    text = '\n'.join(p.get_text() for p in doc)
    lib = 'fitz'
except ImportError:
    try:
        import pypdf
        r = pypdf.PdfReader(src)
        text = '\n'.join((p.extract_text() or '') for p in r.pages)
        lib = 'pypdf'
    except ImportError:
        raise SystemExit('no pdf library')
with open(dst, 'x', encoding='utf-8') as f:
    f.write(text)
print(lib, len(text))
