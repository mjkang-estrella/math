"""Convert (untrusted) PDF bodies to text with a pure-python library; refuses to overwrite.
usage: pdf2txt.py NAME1 NAME2 ... (reads sources/NAME.body, writes texts/NAME.txt)"""
import os, sys
D = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r248'
os.makedirs(D + '/texts', exist_ok=True)
for name in sys.argv[1:]:
    src, dst = f'{D}/sources/{name}.body', f'{D}/texts/{name}.txt'
    if os.path.exists(dst):
        print('exists', dst)
        continue
    try:
        import fitz
        doc = fitz.open(src)
        text = '\n'.join(p.get_text() for p in doc)
        lib = 'fitz'
    except ImportError:
        import pypdf
        r = pypdf.PdfReader(src)
        text = '\n'.join((p.extract_text() or '') for p in r.pages)
        lib = 'pypdf'
    with open(dst, 'x', encoding='utf-8') as f:
        f.write(text)
    print(name, lib, len(text))
