# SPDX-License-Identifier: MIT
# OCR navigation aid; equations must be checked against page images.
import ctypes as c
import pathlib
from concurrent.futures import ThreadPoolExecutor
r=pathlib.Path(__file__).resolve().parent
l=c.CDLL('libtesseract.so.5.5');p=c.CDLL('libleptonica.so.6')
l.TessBaseAPICreate.restype=c.c_void_p
l.TessBaseAPIInit3.argtypes=[c.c_void_p,c.c_char_p,c.c_char_p]
l.TessBaseAPISetImage2.argtypes=[c.c_void_p,c.c_void_p]
l.TessBaseAPIGetUTF8Text.argtypes=[c.c_void_p];l.TessBaseAPIGetUTF8Text.restype=c.c_void_p
l.TessDeleteText.argtypes=[c.c_void_p];l.TessBaseAPIDelete.argtypes=[c.c_void_p]
p.pixRead.argtypes=[c.c_char_p];p.pixRead.restype=c.c_void_p
p.pixDestroy.argtypes=[c.POINTER(c.c_void_p)]
def one(f):
 h=l.TessBaseAPICreate();assert l.TessBaseAPIInit3(h,b'/usr/share/tesseract/tessdata',b'eng')==0
 pix=c.c_void_p(p.pixRead(str(f).encode()));l.TessBaseAPISetImage2(h,pix);s=l.TessBaseAPIGetUTF8Text(h)
 text=c.string_at(s).decode();l.TessDeleteText(s);l.TessBaseAPIDelete(h);p.pixDestroy(c.byref(pix))
 f.with_suffix('.txt').write_text(text);return f.name
with ThreadPoolExecutor(max_workers=4) as ex:
 for name in ex.map(one,sorted((r/'private/render').glob('semmes-*.png'))):print(name,flush=True)
