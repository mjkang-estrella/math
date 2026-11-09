"""Render one PDF page at high resolution and crop a region (QA close-up).

Usage: python3 -I scripts/zoom.py PDF PAGE DPI X0 Y0 X1 Y1 OUT.png   (box as fractions of the page)
"""
import sys
sys.dont_write_bytecode = True
import subprocess, os
from PIL import Image

pdf, page, dpi = sys.argv[1], int(sys.argv[2]), sys.argv[3]
x0, y0, x1, y1 = map(float, sys.argv[4:8])
out = sys.argv[8]
stem = out[:-4] + "-full"
subprocess.run(["pdftoppm", "-r", dpi, "-f", str(page), "-l", str(page), "-singlefile", "-png", pdf, stem],
               check=True, timeout=90)
im = Image.open(stem + ".png")
W, H = im.size
im.crop((int(x0 * W), int(y0 * H), int(x1 * W), int(y1 * H))).save(out)
os.remove(stem + ".png")
print(out, im.size)
