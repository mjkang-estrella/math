"""Compare downloaded MathDB PDFs with accepted upload copies; no network access."""
import concurrent.futures
import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

from PIL import Image, ImageChops, ImageDraw

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
WORK = ROOT / 'tmp/pdfs/submissions-2026-10-25'
WORK.mkdir(parents=True, exist_ok=True)
downloads = {r['fileName'].split('-')[0].upper(): r for r in json.loads((HERE / 'downloads-2026-10-25.json').read_text())}
papers = json.loads((HERE / 'resumed-2026-10-25.json').read_text())['papers']

def verify(row):
    ident = row['finding']
    folder = WORK / ident
    folder.mkdir(exist_ok=True)
    original = Path(row['pdf'])
    public = folder / 'mathdb.pdf'
    shutil.copyfile(downloads[ident]['path'], public)
    for name, path in [('original', original), ('public', public)]:
        subprocess.run(['pdftoppm', '-r', '72', '-png', str(path), str(folder / name)], check=True, capture_output=True)
    a = sorted(folder.glob('original-*.png'))
    b = sorted(folder.glob('public-*.png'))
    assert len(a) == len(b) and a, (ident, 'page count mismatch')
    diffs = []
    for i, (pa, pb) in enumerate(zip(a, b), 1):
        with Image.open(pa) as x, Image.open(pb) as y:
            assert x.size == y.size, (ident, i, 'page dimensions')
            box = ImageChops.difference(x.convert('RGB'), y.convert('RGB')).getbbox()
            assert box is None or box[2] <= 30, (ident, i, 'difference outside left stamp margin', box)
            diffs.append({'page': i, 'difference_bbox_72dpi': box})
    def cropped_text(path):
        r = subprocess.run(['pdftotext', '-r', '72', '-x', '30', '-y', '0', '-W', '1000', '-H', '1200', str(path), '-'], capture_output=True, check=True, text=True)
        return re.sub(r'\s+', ' ', r.stdout).strip()
    text_equal = cropped_text(original) == cropped_text(public)
    assert text_equal, (ident, 'normalized body text mismatch')
    result = {'finding': ident, 'pages': len(a), 'public_pdf_sha256': hashlib.sha256(public.read_bytes()).hexdigest(), 'original_pdf_sha256': hashlib.sha256(original.read_bytes()).hexdigest(), 'body_text_equal_excluding_30pt_left_margin': text_equal, 'all_page_rasters_equal_outside_30px_left_margin_at_72dpi': True, 'page_differences': diffs}
    print(ident, len(a), 'pages: body text and rasters PASS', flush=True)
    return result

with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
    results = list(pool.map(verify, papers))
(HERE / 'mathdb-verification-2026-10-25.json').write_text(json.dumps({'scope': 'All pages at 72dpi; PDF text excludes 30pt left margin containing MathDB stamp. No new proof review.', 'papers': results}, indent=2) + '\n')
thumbs = []
for row in papers:
    with Image.open(sorted((WORK / row['finding']).glob('public-*.png'))[0]) as im:
        im = im.convert('RGB'); im.thumbnail((400, 550))
        cell = Image.new('RGB', (420, 590), 'white')
        cell.paste(im, ((420-im.width)//2, 30))
        ImageDraw.Draw(cell).text((12, 8), row['finding'], fill='black')
        thumbs.append(cell)
sheet = Image.new('RGB', (420*4, 590*3), '#dddddd')
for i, cell in enumerate(thumbs):
    sheet.paste(cell, ((i%4)*420, (i//4)*590))
sheet.save(WORK / 'public-first-pages.png')
print('PASS:', sum(r['pages'] for r in results), 'pages across', len(results), 'papers')
