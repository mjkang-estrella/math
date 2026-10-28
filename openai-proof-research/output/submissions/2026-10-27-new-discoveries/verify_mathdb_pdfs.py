"""Check browser-downloaded public PDFs against immutable local papers."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile
from PIL import Image, ImageChops

root = Path(__file__).resolve().parent
manifest = json.loads((root / 'submission-manifest.json').read_text())
results = []
for item in manifest['papers']:
    number = item['number']
    public = root / 'verification' / f'mathdb-public-D{number:03}.pdf'
    if not public.exists():
        continue
    original = root / item['directory'] / item['pdf']
    public_hash = hashlib.sha256(public.read_bytes()).hexdigest()
    assert public_hash == item['mathdb_public_pdf_sha256'], number
    assert hashlib.sha256(original.read_bytes()).hexdigest() == item['pdf_sha256'], number
    def text(path):
        return subprocess.check_output(['pdftotext', '-layout', str(path), '-']).decode()
    source_text, public_text = text(original), text(public)
    stamp_pattern = r'mathdb:' + re.escape(item['mathdb_pdf_url'].split('/')[-1]) + r' \d+ [A-Za-z]+ \d{4}'
    stamps = re.findall(stamp_pattern, public_text)
    stripped = re.sub(stamp_pattern, '', public_text)
    assert ''.join(source_text.split()) == ''.join(stripped.split()), (number, 'text changed')
    def count(path):
        info = subprocess.check_output(['pdfinfo', str(path)]).decode()
        return int(re.search(r'^Pages:\s+(\d+)', info, re.MULTILINE)[1])
    pages = count(original)
    assert pages == count(public), (number, 'page count')
    assert len(stamps) == pages, (number, 'stamp count')
    differences = []
    with tempfile.TemporaryDirectory() as tmp:
        for page in range(1, pages + 1):
            images = []
            for label, path in [('original', original), ('public', public)]:
                prefix = Path(tmp) / label
                subprocess.run(['pdftoppm', '-f', str(page), '-l', str(page),
                                '-singlefile', '-scale-to', '1000', '-png',
                                str(path), str(prefix)], check=True,
                               stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
                images.append(Image.open(str(prefix) + '.png').convert('RGB'))
            assert images[0].size == images[1].size, (number, page, 'dimensions')
            delta = ImageChops.difference(*images)
            bounds = delta.getbbox()
            # The inspected MathDB stamp occupies the otherwise blank left margin.
            assert bounds and bounds[2] <= images[0].width * .05, (number, page, bounds)
            assert images[0].crop((0, 0, int(images[0].width * .05), images[0].height)).getextrema() == ((255, 255),) * 3, (number, page, 'stamp overlaps source ink')
            differences.append({'page': page, 'difference_bounds': bounds})
    results.append({'number': number, 'mathdb_url': item['mathdb_url'],
                    'public_pdf_sha256': public_hash, 'pages': pages,
                    'text_unchanged_after_removing_margin_stamp': True,
                    'all_page_pixels_identical_outside_blank_left_margin': True,
                    'stamps': stamps, 'render_differences': differences, 'pass': True})
receipt = {'verified_count': len(results), 'verified_pages': sum(r['pages'] for r in results),
           'all_pass': all(r['pass'] for r in results), 'papers': results}
(root / 'verification' / 'mathdb-pdf-comparison.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({k: v for k, v in receipt.items() if k != 'papers'}))
