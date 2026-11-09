"""Render every page of the draft and record mechanical checks (lane tooling).

    python3 -I pdf_qa.py PDF QA_DIR RECEIPT.json

Renders each page with pdftoppm (110 dpi PNG), extracts text with pdftotext, lists fonts with pdffonts
and checks: 5-8 pages, no unreplaced '{{' placeholders, every font embedded, key statements present.
Visual inspection notes are added separately (receipts/pdf-qa.json).
"""
import hashlib, json, re, subprocess, sys
from pathlib import Path

pdf, qa, receipt = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
qa.mkdir(parents=True, exist_ok=True)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
info = subprocess.run(['pdfinfo', str(pdf)], capture_output=True, text=True, check=True).stdout
pages = int(re.search(r'Pages:\s+(\d+)', info).group(1))
for old in qa.glob('page-*.png'):
    old.unlink()
subprocess.run(['pdftoppm', '-r', '110', '-png', str(pdf), str(qa / 'page')], check=True)
pngs = sorted(qa.glob('page-*.png'), key=lambda p: int(re.search(r'(\d+)\.png$', p.name).group(1)))
text = subprocess.run(['pdftotext', '-layout', str(pdf), '-'], capture_output=True, text=True, check=True).stdout
(qa / 'paper-text.txt').write_text(text)
fonts = subprocess.run(['pdffonts', str(pdf)], capture_output=True, text=True, check=True).stdout
rows = [l.split() for l in fonts.splitlines()[2:] if l.strip()]
emb = all(r[-5] == 'yes' for r in rows)  # columns: ... emb sub uni object ID
flat = ' '.join(text.split())
needles = ['DRAFT', 'AI-assisted', 'no priority claim', 'Conjecture 1', 'Theorem 1', 'adjacent to no tour',
           'rank 56', '5040', '1/512', 'ASEP.arc_counterexample', 'ASEP.arc_neighborhood_tour_conjecture_false',
           'ASEP.counterexample', 'ASEP.neighborhood_tour_conjecture_false', 'ASEP.segment_not_face',
           'ASEP.segment_not_exposed', 'propext', 'Classical.choice', 'Quot.sound', 'Deza', 'math/0512493',
           'n = 7', '11 and 20']
missing = [n for n in needles if n not in flat]
rec = {'pdf': str(pdf), 'pdf_sha256': sha(pdf), 'pages': pages,
       'renders': [{'file': p.name, 'sha256': sha(p)} for p in pngs], 'dpi': 110,
       'all_pages_rendered': len(pngs) == pages, 'page_count_in_5_to_8': 5 <= pages <= 8,
       'placeholders_left': '{{' in text, 'fonts_embedded': emb, 'fonts': fonts.splitlines(),
       'key_statements_missing': missing, 'text_sha256': sha(qa / 'paper-text.txt')}
rec['mechanical_ok'] = (rec['all_pages_rendered'] and rec['page_count_in_5_to_8'] and not rec['placeholders_left']
                        and emb and not missing)
receipt.write_text(json.dumps(rec, indent=1))
print(json.dumps({k: rec[k] for k in ('pages', 'mechanical_ok', 'key_statements_missing', 'fonts_embedded')}))
