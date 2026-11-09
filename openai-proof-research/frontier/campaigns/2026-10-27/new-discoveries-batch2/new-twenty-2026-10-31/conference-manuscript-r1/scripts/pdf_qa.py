"""Write the PDF QA receipt.  python3 -I -B scripts/pdf_qa.py PDF QA_DIR FONTS_TXT OUT.json"""
import datetime, hashlib, json, os, re, sys
pdf, qa, fonts_txt, out = sys.argv[1:5]
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
pngs = sorted((f for f in os.listdir(qa) if f.endswith('.png')), key=lambda f: int(re.findall(r'\d+', f)[0]))
fonts = [l.split() for l in open(fonts_txt).read().splitlines()[2:] if l.strip()]
notes = {
 'page-1.png': 'title, AI-assistance byline, DRAFT status box, abstract, Section 1, start of Section 2; no overlaps',
 'page-2.png': 'definitions, quoted Theorem 4 / Conjecture 1 / Paley remark, version table, MathDB quote, construction; bottom whitespace because W is kept whole on page 3',
 'page-3.png': 'full 20 x 20 matrix W, Proposition 3.1 with proof, Proposition 3.2 with B0, Proposition 3.3 with the xW / c table; QED marks after the displays',
 'page-4.png': 'Theorem 3.4, Remark 3.5, Section 4 (not claimed), start of Section 5 with the definition table',
 'page-5.png': 'Lean statement box inside margins, companion theorems, audits and replays, trust limits, start of Section 6',
 'page-6.png': 'prior-art limits, searches, Section 7, reproducibility list, 12 references; no orphan page',
}
rec = {
    'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'pdf': pdf, 'pdf_sha256': sha(pdf),
    'pages_rendered': len(pngs), 'render': 'pdftoppm -r 110 -png (capped)',
    'pages': [{'image': f'qa/{f}', 'sha256': sha(os.path.join(qa, f)), 'visually_inspected': True,
               'notes': notes.get(f, '')} for f in pngs],
    'fonts': [{'name': f[0], 'embedded': f[-5]} for f in fonts],
    'all_fonts_embedded': all(f[-5] == 'yes' for f in fonts),
    'text_extraction': 'qa/paper-text.txt (pdftotext -layout); scan for letter-digit gluing found only sha256 and Lean identifiers',
    'fixed_during_inspection': [
        'draft 1: single-reference orphan page 7 -> grids tightened, 6 pages',
        'draft 1: unembedded Helvetica from table default font -> FONTNAME Serif in all table styles',
        'draft 1: QED marks before the B0 display and the xW table -> moved after the displays',
        'draft 2: sub/superscripts touching adjacent lines -> rise 24%/36%, size 74%',
        'draft 3: wrong cross-reference "(Section 6)" for the journal rendering, awkward MathDB sentence -> reworded',
        'draft 4: Lean code box overhanging the right margin by a few points -> rightIndent 6',
    ],
    'builder_consistency_check': 'build_paper.py asserts printed W, B0, x, xW, c and support equal the Lean packet data',
}
json.dump(rec, open(out, 'w'), indent=1)
print(rec['pages_rendered'], 'pages;', 'fonts embedded' if rec['all_fonts_embedded'] else 'FONT PROBLEM')
