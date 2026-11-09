"""Build the draft PDF from manuscript.md (MathDB 324342).

    python3 -I -B build_paper.py OUT.pdf [REPORTLAB_DIR]

Adapted from the reportlab builder of the asep-manuscript-r1 lane.  Needs reportlab 5.1.0
(importable, or in REPORTLAB_DIR) and the system fonts Liberation Serif/Mono, Noto Sans Math and
Symbola under /usr/share/fonts.  Before typesetting, it checks that the matrix W, the inverse B0,
the coefficient vector and the codeword printed in manuscript.md equal the data in the Lean
endpoint module inside ../lean/324342-replay-fit-source.zip (read in memory, not extracted).

Markup: '# ' title, '!BYLINE', '!STATUS', '## ' heading, '!QUOTE', '!DISPLAY', '!THEOREM' (label up
to the first '. ' in bold), '!PROOF', '!GRID size label' + rows, '!WORD' (3 x 20 table),
'!TABLE w1,w2,..' ... '!ENDTABLE' (' | ' cells), '!CODE' ... '!ENDCODE', '!REF', '- ' bullets,
**bold**, *italic*, `code`, and reportlab inline <sub>/<super> tags.
"""
import html, re, sys, zipfile
from pathlib import Path

if len(sys.argv) > 2:
    sys.path.insert(0, sys.argv[2])
from reportlab import rl_config
from reportlab.lib import colors
from reportlab.lib.enums import TA_CENTER, TA_JUSTIFY, TA_LEFT, TA_RIGHT
from reportlab.lib.fonts import addMapping
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import (KeepTogether, ListFlowable, ListItem, Paragraph, SimpleDocTemplate, Spacer,
                                Table, TableStyle, XPreformatted)

HERE = Path(__file__).resolve().parent
F = Path('/usr/share/fonts')
FONTS = {
    'Serif': F / 'liberation-serif-fonts/LiberationSerif-Regular.ttf',
    'Serif-Italic': F / 'liberation-serif-fonts/LiberationSerif-Italic.ttf',
    'Serif-Bold': F / 'liberation-serif-fonts/LiberationSerif-Bold.ttf',
    'Serif-BoldItalic': F / 'liberation-serif-fonts/LiberationSerif-BoldItalic.ttf',
    'Mono': F / 'liberation-mono-fonts/LiberationMono-Regular.ttf',
    'Math': F / 'google-noto/NotoSansMath-Regular.ttf',
    'Symbols': F / 'gdouros-symbola/Symbola.ttf',
}
for name, path in FONTS.items():
    pdfmetrics.registerFont(TTFont(name, str(path)))
rl_config.canvas_basefontname = 'Serif'
addMapping('Serif', 0, 0, 'Serif')
addMapping('Serif', 0, 1, 'Serif-Italic')
addMapping('Serif', 1, 0, 'Serif-Bold')
addMapping('Serif', 1, 1, 'Serif-BoldItalic')
addMapping('Mono', 0, 0, 'Mono')
addMapping('Mono', 0, 1, 'Mono')
addMapping('Mono', 1, 0, 'Mono')
addMapping('Mono', 1, 1, 'Mono')
TITLE = ('A skew conference matrix of order 20 whose row code over F_19 is not MDS: '
         'a counterexample to a conjecture of Etzion, Vardy and Yaakobi')


def has(font, ch):
    return ord(ch) in pdfmetrics.getFont(font).face.charToGlyph


def text_frag(s, base='Serif'):
    out = []
    for ch in s:
        if ch in '\n\t ' or has(base, ch):
            out.append(html.escape(ch, quote=False))
            continue
        alt = next((f for f in ('Math', 'Symbols') if has(f, ch)), None)
        if alt is None:
            raise SystemExit(f'missing glyph {ch!r} (U+{ord(ch):04X})')
        out.append(f'<font name="{alt}">{html.escape(ch, quote=False)}</font>')
    return ''.join(out)


TAG = re.compile(r'(</?(?:sub|super|b|i)>)')
# gentler than reportlab's default (rise 50%, size -2pt), so scripts do not touch adjacent lines
SUBSUP = {'<sub>': '<sub rise="24%" size="74%">', '<super>': '<super rise="36%" size="74%">'}


def inline(s, base='Serif'):
    parts = s.split('`')
    assert len(parts) % 2 == 1, 'unbalanced backticks: ' + s[:60]
    out = []
    for k, seg in enumerate(parts):
        if k % 2:
            out.append(f'<font name="Mono" size="8.8">{text_frag(seg, "Mono")}</font>')
            continue
        seg = re.sub(r'\*\*(.+?)\*\*', r'<b>\1</b>', seg)
        seg = re.sub(r'(?<![\w*])\*(?!\s)(.+?)(?<!\s)\*(?![\w*])', r'<i>\1</i>', seg)
        out.append(''.join(SUBSUP.get(p, p) if TAG.fullmatch(p) else text_frag(p, base) for p in TAG.split(seg)))
    return ''.join(out)


ST = {
    'title': ParagraphStyle('title', fontName='Serif-Bold', fontSize=15.5, leading=19.5, alignment=TA_CENTER,
                            spaceAfter=6),
    'byline': ParagraphStyle('byline', fontName='Serif-Italic', fontSize=9.2, leading=11.8, alignment=TA_CENTER,
                             spaceAfter=9),
    'status': ParagraphStyle('status', fontName='Serif', fontSize=8.6, leading=11.2, alignment=TA_JUSTIFY,
                             backColor=colors.HexColor('#f1f1ec'), borderPadding=(5, 6, 5, 6), spaceAfter=12,
                             borderColor=colors.HexColor('#b9b9ad'), borderWidth=0.5),
    'h': ParagraphStyle('h', fontName='Serif-Bold', fontSize=11.6, leading=15, spaceBefore=7, spaceAfter=4,
                        keepWithNext=1),
    'body': ParagraphStyle('body', fontName='Serif', fontSize=10, leading=13.1, alignment=TA_JUSTIFY, spaceAfter=5.5),
    'quote': ParagraphStyle('quote', fontName='Serif-Italic', fontSize=9.6, leading=12.6, leftIndent=20,
                            rightIndent=20, spaceBefore=1, spaceAfter=6, alignment=TA_JUSTIFY),
    'thm': ParagraphStyle('thm', fontName='Serif-Italic', fontSize=10, leading=13.1, alignment=TA_JUSTIFY,
                          spaceBefore=3, spaceAfter=5),
    'proof': ParagraphStyle('proof', fontName='Serif', fontSize=10, leading=13.1, alignment=TA_JUSTIFY,
                            spaceAfter=6),
    'display': ParagraphStyle('display', fontName='Serif', fontSize=10, leading=13.5, alignment=TA_CENTER,
                              spaceBefore=1, spaceAfter=6),
    'cell': ParagraphStyle('cell', fontName='Serif', fontSize=8.4, leading=10.3),
    'cellh': ParagraphStyle('cellh', fontName='Serif-Bold', fontSize=8.5, leading=10.4),
    'bullet': ParagraphStyle('bullet', fontName='Serif', fontSize=10, leading=13.1, alignment=TA_JUSTIFY),
    'code': ParagraphStyle('code', fontName='Mono', fontSize=8.1, leading=10.2, leftIndent=6, rightIndent=6,
                           backColor=colors.HexColor('#f4f4f0'), borderPadding=(4, 5, 4, 5),
                           borderColor=colors.HexColor('#c8c8c0'), borderWidth=0.4, spaceBefore=3, spaceAfter=9),
    'ref': ParagraphStyle('ref', fontName='Serif', fontSize=8.8, leading=11.2, leftIndent=18, firstLineIndent=-18,
                          spaceAfter=3, alignment=TA_LEFT),
}


def bullets(lines):
    items = [ListItem(Paragraph(inline(l[2:]), ST['bullet']), leftIndent=14, value='•') for l in lines]
    return ListFlowable(items, bulletType='bullet', start='•', leftIndent=14, bulletFontName='Serif',
                        bulletFontSize=9, spaceAfter=5)


def grid(label, rows, size):
    cw = max(len(t) for r in rows for t in r) * size * 0.62 + 5.2
    st = ParagraphStyle('g', fontName='Mono', fontSize=size, leading=size + 1.6, alignment=TA_CENTER)
    t = Table([[Paragraph(text_frag(c, 'Mono'), st) for c in r] for r in rows], colWidths=[cw] * len(rows[0]),
              hAlign='CENTER')
    t.setStyle(TableStyle([('FONTNAME', (0, 0), (-1, -1), 'Serif'), ('LINEBEFORE', (0, 0), (0, -1), 0.7, colors.black),
                           ('LINEAFTER', (-1, 0), (-1, -1), 0.7, colors.black),
                           ('LINEABOVE', (0, 0), (0, 0), 0.7, colors.black), ('LINEABOVE', (-1, 0), (-1, 0), 0.7, colors.black),
                           ('LINEBELOW', (0, -1), (0, -1), 0.7, colors.black), ('LINEBELOW', (-1, -1), (-1, -1), 0.7, colors.black),
                           ('TOPPADDING', (0, 0), (-1, -1), 0), ('BOTTOMPADDING', (0, 0), (-1, -1), 0.4),
                           ('LEFTPADDING', (0, 0), (-1, -1), 0), ('RIGHTPADDING', (0, 0), (-1, -1), 0)]))
    lab = Paragraph(inline(label), ParagraphStyle('gl', parent=ST['body'], alignment=TA_RIGHT))
    outer = Table([[lab, t]], colWidths=[40, cw * len(rows[0]) + 4], hAlign='CENTER')
    outer.setStyle(TableStyle([('FONTNAME', (0, 0), (-1, -1), 'Serif'), ('VALIGN', (0, 0), (-1, -1), 'MIDDLE')]))
    return KeepTogether([Spacer(1, 2), outer, Spacer(1, 7)])


def word_table(labels, rows):
    st = ParagraphStyle('w', fontName='Mono', fontSize=7.6, leading=9.4, alignment=TA_CENTER)
    sth = ParagraphStyle('wh', fontName='Serif-Bold', fontSize=8.4, leading=9.6, alignment=TA_LEFT)
    data = [[Paragraph(inline(labels[k]), sth)] + [Paragraph(text_frag(c, 'Mono'), st) for c in r]
            for k, r in enumerate(rows)]
    t = Table(data, colWidths=[28] + [21.5] * 20, hAlign='CENTER')
    t.setStyle(TableStyle([('FONTNAME', (0, 0), (-1, -1), 'Serif'), ('LINEABOVE', (0, 0), (-1, 0), 0.7, colors.black),
                           ('LINEBELOW', (0, 0), (-1, 0), 0.4, colors.black),
                           ('LINEBELOW', (0, -1), (-1, -1), 0.7, colors.black),
                           ('BACKGROUND', (0, 2), (-1, 2), colors.HexColor('#f1f1ec')),
                           ('TOPPADDING', (0, 0), (-1, -1), 1.5), ('BOTTOMPADDING', (0, 0), (-1, -1), 1.8),
                           ('LEFTPADDING', (0, 0), (-1, -1), 1), ('RIGHTPADDING', (0, 0), (-1, -1), 1)]))
    return KeepTogether([Spacer(1, 2), t, Spacer(1, 7)])


def lean_data():
    """Witness data from the Lean endpoint module in the replayed source ZIP."""
    src = zipfile.ZipFile(HERE.parent / 'lean' / '324342-replay-fit-source.zip').read('ConferenceMDS324342.lean').decode()

    def lists(name):
        start = src.index('\ndef ' + name + ' ')
        block = src[start:src.index('\n\n', start + 1)]
        return [[int(x) for x in b.split(',')] for b in re.findall(r'\[([-\d,\s]+)\]', block)]
    return {'W': lists('Wrows'), 'B': lists('Blist'), 'coeff': lists('coeff')[0], 'word': lists('word')[0]}


def check_against_lean(grids, words, src):
    d = lean_data()
    sym = {'+': 1, '−': -1, '0': 0}
    W = [[sym[t] for t in r] for r in grids['W =']]
    assert W == d['W'], 'printed W differs from the Lean packet'
    assert [[int(t) for t in r] for r in grids['B<sub>0</sub> =']] == d['B'], 'printed B0 differs'
    m = re.search(r'Let x = \(([\d, ]+), 0, …, 0\)', src)
    x = [int(t) for t in m.group(1).split(',')]
    assert x + [0] * (20 - len(x)) == d['coeff'], 'printed coefficients differ'
    idx, comb, c = words
    assert [int(t) for t in idx] == list(range(20))
    comb = [int(t.replace('−', '-')) for t in comb]
    assert comb == [sum(d['coeff'][i] * d['W'][i][j] for i in range(20)) for j in range(20)], 'printed xW wrong'
    assert [int(t) for t in c] == d['word'] == [v % 19 for v in comb], 'printed codeword differs'
    supp = [j for j in range(20) if d['word'][j]]
    assert 'Its support is {' + ', '.join(map(str, supp)) + '}' in src and len(supp) == 9
    return 'printed W, B0, x, xW and c agree with the Lean packet'


def build(out):
    src = (HERE / 'manuscript.md').read_text()
    blocks = re.split(r'\n\s*\n', src.strip())
    story, grids, words, i = [], {}, None, 0
    while i < len(blocks):
        b = blocks[i].rstrip()
        i += 1
        if b.startswith('# '):
            story.append(Paragraph(inline(b[2:], 'Serif-Bold'), ST['title']))
        elif b.startswith('!BYLINE '):
            story.append(Paragraph(inline(b[8:], 'Serif-Italic'), ST['byline']))
        elif b.startswith('!STATUS '):
            story.append(Paragraph(inline(b[8:]), ST['status']))
        elif b.startswith('## '):
            story.append(Paragraph(inline(b[3:], 'Serif-Bold'), ST['h']))
        elif b.startswith('!QUOTE '):
            story.append(Paragraph(inline(b[7:], 'Serif-Italic'), ST['quote']))
        elif b.startswith('!DISPLAY '):
            story.append(Paragraph(inline(b[9:]), ST['display']))
        elif b.startswith('!GRID '):
            lines = b.splitlines()
            size, label = lines[0][6:].split(' ', 1)
            rows = [l.split() for l in lines[1:]]
            assert len({len(r) for r in rows}) == 1
            grids[label] = rows
            story.append(grid(label, rows, float(size)))
        elif b.startswith('!WORD '):
            lines = b.splitlines()
            labels = [x.strip() for x in lines[0][6:].split('|')]
            rows = [l.split() for l in lines[1:]]
            assert len(rows) == 3 and all(len(r) == 20 for r in rows)
            words = rows
            story.append(word_table(labels, rows))
        elif b.startswith('!THEOREM '):
            lab, rest = b[9:].replace('\n', ' ').split('. ', 1)
            story.append(Paragraph(f'<b><font name="Serif-Bold">{inline(lab, "Serif-Bold")}.</font></b> '
                                   + inline(rest, 'Serif-Italic'), ST['thm']))
        elif b.startswith('!PROOFOPEN '):
            story.append(Paragraph('<i>Proof.</i> ' + inline(b[11:].replace('\n', ' ')), ST['proof']))
        elif b.startswith('!QED '):
            story.append(Paragraph(inline(b[5:].replace('\n', ' ')) + ' ' + text_frag('∎'), ST['proof']))
        elif b.startswith('!PROOF '):
            story.append(Paragraph('<i>Proof.</i> ' + inline(b[7:].replace('\n', ' ')) + ' ' + text_frag('∎'),
                                   ST['proof']))
        elif b.startswith('!TABLE '):
            widths = [float(x) for x in b.splitlines()[0][7:].split(',')]
            body = b.splitlines()[1:]
            while not (body and body[-1].strip() == '!ENDTABLE'):
                body += blocks[i].splitlines()
                i += 1
            rows = []
            for k, l in enumerate(body[:-1]):
                c = [x.strip() for x in l.split(' | ')]
                assert len(c) == len(widths), l
                st = ST['cellh'] if k == 0 else ST['cell']
                rows.append([Paragraph(inline(x, st.fontName), st) for x in c])
            t = Table(rows, colWidths=widths, hAlign='CENTER', repeatRows=1)
            t.setStyle(TableStyle([('FONTNAME', (0, 0), (-1, -1), 'Serif'), ('VALIGN', (0, 0), (-1, -1), 'TOP'),
                                   ('BACKGROUND', (0, 0), (-1, 0), colors.HexColor('#e8e8e2')),
                                   ('LINEABOVE', (0, 0), (-1, 0), 0.8, colors.black),
                                   ('LINEBELOW', (0, 0), (-1, 0), 0.5, colors.black),
                                   ('LINEBELOW', (0, -1), (-1, -1), 0.8, colors.black),
                                   ('LINEBELOW', (0, 1), (-1, -2), 0.25, colors.HexColor('#c8c8c0')),
                                   ('TOPPADDING', (0, 0), (-1, -1), 2.2), ('BOTTOMPADDING', (0, 0), (-1, -1), 2.6)]))
            story.extend([Spacer(1, 2), t, Spacer(1, 8)])
        elif b.startswith('!CODE'):
            body = b.splitlines()[1:]
            while not (body and body[-1].strip() == '!ENDCODE'):
                body += [''] + blocks[i].splitlines()
                i += 1
            story.append(XPreformatted('\n'.join(text_frag(l, 'Mono') for l in body[:-1]), ST['code']))
        elif b.startswith('!REF '):
            for l in b.splitlines():
                story.append(Paragraph(inline(l[5:]), ST['ref']))
        else:
            lines = b.splitlines()
            if all(l.startswith('- ') for l in lines):
                story.append(bullets(lines))
            else:
                k = next((j for j, l in enumerate(lines) if l.startswith('- ')), None)
                if k is None:
                    story.append(Paragraph(inline(' '.join(lines)), ST['body']))
                else:
                    assert all(l.startswith('- ') for l in lines[k:]), lines[0][:50]
                    story.append(KeepTogether([Paragraph(inline(' '.join(lines[:k])), ST['body']),
                                               bullets(lines[k:])]) if len(lines) - k <= 3 else
                                 Paragraph(inline(' '.join(lines[:k])), ST['body']))
                    if len(lines) - k > 3:
                        story.append(bullets(lines[k:]))
    print(check_against_lean(grids, words, src))
    bound = []
    for f in story:  # bind every section heading to the flowable that follows it
        if bound and isinstance(bound[-1], Paragraph) and bound[-1].style is ST['h']:
            bound[-1] = KeepTogether([bound[-1], f])
        else:
            bound.append(f)

    def footer(c, d):
        c.saveState()
        c.setFont('Serif', 7.6)
        c.drawString(56, 30, 'DRAFT  ·  MathDB 324342  ·  AI-assisted (Claude Opus 5.5)  ·  not peer reviewed  ·  no priority claim')
        c.drawRightString(A4[0] - 56, 30, str(d.page))
        c.restoreState()
    doc = SimpleDocTemplate(str(out), pagesize=A4, leftMargin=56, rightMargin=56, topMargin=50, bottomMargin=50,
                            title=TITLE, author='AI-assisted draft (Claude Opus 5.5); no human authorship claimed',
                            subject='MathDB 324342; arXiv:1210.5725 Conjecture 5; IEEE TIT 59(10) Conjecture 1',
                            creator='build_paper.py (reportlab)', invariant=1)
    doc.build(bound, onFirstPage=footer, onLaterPages=footer)


if __name__ == '__main__':
    build(Path(sys.argv[1]))
