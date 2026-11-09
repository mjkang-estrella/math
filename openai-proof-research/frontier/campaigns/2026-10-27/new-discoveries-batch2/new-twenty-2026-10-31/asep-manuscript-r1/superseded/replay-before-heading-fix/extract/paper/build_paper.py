"""Build the draft PDF from manuscript.md.

    python3 -I build_paper.py OUT.pdf [REPORTLAB_DIR]

Needs reportlab 5.1.0 (importable, or in REPORTLAB_DIR) and the system fonts Liberation Serif/Mono,
Noto Sans Math and Symbola under /usr/share/fonts.  Markup: '# ' title, '## ' heading, '!STATUS',
'!QUOTE', '!THEOREM' (label up to the first '. ' in bold; '!ITEM'/'!ENDITEMS' lines inside),
'!DISPLAY', '!MATRIX label' + rows, '!TABLE' ... '!ENDTABLE' ('|' cells), '!REF', '- ' bullets,
**bold**, *italic*, and reportlab inline <sub>/<super> tags.
"""
import html, re, sys
from pathlib import Path

if len(sys.argv) > 2:
    sys.path.insert(0, sys.argv[2])
from reportlab.lib import colors
from reportlab.lib.enums import TA_CENTER, TA_JUSTIFY, TA_LEFT
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import (KeepTogether, ListFlowable, ListItem, Paragraph, SimpleDocTemplate, Spacer,
                                Table, TableStyle, XPreformatted)
from reportlab.lib.fonts import addMapping

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
from reportlab import rl_config
rl_config.canvas_basefontname = 'Serif'   # no unembedded base-14 font in the output
addMapping('Serif', 0, 0, 'Serif')
addMapping('Serif', 0, 1, 'Serif-Italic')
addMapping('Serif', 1, 0, 'Serif-Bold')
addMapping('Serif', 1, 1, 'Serif-BoldItalic')


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


def inline(s, base='Serif'):
    s = re.sub(r'\*\*(.+?)\*\*', r'<b>\1</b>', s)
    s = re.sub(r'(?<![\w*])\*(?!\s)(.+?)(?<!\s)\*(?![\w*])', r'<i>\1</i>', s)
    return ''.join(p if TAG.fullmatch(p) else text_frag(p, base) for p in TAG.split(s))


ST = {
    'title': ParagraphStyle('title', fontName='Serif-Bold', fontSize=16.5, leading=21, alignment=TA_CENTER, spaceAfter=10),
    'status': ParagraphStyle('status', fontName='Serif', fontSize=8.6, leading=11.2, alignment=TA_JUSTIFY,
                             backColor=colors.HexColor('#f1f1ec'), borderPadding=(5, 6, 5, 6), spaceAfter=12,
                             borderColor=colors.HexColor('#b9b9ad'), borderWidth=0.5),
    'h': ParagraphStyle('h', fontName='Serif-Bold', fontSize=11.6, leading=15, spaceBefore=7, spaceAfter=4,
                         keepWithNext=1),
    'body': ParagraphStyle('body', fontName='Serif', fontSize=10, leading=13.1, alignment=TA_JUSTIFY, spaceAfter=5.5),
    'quote': ParagraphStyle('quote', fontName='Serif-Italic', fontSize=10, leading=13.1, leftIndent=22, rightIndent=22,
                            spaceBefore=2, spaceAfter=7),
    'thm': ParagraphStyle('thm', fontName='Serif-Italic', fontSize=10, leading=13.1, alignment=TA_JUSTIFY,
                          spaceBefore=2, spaceAfter=6),
    'item': ParagraphStyle('item', fontName='Serif-Italic', fontSize=10, leading=13.1, leftIndent=22, firstLineIndent=-16,
                           spaceAfter=1.5),
    'display': ParagraphStyle('display', fontName='Serif', fontSize=10, leading=13.5, alignment=TA_CENTER,
                              spaceBefore=2, spaceAfter=7),
    'mono': ParagraphStyle('mono', fontName='Mono', fontSize=9, leading=11, leftIndent=170),
    'cell': ParagraphStyle('cell', fontName='Serif', fontSize=8.2, leading=10.1),
    'cellh': ParagraphStyle('cellh', fontName='Serif-Bold', fontSize=8.4, leading=10.3),
    'bullet': ParagraphStyle('bullet', fontName='Serif', fontSize=10, leading=13.1, alignment=TA_JUSTIFY),
    'ref': ParagraphStyle('ref', fontName='Serif', fontSize=8.8, leading=11.2, leftIndent=18, firstLineIndent=-18,
                          spaceAfter=3, alignment=TA_LEFT),
}


def bullets(lines):
    """'- ' items; '  - ' lines are sub-items of the preceding item."""
    tree = []
    for l in lines:
        if l.startswith('  - '):
            tree[-1][1].append(l[4:])
        else:
            assert l.startswith('- '), l
            tree.append((l[2:], []))
    items = []
    for top, subs in tree:
        flow = [Paragraph(inline(top), ST['bullet'])]
        if subs:
            flow.append(ListFlowable([ListItem(Paragraph(inline(x), ST['bullet']), leftIndent=12, value='–')
                                      for x in subs], bulletType='bullet', start='–', leftIndent=12,
                                     bulletFontName='Serif', bulletFontSize=9))
        items.append(ListItem(flow, leftIndent=14, value='•'))
    return ListFlowable(items, bulletType='bullet', start='•', leftIndent=14, bulletFontName='Serif',
                        bulletFontSize=9, spaceAfter=5)


def build(out):
    src = (HERE / 'manuscript.md').read_text()
    blocks = re.split(r'\n\s*\n', src.strip())
    story, i = [], 0
    while i < len(blocks):
        b = blocks[i].rstrip()
        i += 1
        if b.startswith('# '):
            story.append(Paragraph(inline(b[2:], 'Serif-Bold'), ST['title']))
        elif b.startswith('!STATUS '):
            story.append(Paragraph(inline(b[8:]), ST['status']))
        elif b.startswith('## '):
            story.append(Paragraph(inline(b[3:], 'Serif-Bold'), ST['h']))
        elif b.startswith('!QUOTE '):
            story.append(Paragraph(inline(b[7:], 'Serif-Italic'), ST['quote']))
        elif b.startswith('!DISPLAY '):
            story.append(Paragraph(inline(b[9:]), ST['display']))
        elif b.startswith('!MATRIX'):
            lines = b.splitlines()
            label = lines[0][len('!MATRIX'):].strip()
            rows = [l.split() for l in lines[1:]]
            t = Table([[Paragraph(text_frag(c, 'Mono'), ParagraphStyle('m', fontName='Mono', fontSize=9.2,
                                                                       leading=11, alignment=TA_CENTER))
                        for c in r] for r in rows], colWidths=[17] * 8, hAlign='CENTER')
            t.setStyle(TableStyle([('FONTNAME', (0, 0), (-1, -1), 'Serif'), ('LINEBEFORE', (0, 0), (0, -1), 0.6, colors.black),
                                   ('LINEAFTER', (-1, 0), (-1, -1), 0.6, colors.black),
                                   ('TOPPADDING', (0, 0), (-1, -1), 0), ('BOTTOMPADDING', (0, 0), (-1, -1), 0)]))
            lab = Paragraph(text_frag(f'X  =', 'Serif'), ST['body'])
            num = Paragraph(text_frag(label), ST['body'])
            outer = Table([[lab, t, num]], colWidths=[40, 150, 40], hAlign='CENTER')
            outer.setStyle(TableStyle([('FONTNAME', (0, 0), (-1, -1), 'Serif'), ('VALIGN', (0, 0), (-1, -1), 'MIDDLE')]))
            story.append(KeepTogether([Spacer(1, 2), outer, Spacer(1, 7)]))
        elif b.startswith('!THEOREM '):
            lines = b[9:].splitlines()
            parts = []

            def thm_par(text):
                if not parts:
                    lab, rest = text.split('. ', 1)
                    return Paragraph(f'<b><font name="Serif-Bold">{inline(lab, "Serif-Bold")}.</font></b> '
                                     + inline(rest, 'Serif-Italic'), ST['thm'])
                return Paragraph(inline(text, 'Serif-Italic'), ST['thm'])
            head, items, tail = [], [], []
            for l in lines:
                if l.startswith('!ITEM '):
                    items.append(l[6:])
                elif l.startswith('!ENDITEMS '):
                    tail.append(l[10:])
                elif items:
                    items[-1] += ' ' + l
                else:
                    head.append(l)
            parts.append(thm_par(' '.join(head)))
            for it in items:
                parts.append(Paragraph(inline(it, 'Serif-Italic'), ST['item']))
            if tail:
                parts.append(Paragraph(inline(' '.join(tail), 'Serif-Italic'), ST['thm']))
            story.append(KeepTogether(parts))
        elif b.startswith('!TABLE'):
            rows = []
            body = b.splitlines()[1:]
            while not (body and body[-1].strip() == '!ENDTABLE'):
                body += blocks[i].splitlines()
                i += 1
            for k, l in enumerate(body[:-1]):
                c = [x.strip() for x in l.split(' | ')]
                assert len(c) == 2, l
                st = ST['cellh'] if k == 0 else ST['cell']
                rows.append([Paragraph(inline(c[0], st.fontName), st), Paragraph(inline(c[1], st.fontName), st)])
            t = Table(rows, colWidths=[170, 312], hAlign='CENTER', repeatRows=1)
            t.setStyle(TableStyle([('FONTNAME', (0, 0), (-1, -1), 'Serif'), ('VALIGN', (0, 0), (-1, -1), 'TOP'),
                                   ('BACKGROUND', (0, 0), (-1, 0), colors.HexColor('#e8e8e2')),
                                   ('LINEABOVE', (0, 0), (-1, 0), 0.8, colors.black),
                                   ('LINEBELOW', (0, 0), (-1, 0), 0.5, colors.black),
                                   ('LINEBELOW', (0, -1), (-1, -1), 0.8, colors.black),
                                   ('LINEBELOW', (0, 1), (-1, -2), 0.25, colors.HexColor('#c8c8c0')),
                                   ('TOPPADDING', (0, 0), (-1, -1), 2.2), ('BOTTOMPADDING', (0, 0), (-1, -1), 2.6)]))
            story.extend([Spacer(1, 2), t, Spacer(1, 8)])
        elif b.startswith('!REF '):
            for l in b.splitlines():
                story.append(Paragraph(inline(l[5:]), ST['ref']))
        else:
            lines = b.splitlines()
            if all(l.startswith(('- ', '  - ')) for l in lines):
                story.append(bullets(lines))
            elif lines[0].startswith('- '):
                raise SystemExit('mixed bullet block: ' + lines[0][:40])
            else:
                k = next((j for j, l in enumerate(lines) if l.startswith('- ')), None)
                if k is None:
                    story.append(Paragraph(inline(' '.join(lines)), ST['body']))
                else:
                    story.append(Paragraph(inline(' '.join(lines[:k])), ST['body']))
                    story.append(bullets(lines[k:]))

    def footer(c, d):
        c.saveState()
        c.setFont('Serif', 7.6)
        c.drawString(56, 30, 'DRAFT  ·  MathDB 368807  ·  AI-assisted (Claude Opus 5.5)  ·  not peer reviewed  ·  no priority claim')
        c.drawRightString(A4[0] - 56, 30, str(d.page))
        c.restoreState()
    doc = SimpleDocTemplate(str(out), pagesize=A4, leftMargin=56, rightMargin=56, topMargin=52, bottomMargin=50,
                            title='A vertex of the asymmetric subtour elimination polytope on eight nodes that is adjacent to no tour',
                            author='AI-assisted draft (Claude Opus 5.5); no human authorship claimed',
                            subject='MathDB 368807; arXiv:2506.10671 Conjecture 1', creator='build_paper.py (reportlab)',
                            invariant=1)
    doc.build(story, onFirstPage=footer, onLaterPages=footer)


if __name__ == '__main__':
    build(Path(sys.argv[1]))
