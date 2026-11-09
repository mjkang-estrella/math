#!/usr/bin/env python3
"""Build paper.md (includes expanded) and render paper.pdf with the lane-local reportlab copy.

Usage (from the lane root): python3 -I scripts/render.py
Markup: '# ' title, '## ' section, '@@ ' status box, 4-space indented display lines,
'|' tables, ``` code fences, `code`, **bold**, *italic*, _{sub} / ^{sup} and bare _x / ^x tokens,
{{include:FILE}} (relative to paper-src/).
"""
import re, sys
from pathlib import Path
from xml.sax.saxutils import escape

LANE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(LANE / 'tmp' / 'pdf-deps'))
from reportlab.lib import colors  # noqa: E402
from reportlab.lib.enums import TA_CENTER, TA_JUSTIFY  # noqa: E402
from reportlab.lib.styles import ParagraphStyle  # noqa: E402
from reportlab.pdfbase import pdfmetrics  # noqa: E402
from reportlab.pdfbase.ttfonts import TTFont  # noqa: E402
from reportlab.lib.fonts import addMapping  # noqa: E402
from reportlab.platypus import (SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle,  # noqa: E402
                                XPreformatted, KeepTogether)

F = LANE / 'fonts'
for name, file in [('Body', 'LiberationSerif-Regular.ttf'), ('BodyB', 'LiberationSerif-Bold.ttf'),
                   ('BodyI', 'LiberationSerif-Italic.ttf'), ('Mono', 'LiberationMono-Regular.ttf'),
                   ('Sym', 'Symbola.ttf')]:
    pdfmetrics.registerFont(TTFont(name, str(F / file)))
addMapping('Body', 0, 0, 'Body'); addMapping('Body', 1, 0, 'BodyB')
addMapping('Body', 0, 1, 'BodyI'); addMapping('Body', 1, 1, 'BodyB')
BODY_CMAP = set(pdfmetrics.getFont('Body').face.charToGlyph) - {ord('∎')}  # tiny in Liberation; use Symbola
MONO_CMAP = set(pdfmetrics.getFont('Mono').face.charToGlyph)

S = {
    'T': ParagraphStyle('T', fontName='BodyB', fontSize=15.5, leading=19, alignment=TA_CENTER, spaceAfter=10),
    'H': ParagraphStyle('H', fontName='BodyB', fontSize=11.6, leading=14.5, spaceBefore=8, spaceAfter=5, keepWithNext=1),
    'B': ParagraphStyle('B', fontName='Body', fontSize=9.9, leading=13.3, spaceAfter=5.5, alignment=TA_JUSTIFY),
    'D': ParagraphStyle('D', fontName='Body', fontSize=9.9, leading=13.6, leftIndent=26, spaceBefore=1, spaceAfter=6),
    'X': ParagraphStyle('X', fontName='BodyI', fontSize=8.8, leading=11.6, spaceAfter=10, borderColor=colors.HexColor('#9aa7b2'),
                        borderWidth=0.6, borderPadding=6, backColor=colors.HexColor('#f2f5f7'), alignment=TA_JUSTIFY),
    'C': ParagraphStyle('C', fontName='Mono', fontSize=7.3, leading=9.6, leftIndent=8, spaceAfter=8, spaceBefore=2),
    'TC': ParagraphStyle('TC', fontName='Body', fontSize=8.1, leading=10.0),
    'TH': ParagraphStyle('TH', fontName='BodyB', fontSize=8.1, leading=10.0),
    'L': ParagraphStyle('L', fontName='Body', fontSize=9.9, leading=13.3, leftIndent=14, bulletIndent=4, spaceAfter=3),
}


def sym_fallback(markup, cmap):
    out = []
    for part in re.split(r'(<[^>]+>|&[a-z]+;|&#\d+;)', markup):
        if part.startswith('<') or (part.startswith('&') and part.endswith(';')):
            out.append(part); continue
        buf = ''
        for ch in part:
            if ord(ch) in cmap or ch in '\n':
                buf += ch
            else:
                buf += f'<font name="Sym">{ch}</font>'
        out.append(buf)
    return ''.join(out)


def scripts(t):
    """Convert _{..}/^{..} (nested) and bare _tok/^tok to sub/super tags. t is already XML-escaped."""
    res, i = '', 0
    while i < len(t):
        ch = t[i]
        if ch in '_^' and i + 1 < len(t):
            tag = 'sub' if ch == '_' else 'super'
            if t[i + 1] == '{':
                depth, j = 0, i + 1
                while j < len(t):
                    if t[j] == '{': depth += 1
                    elif t[j] == '}':
                        depth -= 1
                        if depth == 0: break
                    j += 1
                res += f'<{tag}>{scripts(t[i + 2:j])}</{tag}>'; i = j + 1; continue
            m = re.match(r'[A-Za-z0-9]+', t[i + 1:])
            if m:
                res += f'<{tag}>{m.group(0)}</{tag}>'; i += 1 + len(m.group(0)); continue
        res += ch; i += 1
    return res


def inline(text):
    codes = []
    def keep(m):
        codes.append(m.group(1)); return f'§§{len(codes) - 1}§§'
    text = re.sub(r'`([^`]+)`', keep, text)
    t = escape(text)
    t = re.sub(r'\*\*(.+?)\*\*', r'<b>\1</b>', t)
    t = re.sub(r'(?<![\w*])\*(?!\s)(.+?)(?<!\s)\*(?![\w*])', r'<i>\1</i>', t)
    t = scripts(t)
    t = re.sub(r' {2,}', lambda m: '&nbsp;' * len(m.group(0)), t)
    t = sym_fallback(t, BODY_CMAP)
    def put(m):
        c = sym_fallback(escape(codes[int(m.group(1))]), MONO_CMAP)
        return f'<font name="Mono" size="8.2">{c}</font>'
    return re.sub(r'§§(\d+)§§', put, t)


def table(lines):
    rows = [[c.strip() for c in l.strip().strip('|').split('|')] for l in lines if not re.match(r'^\|[-| ]+\|$', l.strip())]
    n = len(rows[0])
    widths = {2: [150, 334], 4: [26, 196, 108, 108], 5: [36, 40, 66, 206, 136], 6: [26, 128, 78, 86, 78, 78]}[n]
    data = [[Paragraph(inline(c), S['TH'] if r == 0 else S['TC']) for c in row] for r, row in enumerate(rows)]
    t = Table(data, colWidths=widths, hAlign='LEFT', repeatRows=1)
    t.setStyle(TableStyle([('VALIGN', (0, 0), (-1, -1), 'TOP'), ('BACKGROUND', (0, 0), (-1, 0), colors.HexColor('#e8edf1')),
                           ('LINEBELOW', (0, 0), (-1, 0), 0.6, colors.grey), ('LINEBELOW', (0, -1), (-1, -1), 0.6, colors.grey),
                           ('TOPPADDING', (0, 0), (-1, -1), 1.6), ('BOTTOMPADDING', (0, 0), (-1, -1), 1.6),
                           ('LEFTPADDING', (0, 0), (-1, -1), 3), ('RIGHTPADDING', (0, 0), (-1, -1), 3)]))
    return t


def build_md():
    src = (LANE / 'paper-src' / 'paper.src.md').read_text(encoding='utf-8')
    md = re.sub(r'\{\{include:([^}]+)\}\}', lambda m: (LANE / 'paper-src' / m.group(1)).read_text(encoding='utf-8').strip(), src)
    import json
    status = json.loads((LANE / 'paper-src' / 'status.json').read_text(encoding='utf-8'))
    md = re.sub(r'\{\{(STATUS_[A-Z0-9_]+)\}\}', lambda m: status[m.group(1)], md)
    assert '{{' not in md, 'unexpanded token'
    (LANE / 'paper.md').write_text(md, encoding='utf-8')
    return md


def story_of(md):
    story, lines, i = [], md.split('\n'), 0
    while i < len(lines):
        l = lines[i]
        if not l.strip():
            i += 1; continue
        if l.startswith('```'):
            j = i + 1
            while not lines[j].startswith('```'): j += 1
            code = sym_fallback(escape('\n'.join(lines[i + 1:j])), MONO_CMAP)
            story.append(XPreformatted(code, S['C'])); i = j + 1; continue
        if l.startswith('|'):
            j = i
            while j < len(lines) and lines[j].startswith('|'): j += 1
            story.append(table(lines[i:j])); story.append(Spacer(1, 8)); i = j; continue
        if l.startswith('# '):
            story.append(Paragraph(inline(l[2:]), S['T'])); i += 1; continue
        if l.startswith('## '):
            story.append(Paragraph(inline(l[3:]), S['H'])); i += 1; continue
        if l.startswith('@@ '):
            story.append(Paragraph(inline(l[3:]), S['X'])); i += 1; continue
        if l.startswith('    '):
            story.append(Paragraph(inline(l.strip()), S['D'])); i += 1; continue
        if l.startswith('- '):
            story.append(Paragraph(inline(l[2:]), S['L'], bulletText='•')); i += 1; continue
        j = i
        while j < len(lines) and lines[j].strip() and not re.match(r'^(```|\||#|@@ |    |- )', lines[j]): j += 1
        para = ' '.join(x.strip() for x in lines[i:j])
        st = S['B']
        if para.startswith('**Table') and j < len(lines) and not lines[j].strip() and j + 1 < len(lines) and lines[j + 1].startswith('|'):
            st = ParagraphStyle('Bk', parent=S['B'], keepWithNext=1)
        story.append(Paragraph(inline(para), st)); i = j
    return story


def footer(c, d):
    c.saveState(); c.setFont('Body', 7.2); c.setFillColor(colors.grey)
    c.drawString(56, 26, 'DRAFT  |  AI-assisted  |  MathDB 345545  |  zero accepted credit; root review pending')
    c.drawRightString(540, 26, str(d.page)); c.restoreState()


def main():
    md = build_md()
    doc = SimpleDocTemplate(str(LANE / 'paper.pdf'), pagesize=(595.28, 841.89), leftMargin=56, rightMargin=56,
                            topMargin=50, bottomMargin=46,
                            title='The stack-sorting degree grows faster than 1.80^n (draft)',
                            author='AI-assisted draft; no human authorship asserted',
                            subject='MathDB 345545: refutation of Defant-Propp Conjecture 4.4',
                            creator='reportlab (lane-local copy)')
    doc.build(story_of(md), onFirstPage=footer, onLaterPages=footer)
    print('rendered paper.pdf')


if __name__ == '__main__':
    main()
