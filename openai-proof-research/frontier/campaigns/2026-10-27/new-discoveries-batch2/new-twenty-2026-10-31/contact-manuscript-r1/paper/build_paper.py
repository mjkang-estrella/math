#!/usr/bin/env python3
"""Requires reportlab; reads contact-draft.md and writes contact-draft.pdf here."""
from pathlib import Path
from xml.sax.saxutils import escape
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, PageBreak, Preformatted
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib.colors import HexColor
import os
p=Path(__file__).resolve().parent
fonts=Path(os.environ.get('FONT_DIR','/usr/share/fonts'))
for n,f in [('Serif','liberation-serif-fonts/LiberationSerif-Regular.ttf'),('Bold','liberation-serif-fonts/LiberationSerif-Bold.ttf'),('Mono','liberation-mono-fonts/LiberationMono-Regular.ttf')]:pdfmetrics.registerFont(TTFont(n,str(fonts/f)))
body=ParagraphStyle('Body',fontName='Serif',fontSize=10.2,leading=14.2,spaceAfter=7)
head=ParagraphStyle('Head',fontName='Bold',fontSize=12,leading=16,spaceBefore=5,spaceAfter=9)
title=ParagraphStyle('Title',fontName='Bold',fontSize=19,leading=23,spaceAfter=13,textColor=HexColor('#172c43'))
mono=ParagraphStyle('Mono',fontName='Mono',fontSize=8.2,leading=11,spaceBefore=3,spaceAfter=9)
items=[]
s=(p/'contact-draft.md').read_text().replace('---PAGE---', '\n\n---PAGE---\n\n')
for part in s.split('\n\n'):
 part=part.strip('\n')
 if not part.strip():continue
 if part.strip()=='---PAGE---':items.append(PageBreak())
 elif part.startswith('# '):items.append(Paragraph(escape(part[2:]),title))
 elif part.startswith('## '):items.append(Paragraph(escape(part[3:]),head))
 elif part.startswith('    '):items.append(Preformatted('\n'.join(l[4:] if l.startswith('    ') else l for l in part.splitlines()),mono))
 else:items.append(Paragraph(escape(part.replace('\n',' ')),body))
def footer(c,d):
 c.setStrokeColor(HexColor('#b7c2cd'));c.line(48,42,564,42)
 c.setFont('Serif',8);c.setFillColor(HexColor('#435365'))
 c.drawString(48,29,'DRAFT | MathDB 365301 | AI-assisted manuscript')
 c.drawRightString(564,29,str(d.page))
doc=SimpleDocTemplate(str(p/'contact-draft.pdf'),pagesize=(612,792),leftMargin=48,rightMargin=48,topMargin=42,bottomMargin=52,title='A five-vertex counterexample to nearest-colour contact order',author='AI-assisted research draft')
doc.build(items,onFirstPage=footer,onLaterPages=footer)
print('PDF built:',p/'contact-draft.pdf')
