from pathlib import Path
import sys,html,re
sys.path.insert(0,str(Path('../tabminors-manuscript-r1/tmp/pdf-deps').resolve()))
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,PageBreak,Table,TableStyle
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib import colors
for name,f in [('Body','Carlito-Regular.ttf'),('Bold','Carlito-Bold.ttf'),('Mono','AdwaitaMono-Regular.ttf')]:
 pdfmetrics.registerFont(TTFont(name,str(Path('fonts')/f)))
pdfmetrics.registerFontFamily('Body',normal='Body',bold='Bold',italic='Body',boldItalic='Bold')
styles={
 'body':ParagraphStyle('body',fontName='Body',fontSize=10,leading=14,spaceAfter=9),
 'title':ParagraphStyle('title',fontName='Bold',fontSize=19,leading=24,spaceAfter=15),
 'h':ParagraphStyle('h',fontName='Bold',fontSize=13,leading=17,spaceAfter=13),
 'formula':ParagraphStyle('formula',fontName='Mono',fontSize=8.4,leading=12,spaceAfter=11,leftIndent=12),
 'cell':ParagraphStyle('cell',fontName='Body',fontSize=8.2,leading=11,spaceAfter=0)}
def mark(s):
 s=html.escape(s)
 s=re.sub(r'\*\*(.*?)\*\*',r'<b>\1</b>',s)
 s=re.sub(r'`(.*?)`',r'<font name="Mono" size="8.1">\1</font>',s)
 return s
story=[]
for pageidx,section in enumerate(Path('paper.md').read_text().split('---PAGE---')):
 if pageidx:story.append(PageBreak())
 blocks=section.strip().split('\n\n')
 for block in blocks:
  if block.startswith('|'):
   rows=[[Paragraph(mark(cell.strip()),styles['cell']) for cell in line.strip('|').split('|')] for line in block.splitlines()]
   t=Table(rows,colWidths=[159,333],hAlign='LEFT');t.setStyle(TableStyle([('VALIGN',(0,0),(-1,-1),'TOP'),('BACKGROUND',(0,0),(-1,0),colors.HexColor('#e8edf2')),('LINEBELOW',(0,0),(-1,0),.6,colors.grey),('BOTTOMPADDING',(0,0),(-1,-1),6),('TOPPADDING',(0,0),(-1,-1),5)]));story.extend([t,Spacer(1,12)]);continue
  if block.startswith('# '):key='title';block=block[2:]
  elif block.startswith('## '):key='h';block=block[3:]
  elif block.startswith('`') and block.endswith('`'):key='formula';block=block[1:-1]
  else:key='body'
  story.append(Paragraph(mark(block.replace('\n',' ')),styles[key]))
def footer(c,d):
 c.setFont('Body',8);c.setFillColor(colors.HexColor('#5c6570'));c.drawString(51,30,'DRAFT | Signed-quotient obstruction | MathDB 365943');c.drawRightString(561,30,str(d.page))
doc=SimpleDocTemplate('nut-draft.pdf',pagesize=(612,792),rightMargin=54,leftMargin=54,topMargin=46,bottomMargin=48,title='No cubic 8-circulant nut graph: a signed-quotient obstruction',author='AI-assisted MathDB campaign draft')
doc.build(story,onFirstPage=footer,onLaterPages=footer)
print('Rendered nut-draft.pdf')
