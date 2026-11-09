from pathlib import Path
import re,html,json,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"vendor"))
from reportlab.pdfgen import canvas
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,Table,TableStyle,PageBreak,Preformatted
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib import colors
root=Path(__file__).resolve().parents[1]
for name,path in [('Body',str(root/'fonts'/'LiberationSerif-Regular.ttf')),('Bold',str(root/'fonts'/'LiberationSerif-Bold.ttf')),('Mono',str(root/'fonts'/'LiberationMono-Regular.ttf'))]:pdfmetrics.registerFont(TTFont(name,path))
pdfmetrics.registerFont(TTFont('Math',str(root/'fonts/NotoSansMath-Regular.ttf')))
def rich(s,font='Body'):
 out=[]
 for c in s:
  if c in '\n\t':out.append(c);continue
  name=font if ord(c) in pdfmetrics.getFont(font).face.charWidths else 'Math'
  if ord(c) not in pdfmetrics.getFont(name).face.charWidths:raise ValueError(('missing glyph',c,ord(c)))
  out.append(html.escape(c) if name==font else '<font name="Math">'+html.escape(c)+'</font>')
 return ''.join(out)
body=ParagraphStyle('body',fontName='Body',fontSize=10.1,leading=14,spaceAfter=8)
heading=ParagraphStyle('heading',fontName='Bold',fontSize=13,leading=17,spaceBefore=4,spaceAfter=12,textColor=colors.HexColor('#19384b'))
title=ParagraphStyle('title',parent=heading,fontSize=19,leading=24,spaceAfter=17)
code=ParagraphStyle('code',fontName='Mono',fontSize=8.5,leading=12,spaceAfter=8,leftIndent=10)
cell=ParagraphStyle('cell',fontName='Body',fontSize=8,leading=10.5)
story=[]
for j,page in enumerate((root/'paper.md').read_text().split('---PAGE---')):
 if j:story.append(PageBreak())
 blocks=re.split(r'\n\s*\n',page.strip())
 for block in blocks:
  if block.startswith('[TABLE]'):
   lines=block.splitlines()[1:-1];rows=[[Paragraph(rich(c.strip()),cell) for c in line.split('|')] for line in lines]
   widths=([25,25,100,100,210] if len(rows[0])==5 else [210,250])
   table=Table(rows,colWidths=widths,hAlign='LEFT');table.setStyle(TableStyle([('BACKGROUND',(0,0),(-1,0),colors.HexColor('#e7edf1')),('VALIGN',(0,0),(-1,-1),'TOP'),('LINEBELOW',(0,0),(-1,0),.5,colors.HexColor('#617687')),('BOTTOMPADDING',(0,0),(-1,-1),6),('TOPPADDING',(0,0),(-1,-1),6)]));story.extend([table,Spacer(1,10)])
  elif block.startswith('# '):story.append(Paragraph(rich(block[2:],'Bold'),title))
  elif block.startswith('## '):story.append(Paragraph(rich(block[3:],'Bold'),heading))
  elif block.startswith('    '):
   for line in block.splitlines():story.append(Paragraph(rich(line.strip(),'Mono'),code))
  else:story.append(Paragraph(rich(block).replace('\n',' '),body))
def footer(c,d):
 c.setFont('Body',8);c.setFillColor(colors.HexColor('#617687'));c.drawString(67,32,'DRAFT · MathDB 342364 · AI-assisted · Zero accepted credit');c.drawRightString(545,32,str(d.page))
doc=SimpleDocTemplate(str(root/'paper.pdf'),pagesize=(612,792),rightMargin=67,leftMargin=67,topMargin=47,bottomMargin=49,title='Valuation differences for coloured binary partitions',author='AI-assisted draft for root review')
doc.build(story,onFirstPage=footer,onLaterPages=footer)
print('Rendered paper.pdf')
