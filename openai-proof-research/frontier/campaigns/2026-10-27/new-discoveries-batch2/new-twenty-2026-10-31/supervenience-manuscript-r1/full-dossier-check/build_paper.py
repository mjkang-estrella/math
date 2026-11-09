from pathlib import Path
import sys,html
D=Path(__file__).resolve().parent
sys.path.insert(0,str(D/'local-deps'))
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,PageBreak,Table,TableStyle,KeepTogether
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib import colors
for n,f in [('Serif','/usr/share/fonts/liberation-serif-fonts/LiberationSerif-Regular.ttf'),('Bold','/usr/share/fonts/liberation-serif-fonts/LiberationSerif-Bold.ttf'),('Sans','/usr/share/fonts/liberation-sans-fonts/LiberationSans-Regular.ttf'),('Mono','/usr/share/fonts/liberation-mono-fonts/LiberationMono-Regular.ttf'),('Unicode','/usr/share/fonts/google-noto-vf/NotoSans[wght].ttf'),('Math','/usr/share/fonts/google-noto/NotoSansMath-Regular.ttf'),('Symbols','/usr/share/fonts/google-noto/NotoSansSymbols2-Regular.ttf')]:
 pdfmetrics.registerFont(TTFont(n,f))
def esc(text):
 out=''
 for c in text:
  if ord(c)<128 or ord(c) in pdfmetrics.getFont('Serif').face.charToGlyph:
   out+=html.escape(c)
  else:
   n=next((n for n in ['Unicode','Math','Symbols'] if ord(c) in pdfmetrics.getFont(n).face.charToGlyph),None)
   if n is None: raise ValueError('Missing glyph '+repr(c))
   out+='<font name="'+n+'">'+html.escape(c)+'</font>'
 return out
s=ParagraphStyle('body',fontName='Serif',fontSize=9.5,leading=13.6,spaceAfter=7)
h=ParagraphStyle('heading',fontName='Bold',fontSize=12,leading=16,spaceBefore=7,spaceAfter=9)
title=ParagraphStyle('title',fontName='Bold',fontSize=19,leading=24,spaceAfter=12)
eq=ParagraphStyle('eq',fontName='Sans',fontSize=9.2,leading=13,spaceAfter=2,leftIndent=12)
small=ParagraphStyle('small',fontName='Sans',fontSize=8.1,leading=11,spaceAfter=3)
story=[]
for page in (D/'paper.md').read_text().split('<!-- PAGE -->'):
 if story:story.append(PageBreak())
 blocks=page.strip().split('\n\n')
 for b in blocks:
  if b.startswith('|'):
   rows=[[Paragraph(esc(c.strip()),small) for c in line.strip('|').split('|')] for line in b.splitlines()]
   t=Table(rows,colWidths=[245,245],hAlign='LEFT')
   t.setStyle(TableStyle([('VALIGN',(0,0),(-1,-1),'TOP'),('BACKGROUND',(0,0),(-1,0),colors.HexColor('#eaf0f5')),('LINEBELOW',(0,0),(-1,0),.6,colors.grey),('BOTTOMPADDING',(0,0),(-1,-1),4)]))
   story.extend([t,Spacer(1,9)])
  elif b.startswith('@'):
   for line in b.splitlines():story.append(Paragraph(esc(line.removeprefix('@ ')),eq))
   story.append(Spacer(1,6))
  else:
   for line in b.splitlines():
    sty=eq if line.startswith('@ ') else title if line.startswith('# ') else h if line.startswith('##') else s
    story.append(Paragraph(esc(line.removeprefix('@ ').lstrip('# ')),sty))
def footer(c,d):
 c.setFont('Sans',8);c.setFillColor(colors.HexColor('#526172'))
 c.drawString(52,27,'DRAFT · MathDB 334599 · zero accepted credit')
 c.drawRightString(560,27,str(d.page))
out=D/'output/pdf/supervenience-draft.pdf';out.parent.mkdir(parents=True,exist_ok=True)
SimpleDocTemplate(str(out),pagesize=(612,792),leftMargin=52,rightMargin=52,topMargin=39,bottomMargin=47,title='Binary supervenience from unary supervenience on arbitrary ternary frames',author='AI-assisted research draft').build(story,onFirstPage=footer,onLaterPages=footer)
print(out)
