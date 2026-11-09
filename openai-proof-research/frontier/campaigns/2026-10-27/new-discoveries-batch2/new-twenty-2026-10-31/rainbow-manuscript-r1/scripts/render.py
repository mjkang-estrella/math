from pathlib import Path
import html,re
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,PageBreak,Table,TableStyle
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib import colors
P=Path(__file__).resolve().parents[1]
for n,f in [('Body','LiberationSerif-Regular.ttf'),('Bold','LiberationSerif-Bold.ttf')]:pdfmetrics.registerFont(TTFont(n,str(P/'assets/fonts'/f)))
styles={ 'p':ParagraphStyle('p',fontName='Body',fontSize=9.4,leading=13.3,spaceAfter=8), 'h1':ParagraphStyle('h1',fontName='Bold',fontSize=17,leading=21,spaceAfter=14), 'h2':ParagraphStyle('h2',fontName='Bold',fontSize=11.5,leading=15,spaceBefore=6,spaceAfter=10),'t':ParagraphStyle('t',fontName='Body',fontSize=8.4,leading=11)}
pdfmetrics.registerFont(TTFont('Symbols',str(P/'assets/fonts/Symbola.ttf')))
def esc(s):
 return ''.join(html.escape(c) if ord(c) in pdfmetrics.getFont('Body').face.charToGlyph else '<font name="Symbols">'+html.escape(c)+'</font>' for c in s)
s=(P/'manuscript.md').read_text();story=[]
for page in s.split('<!-- pagebreak -->'):
 if story:story.append(PageBreak())
 chunks=re.split(r'\n\s*\n',page.strip())
 for chunk in chunks:
  if chunk.startswith('|'):
   rows=[[Paragraph(esc(c.strip()),styles['t']) for c in line.strip().strip('|').split('|')] for line in chunk.splitlines() if line.startswith('|') and not re.match(r'^\|[- :|]+$',line)]
   t=Table(rows,hAlign='LEFT',repeatRows=1)
   t.setStyle(TableStyle([('BACKGROUND',(0,0),(-1,0),colors.HexColor('#e8edf1')),('LINEBELOW',(0,0),(-1,0),.6,colors.grey),('VALIGN',(0,0),(-1,-1),'TOP'),('LEFTPADDING',(0,0),(-1,-1),7),('RIGHTPADDING',(0,0),(-1,-1),7),('TOPPADDING',(0,0),(-1,-1),3),('BOTTOMPADDING',(0,0),(-1,-1),3)]));story.extend([t,Spacer(1,9)])
  else:
   key='h1' if chunk.startswith('# ') else 'h2' if chunk.startswith('## ') else 'p'
   story.append(Paragraph(esc(re.sub(r'^#+ ','',chunk).replace('\n',' ')),styles[key]))
def footer(c,doc):
 c.setFont('Body',8);c.setFillColor(colors.grey);c.drawString(44,25,'DRAFT • AI-assisted • MathDB 346167 • zero accepted credit');c.drawRightString(551,25,str(doc.page))
SimpleDocTemplate(str(P/'rainbow-counterexample-draft.pdf'),pagesize=(595.28,841.89),leftMargin=44,rightMargin=44,topMargin=38,bottomMargin=43,title='An eight-vertex counterexample to the rainbow vertex-disconnection sum conjecture',author='AI-assisted draft').build(story,onFirstPage=footer,onLaterPages=footer)
print('rendered')
