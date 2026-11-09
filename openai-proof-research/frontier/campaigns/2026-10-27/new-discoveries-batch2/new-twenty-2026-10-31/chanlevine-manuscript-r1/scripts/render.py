from pathlib import Path
import re,html,shutil,sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/"tmp/pdf-deps"))
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,PageBreak,Table,TableStyle,Preformatted
from reportlab.lib.styles import getSampleStyleSheet,ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib import colors
p=Path.cwd()
for name,file in [('Body','LiberationSerif-Regular.ttf'),('Bold','LiberationSerif-Bold.ttf'),('Mono','LiberationMono-Regular.ttf')]:
 f=p/'fonts'/file
 if not f.exists():f=next(Path('/usr/share/fonts').rglob(file))
 pdfmetrics.registerFont(TTFont(name,str(p/'fonts'/file)))
s=getSampleStyleSheet();s.add(ParagraphStyle(name='B',fontName='Body',fontSize=9.4,leading=13.2,spaceAfter=8));s.add(ParagraphStyle(name='H',fontName='Bold',fontSize=13,leading=16,spaceAfter=12));s.add(ParagraphStyle(name='T',fontName='Bold',fontSize=19,leading=23,spaceAfter=14));s.add(ParagraphStyle(name='Eq',fontName='Mono',fontSize=7.6,leading=11,spaceAfter=9))
story=[]
for pi,page in enumerate((p/'paper.md').read_text().split('---PAGE---')):
 if pi:story.append(PageBreak())
 for block in re.split(r'\n\s*\n',page.strip()):
  if block.startswith('|'):
   data=[[Paragraph(html.escape(c.strip()),s['B']) for c in row.strip().strip('|').split('|')] for row in block.splitlines()]
   widths=[35,35,426] if len(data[0])==3 else [160,336]
   t=Table(data,colWidths=widths,hAlign='LEFT');t.setStyle(TableStyle([('VALIGN',(0,0),(-1,-1),'TOP'),('BACKGROUND',(0,0),(-1,0),colors.HexColor('#edf1f4')),('LINEBELOW',(0,0),(-1,0),.5,colors.grey),('BOTTOMPADDING',(0,0),(-1,-1),3)]));story.append(t);story.append(Spacer(1,8))
  elif block.startswith('    '):story.append(Preformatted(block,s['Eq'],dedent=4))
  else:
   style='T' if block.startswith('# ') else 'H' if block.startswith('## ') else 'B'
   text=re.sub(r'^#{1,2} ','',block);story.append(Paragraph(html.escape(text).replace('\n',' '),s[style]))
def footer(c,d):
 c.setFont('Body',7);c.setFillColor(colors.grey);c.drawString(50,28,'DRAFT | AI-assisted | MathDB 338887 | root review pending');c.drawRightString(546,28,str(d.page))
doc=SimpleDocTemplate(str(p/'paper.pdf'),pagesize=(596,842),rightMargin=50,leftMargin=50,topMargin=46,bottomMargin=48,title='Gcd symmetry of recurrent-component sizes on a bidirected cycle',author='AI-assisted draft; no human authorship asserted')
doc.build(story,onFirstPage=footer,onLaterPages=footer)
print('Rendered paper.pdf')
