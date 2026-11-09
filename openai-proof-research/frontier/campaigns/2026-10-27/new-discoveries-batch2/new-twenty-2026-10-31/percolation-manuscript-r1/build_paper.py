from pathlib import Path
import sys,re,json
sys.path.insert(0,str(Path(sys.argv[1]).resolve()/"pdf-deps"))
from xml.sax.saxutils import escape
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,Table,TableStyle,PageBreak
from reportlab.lib.styles import getSampleStyleSheet,ParagraphStyle
from reportlab.lib import colors
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
D=Path(sys.argv[1]).resolve()
pdfmetrics.registerFont(TTFont('DejaVu',str(D/'fonts/DejaVuSans.ttf')))
pdfmetrics.registerFont(TTFont('DejaVuBold',str(D/'fonts/DejaVuSans-Bold.ttf')))
styles=getSampleStyleSheet();styles.add(ParagraphStyle(name='Body',fontName='DejaVu',fontSize=9.8,leading=14,spaceAfter=8));styles.add(ParagraphStyle(name='Head',fontName='DejaVuBold',fontSize=13,leading=17,spaceAfter=11));styles.add(ParagraphStyle(name='Title2',fontName='DejaVuBold',fontSize=20,leading=25,spaceAfter=14));styles.add(ParagraphStyle(name='Cell2',fontName='DejaVu',fontSize=8.3,leading=11))
def para(s,style='Body'):
 s=escape(s).replace('&lt;br/&gt;','<br/>');s=re.sub(r'\*\*(.*?)\*\*',r'<b>\1</b>',s);return Paragraph(s,styles[style])
story=[];pages=(D/'paper.md').read_text().split('---PAGE---')
for ix,page in enumerate(pages):
 if ix:story.append(PageBreak())
 blocks=page.strip().split('\n\n')
 for block in blocks:
  if block.startswith('|'):
   rows=[[para(c.strip(),'Cell2') for c in line.strip().strip('|').split('|')] for line in block.splitlines()]
   widths=([24,24,105,53,178,36] if len(rows[0])==6 else [290,130])
   t=Table(rows,colWidths=widths,hAlign='LEFT');t.setStyle(TableStyle([('BACKGROUND',(0,0),(-1,0),colors.HexColor('#e6edf5')),('VALIGN',(0,0),(-1,-1),'TOP'),('LINEBELOW',(0,0),(-1,0),.6,colors.HexColor('#60748a')),('BOTTOMPADDING',(0,0),(-1,-1),5),('TOPPADDING',(0,0),(-1,-1),5)]));story.extend([t,Spacer(1,10)])
  elif block.startswith('# '):story.append(para(block[2:],'Title2'))
  elif block.startswith('## '):story.append(para(block[3:],'Head'))
  else:story.append(para(block.replace('\n','<br/>') if block.startswith('•') else block.replace('\n',' ')))
def foot(c,d):
 c.setFont('DejaVu',8);c.setFillColor(colors.HexColor('#60748a'));c.drawString(54,30,'DRAFT · AI-assisted · MathDB 333709');c.drawRightString(558,30,str(d.page))
doc=SimpleDocTemplate(str(D/'paper.pdf'),pagesize=(612,792),rightMargin=54,leftMargin=54,topMargin=46,bottomMargin=48,title='No two-round minimal line-percolating set in PG(2,5)',author='AI-assisted draft; no human authorship asserted')
doc.build(story,onFirstPage=foot,onLaterPages=foot)
print('PDF built')
