"""Build the five-page draft from paper-source.json using ReportLab."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent/"tools/vendor"))
import json,html
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, PageBreak
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib import colors
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
ROOT=Path(__file__).resolve().parent
pdfmetrics.registerFont(TTFont('DejaVu','/usr/share/fonts/liberation-sans-fonts/LiberationSans-Regular.ttf'))
pdfmetrics.registerFont(TTFont('DejaVuBold','/usr/share/fonts/liberation-sans-fonts/LiberationSans-Bold.ttf'))
s=getSampleStyleSheet()
s.add(ParagraphStyle(name='BodyCustom',fontName='DejaVu',fontSize=9.3,leading=13,spaceAfter=8))
s.add(ParagraphStyle(name='TitleCustom',fontName='DejaVuBold',fontSize=17,leading=22,spaceAfter=14,textColor=colors.HexColor('#19334c')))
s.add(ParagraphStyle(name='HeadCustom',fontName='DejaVuBold',fontSize=10,leading=14,spaceBefore=6,spaceAfter=6))
s.add(ParagraphStyle(name='CellCustom',fontName='DejaVu',fontSize=8.1,leading=11))
def para(t,style='BodyCustom'): return Paragraph(html.escape(t),s[style])
story=[]
for idx,page in enumerate(json.loads((ROOT/'paper-source.json').read_text())):
 if idx: story.append(PageBreak())
 story.append(para(page['title'],'TitleCustom'))
 if page.get('subtitle'): story.append(para(page['subtitle'],'HeadCustom'))
 for heading,text in page['sections']:
  if heading=='TABLE':
   data=[[para(c,'CellCustom') for c in row] for row in text]
   widths=[124,110,110,110] if len(text[0])==4 else [170,284]
   t=Table(data,colWidths=widths,hAlign='LEFT',repeatRows=1)
   t.setStyle(TableStyle([('BACKGROUND',(0,0),(-1,0),colors.HexColor('#e5edf4')),('GRID',(0,0),(-1,-1),.35,colors.HexColor('#b0bfcc')),('VALIGN',(0,0),(-1,-1),'TOP'),('LEFTPADDING',(0,0),(-1,-1),7),('RIGHTPADDING',(0,0),(-1,-1),7),('TOPPADDING',(0,0),(-1,-1),5),('BOTTOMPADDING',(0,0),(-1,-1),5)]))
   story.extend([t,Spacer(1,10)])
  else:
   if heading: story.append(para(heading,'HeadCustom'))
   story.append(para(text))
def footer(c,d):
 c.setFont('DejaVu',8);c.setFillColor(colors.HexColor('#526273'))
 c.drawString(54,30,'DRAFT • AI-assisted • MathDB 381805 • No priority claim')
 c.drawRightString(558,30,str(d.page))
doc=SimpleDocTemplate(str(ROOT/'paper.pdf'),pagesize=(612,792),leftMargin=54,rightMargin=54,topMargin=42,bottomMargin=48,title='Exact super edge-magic total strength of a seven-cycle with four leaves at one vertex',author='AI-assisted draft; no human authorship asserted')
doc.build(story,onFirstPage=footer,onLaterPages=footer)
# An editable, readable source companion contains all mathematical prose and table data.
parts=[]
for page in json.loads((ROOT/'paper-source.json').read_text()):
 parts.append('# '+page['title'])
 for h,t in page['sections']:
  if h=='TABLE': parts.append('\n'.join(' | '.join(row) for row in t))
  else: parts.append(('## '+h+'\n' if h else '')+t)
(ROOT/'PROOF.md').write_text('DRAFT. Ordinary proof and formal correspondence; zero accepted credit.\n\n'+'\n\n'.join(parts)+'\n')
