#!/usr/bin/env python3
"""Deterministic PDF renderer; paper.json is the editable manuscript source."""
from pathlib import Path
import json
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,PageBreak,Table,TableStyle,Preformatted
from reportlab.lib.styles import getSampleStyleSheet,ParagraphStyle
from reportlab.lib import colors
D=Path(__file__).resolve().parents[1]
styles=getSampleStyleSheet()
styles.add(ParagraphStyle(name='Text',fontName='Times-Roman',fontSize=11,leading=14,spaceAfter=9))
styles.add(ParagraphStyle(name='SmallText',fontName='Times-Roman',fontSize=9,leading=11,spaceAfter=5))
styles.add(ParagraphStyle(name='CodeText',fontName='Courier',fontSize=8,leading=11,spaceAfter=10))
story=[]
for i,page in enumerate(json.loads((D/'paper.json').read_text())):
 if i:story.append(PageBreak())
 for kind,body in page:
  if kind=='table':
   rows=[[Paragraph(str(v),styles['SmallText']) for v in row] for row in body]
   t=Table(rows,colWidths=[205,295],hAlign='LEFT');t.setStyle(TableStyle([('VALIGN',(0,0),(-1,-1),'TOP'),('BACKGROUND',(0,0),(-1,0),colors.HexColor('#e8eef3')),('LINEBELOW',(0,0),(-1,0),.6,colors.grey),('BOTTOMPADDING',(0,0),(-1,-1),6),('TOPPADDING',(0,0),(-1,-1),4)]));story.append(t)
  elif kind=='code':story.append(Preformatted(body,styles['CodeText']))
  else:story.append(Paragraph(body,styles[{'title':'Title','h':'Heading2','p':'Text','small':'SmallText'}[kind]]))
def footer(c,doc):
 c.setStrokeColor(colors.HexColor('#aab8c4'));c.line(48,42,564,42);c.setFont('Helvetica',8);c.drawString(48,29,'DRAFT | MathDB 364205 | 1 November 2026 | AI-assisted research artifact');c.drawRightString(564,29,str(doc.page))
SimpleDocTemplate(str(D/'draft.pdf'),pagesize=(612,792),rightMargin=56,leftMargin=56,topMargin=48,bottomMargin=58,title='A 34-vertex maximal rigid diameter-5 subset of the eight-dimensional Hamming cube',author='AI-assisted research draft; no human author asserted').build(story,onFirstPage=footer,onLaterPages=footer)
print('PDF built')
