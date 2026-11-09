from pathlib import Path
import json,html
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,PageBreak,Table,TableStyle
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib import colors
W=Path(__file__).resolve().parent
body=ParagraphStyle('body',fontName='Times-Roman',fontSize=10.5,leading=13.1,spaceAfter=8)
small=ParagraphStyle('small',parent=body,fontSize=9,leading=11,spaceAfter=6)
head=ParagraphStyle('head',parent=body,fontName='Times-Bold',fontSize=14,leading=17,spaceAfter=12)
title=ParagraphStyle('title',parent=head,fontSize=19,leading=22)
def p(s,style=body):return Paragraph(html.escape(s),style)
def table(rows,widths):
 t=Table([[p(str(x),small) for x in row] for row in rows],colWidths=widths,hAlign='LEFT')
 t.setStyle(TableStyle([('VALIGN',(0,0),(-1,-1),'TOP'),('BACKGROUND',(0,0),(-1,0),colors.HexColor('#eaf0f5')),('LINEBELOW',(0,0),(-1,0),.5,colors.grey),('LEFTPADDING',(0,0),(-1,-1),6),('RIGHTPADDING',(0,0),(-1,-1),6),('BOTTOMPADDING',(0,0),(-1,-1),5)]));return t
story=[]
for i,page in enumerate(json.loads((W/'manuscript.json').read_text())):
 if i:story.append(PageBreak())
 if 'title' in page:story += [p(page['title'],title),p(page['subtitle'],small),Spacer(1,8)]
 story.append(p(page['heading'],head))
 story += [p(x) for x in page['paragraphs']]
 if page.get('table')=='classification':
  story += [table([['Mask m','Missing vertex'],['0, 1, 2, 4, 5, 6, 8, 9, 12','1, 3, 1, 1, 5, 7, 1, 6, 2'],['32, 33, 34, 40, 41','1, 4, 1, 1, -'],['64, 66, 68, 70, 96','2, 3, 2, -, 4']],[260,235]),Spacer(1,10)]
 if page.get('table')=='correspondence':
  rows=[['Declaration','Mathematical content'],['InducedPath R m f','Injective f on Fin (m+1); adjacency iff consecutive indices.'],['TripleMP R a b c','No induced path contains all three specified vertices.'],['MonophonicSet R S','Every distinct triple of S satisfies TripleMP.'],['mpNumber G','Maximum mp-set cardinality, as a finite supremum.'],['SourceClaim','For every n >= 11 there EXISTS J with diameter 2 and mp-number 2.'],['Bridge.represent (represent)','Every mathlib circulant at order 15 has one of the 128 masks.'],['radius_of_diam','diam = 2 implies every vertex is within two steps of zero.'],['order15','For every J, diam = 2 implies 3 <= mpNumber.'],['source_refutation','The literal negation of SourceClaim, using n = 15.']]
  story += [table(rows,[162,333]),Spacer(1,10)]
 story += [p(x) for x in page.get('after',[])]
 story += [p(x,small) for x in page.get('references',[])]
def footer(c,d):
 c.setFont('Times-Roman',9);c.setFillColor(colors.grey);c.drawString(50,29,'DRAFT | MathDB 350979 | AI-assisted');c.drawRightString(545,29,str(d.page))
doc=SimpleDocTemplate(str(W/'circulant-draft.pdf'),pagesize=(595.28,841.89),leftMargin=50,rightMargin=50,topMargin=42,bottomMargin=45)
doc.build(story,onFirstPage=footer,onLaterPages=footer)
