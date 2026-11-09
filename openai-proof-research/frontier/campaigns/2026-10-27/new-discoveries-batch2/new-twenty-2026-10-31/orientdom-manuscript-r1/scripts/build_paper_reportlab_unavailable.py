from pathlib import Path
import json,html,re
from reportlab.pdfgen import canvas
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,PageBreak,Table,TableStyle
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib import colors
R=Path.cwd()
for n,f in [('Serif','LiberationSerif-Regular.ttf'),('SerifB','LiberationSerif-Bold.ttf'),('SerifI','LiberationSerif-Italic.ttf'),('SerifBI','LiberationSerif-BoldItalic.ttf')]:
 pdfmetrics.registerFont(TTFont(n,'/usr/share/fonts/liberation-serif-fonts/'+f))
pdfmetrics.registerFontFamily('Serif',normal='Serif',bold='SerifB',italic='SerifI',boldItalic='SerifBI')
body=ParagraphStyle('body',fontName='Serif',fontSize=10.5,leading=13.3,spaceAfter=7)
small=ParagraphStyle('small',parent=body,fontSize=9.1,leading=11,spaceAfter=5)
h=ParagraphStyle('heading',parent=body,fontName='SerifB',fontSize=13,leading=16,spaceAfter=12)
title=ParagraphStyle('title',parent=h,fontSize=20,leading=23,spaceAfter=14)
q=ParagraphStyle('quote',parent=small,leftIndent=8,borderColor=colors.HexColor('#b5bbc4'),borderWidth=.4,borderPadding=5,spaceAfter=8)
source=(R/'paper.md').read_text(); pages=source.split('---PAGE---'); flow=[]
qual=json.loads((R/'inputs/orientdom-root-ruling-r2.json').read_text())['gate_D_ruling']
data=json.loads((R/'recomputed/verification.json').read_text())
for pi,page in enumerate(pages):
 for block in page.strip().split('\n\n'):
  if block=='[[ROOT_QUALIFICATIONS]]':
   for s in qual: flow.append(Paragraph(html.escape(s),q))
  elif block=='[[ENUM_TABLE]]':
   rows=[['Order','Admissible graphs','Valid orientations','Gaps']]+[[str(d['n']),f"{d['graphs']:,}",f"{d['orientations']:,}",str(d['gaps'])] for d in data['orders']]
   t=Table(rows,colWidths=[60,145,145,55]); t.setStyle(TableStyle([('FONTNAME',(0,0),(-1,-1),'Serif'),('FONTSIZE',(0,0),(-1,-1),10),('BACKGROUND',(0,0),(-1,0),colors.HexColor('#eef1f5')),('LINEBELOW',(0,0),(-1,0),.5,colors.grey),('TOPPADDING',(0,0),(-1,-1),5),('BOTTOMPADDING',(0,0),(-1,-1),5)])); flow+=[t,Spacer(1,10)]
  elif block=='[[FORMAL_TABLE]]':
   meanings=[('Rel / Arc','Boolean adjacency / equality to true.'),('Valid','Every vertex has an incoming arc.'),('Asym','No opposite arcs; in particular no loops.'),('Same','Identical underlying undirected support.'),('OrientationOf G D','Asym D and support exactly G.'),('TD D S','Every vertex has an in-neighbour in S.'),('Minimum D S','TD D S and |S| ≤ |T| for every TD set T.'),('spectrum G','Attained minimum sizes, restricted to 0,…,|V|.'),('lower / upper','Actual min′ and max′ of nonempty spectrum.'),('Conjecture','All intermediate sizes belong to spectrum.'),('conjecture_true','A proof of this literal Conjecture.')]
   t=Table([[Paragraph('<b>'+a+'</b>',small),Paragraph(b,small)] for a,b in meanings],colWidths=[130,374]); t.setStyle(TableStyle([('VALIGN',(0,0),(-1,-1),'TOP'),('ROWBACKGROUNDS',(0,0),(-1,-1),[colors.white,colors.HexColor('#f3f4f6')]),('BOTTOMPADDING',(0,0),(-1,-1),3)])); flow+=[t,Spacer(1,9)]
  else:
   style=small if pi==4 else body
   if block.startswith('# '): block=block[2:]; style=title
   elif block.startswith('## '): block=block[3:]; style=h
   flow.append(Paragraph(block,style))
 if pi<len(pages)-1: flow.append(PageBreak())
def footer(c,doc):
 c.setStrokeColor(colors.HexColor('#b5bbc4')); c.line(54,40,558,40)
 c.setFont('Serif',8); c.drawString(54,27,'DRAFT · AI-assisted · Orientable total domination'); c.drawRightString(558,27,str(doc.page))
doc=SimpleDocTemplate(str(R/'paper.pdf'),pagesize=(612,792),rightMargin=54,leftMargin=54,topMargin=45,bottomMargin=53,title='Interpolation of orientable total domination by safe arc reversals',author='AI-assisted research draft; no human author asserted')
doc.build(flow,onFirstPage=footer,onLaterPages=footer)
print('Built paper.pdf')
