from pathlib import Path
import sys,json
D=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(D/'outputs/python-libs'))
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,PageBreak,Table,TableStyle,KeepTogether
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib import colors
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
F=Path('/usr/share/fonts/liberation-serif-fonts')
for name,file in [('Serif','Regular'),('Serif-Bold','Bold'),('Serif-Italic','Italic')]:pdfmetrics.registerFont(TTFont(name,str(F/f'LiberationSerif-{file}.ttf')))
pdfmetrics.registerFontFamily('Serif',normal='Serif',bold='Serif-Bold',italic='Serif-Italic',boldItalic='Serif-Bold')
styles={
 'body':ParagraphStyle('body',fontName='Serif',fontSize=10.2,leading=12.8,spaceAfter=6),
 'small':ParagraphStyle('small',fontName='Serif',fontSize=9.0,leading=10.8,spaceAfter=3),
 'h':ParagraphStyle('h',fontName='Serif-Bold',fontSize=12,leading=15,spaceBefore=8,spaceAfter=7),
 'title':ParagraphStyle('title',fontName='Serif-Bold',fontSize=18,leading=21,spaceAfter=13),
 'eq':ParagraphStyle('eq',fontName='Serif',fontSize=10.6,leading=14,alignment=1,spaceAfter=9,spaceBefore=3)}
def P(t,style='body'):return Paragraph(t.replace('&','&amp;').replace('<','&lt;').replace('>','&gt;'),styles[style])
tables={
'experiment':[['Order','Connected graphs','MP failures','Spectral failures'],['5','21','2','0'],['6','112','10','0'],['7','853','56','0'],['8','11,117','545','0'],['Total','12,103','613','0']],
'values':[['Reading','α = −1','α = 0','α = 1'],['MP pair sum','21930927/278132','370/3','515538204/7137235'],['Spectral trace','1096887/11036','370/3','1696684/14035']],
'formal':[['Object','Lean declaration and scope'],['Real MP refutation','KirchhoffReal.refuteMP: negates LiteralConjecture Penrose pairIndex.'],['Real spectral refutation','KirchhoffReal.refuteSpec: negates LiteralConjecture GroupInverse spectralIndex.'],['Quantifiers','LiteralConjecture: every n ≥ 2, connected graph, and α = ±1; existential inverse data, ordering, and regularity iff equality.'],['Inverse equations','Penrose: AXA=A, XAX=X, (AX)ᵀ=AX, (XA)ᵀ=XA. GroupInverse: AXA=A, XAX=X, AX=XA.'],['Laplacian','Kirchhoff.laplacian; laplacian_source_formula identifies (3.8).'],['MP index','pairIndex: sum of Xᵢᵢ + Xⱼⱼ − Xᵢⱼ − Xⱼᵢ over i < j.'],['Spectral index','spectralIndex: n tr(X); ordinary eigenvalue bridge in Section 3.']]}
story=[]; pages=json.loads((D/'paper/manuscript.json').read_text())
for k,page in enumerate(pages):
 if k:story.append(PageBreak())
 story.append(P(page['title'],'title'))
 if page.get('subtitle'):story.append(P(page['subtitle'],'small'))
 for sec in page['sections']:
  story.append(P(sec[0],'h'))
  for t in sec[1:]:
   if t.startswith('EQ:'):story.append(P(t[3:],'eq'))
   elif t.startswith('TABLE:'):
    name=t[6:];rows=tables[name]; widths=[125,343] if name=='formal' else [115,118,100,135]
    tab=Table([[P(c,'small') for c in r] for r in rows],colWidths=widths,hAlign='CENTER')
    tab.setStyle(TableStyle([('BACKGROUND',(0,0),(-1,0),colors.HexColor('#e9edf0')),('VALIGN',(0,0),(-1,-1),'TOP'),('LINEBELOW',(0,0),(-1,0),.6,colors.gray),('BOTTOMPADDING',(0,0),(-1,-1),3),('TOPPADDING',(0,0),(-1,-1),3)]))
    story.extend([tab,Spacer(1,8)])
   else:story.append(P(t,'small' if sec[0]=='References and evidence' else 'body'))
def footer(c,d):
 c.setFont('Serif',8);c.setFillColor(colors.gray);c.drawString(63,30,'DRAFT · AI-assisted · MathDB 349441 · No priority claim');c.drawRightString(531,30,str(d.page))
doc=SimpleDocTemplate(str(D/'paper/kirchhoff-draft.pdf'),pagesize=(594,842),leftMargin=63,rightMargin=63,topMargin=45,bottomMargin=49,title=pages[0]['title'],author='AI-assisted project draft; no human authors asserted')
doc.build(story,onFirstPage=footer,onLaterPages=footer)
print('Rendered',D/'paper/kirchhoff-draft.pdf')
