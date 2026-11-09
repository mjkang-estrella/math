from pathlib import Path
import json,re,html
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,PageBreak,Table,TableStyle
from reportlab.lib.styles import getSampleStyleSheet,ParagraphStyle
from reportlab.lib import colors
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
D=Path(__file__).resolve().parents[1];r=json.loads((D/'recomputed.json').read_text())
for name,file in [('Serif','LiberationSerif-Regular.ttf'),('SerifBold','LiberationSerif-Bold.ttf'),('Sans','LiberationSerif-Regular.ttf')]:pdfmetrics.registerFont(TTFont(name,'/usr/share/fonts/liberation-serif-fonts/'+file))
pdfmetrics.registerFont(TTFont('Math','/usr/share/fonts/google-noto/NotoSansMath-Regular.ttf'))
s=getSampleStyleSheet();s.add(ParagraphStyle(name='Body',fontName='Serif',fontSize=10,leading=13,spaceAfter=8));s.add(ParagraphStyle(name='Head',fontName='SerifBold',fontSize=12,leading=15,spaceBefore=5,spaceAfter=10));s.add(ParagraphStyle(name='PaperTitle',fontName='SerifBold',fontSize=17,leading=21,spaceAfter=12));s.add(ParagraphStyle(name='Quote',parent=s['Body'],leftIndent=14,fontSize=9,leading=12));s.add(ParagraphStyle(name='Small',fontName='Sans',fontSize=8,leading=10))
story=[]
def table(data,widths):
 t=Table(data,colWidths=widths,hAlign='CENTER');t.setStyle(TableStyle([('FONTNAME',(0,0),(-1,-1),'Sans'),('FONTSIZE',(0,0),(-1,-1),8.5),('LEADING',(0,0),(-1,-1),11),('TOPPADDING',(0,0),(-1,-1),5),('BOTTOMPADDING',(0,0),(-1,-1),5),('BACKGROUND',(0,0),(-1,0),colors.HexColor('#e3e9ee')),('LINEBELOW',(0,0),(-1,0),.6,colors.HexColor('#536675')),('ROWBACKGROUNDS',(0,1),(-1,-1),[colors.whitesmoke,colors.white]),('VALIGN',(0,0),(-1,-1),'MIDDLE')]));return t
def red(p):return ''.join(str(sorted(p).index(x)+1) for x in p)
for page in (D/'manuscript.md').read_text().split('===PAGE==='):
 if story:story.append(PageBreak())
 for block in re.sub(r'(?m)^(#{1,2} [^\n]+)\n(?!\n)', r'\1\n\n',page.strip()).split('\n\n'):
  if block=='[[TOUR_TABLE]]':
   rows=[['i','Edge','Prefix','Suffix','i','Edge','Prefix','Suffix']]
   for i in range(12):
    row=[]
    for j in [i,i+12]:
     p=r['witness'][j];row += [str(j),p,red(p[:-1]),red(p[1:])]
    rows.append(row)
   story += [table(rows,[26,59,49,49]*2),Spacer(1,9)]
  elif block=='[[FORCING_TABLE]]':
   rows=[['Window','Type','Offsets','Ranks','Forced inequality']]
   for x in r['forcing_table']:
    a,b=x['offsets'];u,v=x['positions'];c,d=x['ranks'];rows.append([str(x['window']),x['permutation'],f'{a}, {b}',f'{c} < {d}',f'x{u} < x{v}'])
   story += [table(rows,[52,65,65,65,119]),Spacer(1,9)]
  else:
   style='Body'
   if block.startswith('# '):style='PaperTitle';block=block[2:]
   elif block.startswith('## '):style='Head';block=block[3:]
   elif block.startswith('> '):style='Quote';block=block[2:]
   block=''.join(html.escape(ch) if ord(ch) in pdfmetrics.getFont(s[style].fontName).face.charToGlyph else '<font name="Math">'+html.escape(ch)+'</font>' for ch in block.replace('□','QED'))
   story.append(Paragraph(block.replace('\n','<br/>'),s[style]))
def footer(c,doc):
 c.setStrokeColor(colors.HexColor('#9aa6b0'));c.line(54,43,558,43);c.setFont('Sans',7);c.drawString(54,31,'DRAFT • AI-assisted • MathDB 356266 • root review pending');c.drawRightString(558,31,str(doc.page))
SimpleDocTemplate(str(D/'manuscript.pdf'),pagesize=(612,792),rightMargin=54,leftMargin=54,topMargin=44,bottomMargin=57,title='An Euler tour of the full permutation overlap graph that no cyclic word realizes',author='AI-assisted draft; no human author asserted').build(story,onFirstPage=footer,onLaterPages=footer)
print('Rendered manuscript.pdf')
