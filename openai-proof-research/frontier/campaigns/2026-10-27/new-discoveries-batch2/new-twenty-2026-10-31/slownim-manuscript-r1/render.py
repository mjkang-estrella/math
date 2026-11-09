from pathlib import Path
import re,html,json
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,PageBreak,Table,TableStyle
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib.enums import TA_CENTER
L=Path(__file__).resolve().parent
pdfmetrics.registerFont(TTFont('Serif','/usr/share/fonts/liberation-serif-fonts/LiberationSerif-Regular.ttf'))
pdfmetrics.registerFont(TTFont('Bold','/usr/share/fonts/liberation-serif-fonts/LiberationSerif-Bold.ttf'))
pdfmetrics.registerFont(TTFont('Math','/usr/share/fonts/google-noto/NotoSansMath-Regular.ttf'))
regular=pdfmetrics.getFont('Serif').face.charWidths;math=pdfmetrics.getFont('Math').face.charWidths
missing=set()
def esc(s):
 result=''
 for c in s:
  sub=dict(zip('₀₁₂₃₄₅₆₇₈₉ᵢⱼₙₗ₋₊₌','0123456789ijnl-+='))
  if c in sub:
   result+='<sub>'+sub[c]+'</sub>';continue
  if c=='⁰':result+='<super>0</super>';continue
  v=html.escape(c)
  if ord(c) not in regular:
   if ord(c) not in math:missing.add(c)
   v='<font name="Math">'+v+'</font>'
  result+=v
 return result
styles={
 'body':ParagraphStyle('body',fontName='Serif',fontSize=10.8,leading=13.7,spaceAfter=8),
 'heading':ParagraphStyle('heading',fontName='Bold',fontSize=13,leading=16,spaceBefore=3,spaceAfter=11),
 'title':ParagraphStyle('title',fontName='Bold',fontSize=19,leading=22,spaceAfter=12),
 'reference':ParagraphStyle('reference',fontName='Serif',fontSize=10,leading=12.2,spaceAfter=5),
}
story=[];references=False
for block in (L/'manuscript.md').read_text().split('\n\n'):
 block=block.strip()
 if not block:continue
 if block=='---PAGE---':story.append(PageBreak());continue
 if block.startswith('n | l | B |'):
  rows=[[cell.strip() for cell in line.split('|')] for line in block.splitlines()]
  table=Table(rows,colWidths=[40,40,40,165,165],hAlign='LEFT')
  table.setStyle(TableStyle([('FONTNAME',(0,0),(-1,-1),'Serif'),('FONTSIZE',(0,0),(-1,-1),10.5),('FONTNAME',(0,0),(-1,0),'Bold'),('LINEBELOW',(0,0),(-1,0),.4,(.3,.3,.3)),('BOTTOMPADDING',(0,0),(-1,-1),5),('TOPPADDING',(0,0),(-1,-1),5)]))
  story.extend([table,Spacer(1,9)]);continue
 style='title' if block.startswith('# ') else 'heading' if block.startswith('## ') else 'body'
 if block=='## References':references=True
 if references and style=='body':style='reference'
 block=re.sub(r'^#{1,2} ','',block)
 story.append(Paragraph(esc(block),styles[style]))
def footer(c,d):
 c.setFont('Serif',8.5);c.setFillColorRGB(.35,.35,.35)
 c.drawString(48,27,'DRAFT • AI-assisted • MathDB 360653 / duplicate 361128')
 c.drawRightString(564,27,str(d.page))
doc=SimpleDocTemplate(str(L/'manuscript.pdf'),invariant=1,pagesize=(612,792),rightMargin=48,leftMargin=48,topMargin=42,bottomMargin=45,title='A unilateral deviation from GM play in multiplayer exact slow NIM',author='AI-assisted draft; no human authors asserted')
assert not missing,missing
doc.build(story,onFirstPage=footer,onLaterPages=footer)
(L/'logs/font-audit.json').write_text(json.dumps(dict(missing_glyphs=sorted(missing)))+'\n')
print('Rendered manuscript.pdf')
