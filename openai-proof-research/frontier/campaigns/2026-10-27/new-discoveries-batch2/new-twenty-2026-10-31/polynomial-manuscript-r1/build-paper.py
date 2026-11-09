from pathlib import Path
import json,io
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,Image,PageBreak,KeepTogether
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib.colors import HexColor
from matplotlib.mathtext import math_to_image
from matplotlib import get_data_path
from PIL import Image as PILImage
R=Path(__file__).resolve().parent
for name,file in [('Body','DejaVuSerif.ttf'),('Bold','DejaVuSerif-Bold.ttf'),('Sans','DejaVuSans.ttf'),('Mono','DejaVuSansMono.ttf')]:
 folder='dejavu'; pdfmetrics.registerFont(TTFont(name,str(Path(get_data_path())/'fonts/ttf'/file)))
styles={'p':ParagraphStyle('p',fontName='Body',fontSize=9.5,leading=14,spaceAfter=9), 'h':ParagraphStyle('h',fontName='Bold',fontSize=11.5,leading=16,spaceBefore=8,spaceAfter=8), 'title':ParagraphStyle('t',fontName='Bold',fontSize=18,leading=24,spaceAfter=15),'sub':ParagraphStyle('s',fontName='Sans',fontSize=11,leading=16,spaceAfter=18), 'code':ParagraphStyle('c',fontName='Mono',fontSize=9,leading=13,spaceAfter=12)}
flow=[]
for k,page in enumerate(json.loads((R/'paper-source.json').read_text())):
 if k: flow.append(PageBreak())
 flow.append(Paragraph(page['title'],styles['title']))
 if 'subtitle' in page:flow.append(Paragraph(page['subtitle'],styles['sub']))
 for kind,s in page['blocks']:
  if kind=='eq':
   f=io.BytesIO(); math_to_image('$'+s+'$',f,dpi=240,format='png'); f.seek(0); im=PILImage.open(f); w,h=im.size; scale=min(0.30,465/w); flow += [Image(f,width=w*scale,height=h*scale),Spacer(1,12)]
  else:flow.append(Paragraph(s.replace('&','&amp;').replace(' <= ',' &lt;= ').replace(' -> ',' -&gt; ').replace('\n','<br/>'),styles[kind]))
def footer(c,d):
 c.setStrokeColor(HexColor('#b8c3cb')); c.line(58,43,537,43);c.setFont('Sans',8);c.setFillColor(HexColor('#455461'));c.drawString(58,30,'MathDB 347913 | Draft | Novelty and root acceptance pending');c.drawRightString(537,30,str(d.page))
SimpleDocTemplate(str(R/'paper.pdf'),pagesize=(595,842),leftMargin=58,rightMargin=58,topMargin=48,bottomMargin=57).build(flow,onFirstPage=footer,onLaterPages=footer)
