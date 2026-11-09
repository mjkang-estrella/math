from pathlib import Path
import sys,html
from reportlab.pdfgen import canvas
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,PageBreak,Table,TableStyle
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib import colors
P=Path(__file__).resolve().parent
out=Path(sys.argv[1]) if len(sys.argv)>1 else P/'output/pdf/cube-cct.pdf'
out.parent.mkdir(parents=True,exist_ok=True)
class FixedCanvas(canvas.Canvas):
 def __init__(self,*a,**kw):kw['invariant']=1;super().__init__(*a,**kw)
styles={
 'body':ParagraphStyle('body',fontName='Times-Roman',fontSize=10.4,leading=13.1,spaceAfter=8),
 'title':ParagraphStyle('title',fontName='Times-Bold',fontSize=19,leading=22,spaceAfter=12),
 'head':ParagraphStyle('head',fontName='Times-Bold',fontSize=12,leading=15,spaceBefore=7,spaceAfter=8),
 'formula':ParagraphStyle('formula',fontName='Courier',fontSize=8.6,leading=12,spaceBefore=4,spaceAfter=10,leftIndent=12),
}
story=[]
pages=(P/'manuscript.md').read_text().split('---PAGE---')
for n,page in enumerate(pages):
 if n:story.append(PageBreak())
 for block in page.strip().split('\n\n'):
  if block.startswith('| x / y |'):
   rows=[['x / y','2','9','10','13','19','20','score'],['2',1,8,2,16,4,8,39],['9',8,1,4,2,8,16,39],['10',2,4,1,8,8,16,39],['13',16,2,8,1,16,8,51],['19',4,8,8,16,1,8,45],['20',8,16,16,8,8,1,57]]
   t=Table(rows,colWidths=[58]+[43]*6+[58],rowHeights=23)
   t.setStyle(TableStyle([('FONTNAME',(0,0),(-1,-1),'Times-Roman'),('FONTNAME',(0,0),(-1,0),'Times-Bold'),('ALIGN',(0,0),(-1,-1),'CENTER'),('BACKGROUND',(0,0),(-1,0),colors.HexColor('#e8edf2')),('LINEBELOW',(0,0),(-1,0),.7,colors.black),('LINEBELOW',(0,-1),(-1,-1),.5,colors.black),('BACKGROUND',(0,4),(-1,4),colors.HexColor('#f0f3f6'))]))
   story.extend([t,Spacer(1,12)]);continue
  style='body'
  if block.startswith('# '):style='title';block=block[2:]
  elif block.startswith('## '):style='head';block=block[3:]
  elif block.startswith('    '):style='formula';block=block.strip()
  s=html.escape(block).replace('\n',' ')
  if s.startswith('**Theorem 1.**'):s=s.replace('**Theorem 1.**','<b>Theorem 1.</b>')
  story.append(Paragraph(s,styles[style]))
def footer(c,d):
 c.setStrokeColor(colors.HexColor('#aab3bb'));c.line(52,42,560,42)
 c.setFont('Times-Roman',8);c.drawString(52,30,'Cube common-cover transitivity | Unpublished research manuscript');c.drawRightString(560,30,str(d.page))
doc=SimpleDocTemplate(str(out),pagesize=(612,792),rightMargin=52,leftMargin=52,topMargin=45,bottomMargin=54,title='A six-point obstruction to common-cover transitivity of the cube',author='OpenAI Codex',pageCompression=1)
doc.build(story,onFirstPage=footer,onLaterPages=footer,canvasmaker=FixedCanvas)
print(out)
