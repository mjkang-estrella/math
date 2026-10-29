from pathlib import Path
import json
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,Table,TableStyle,KeepTogether
from reportlab.lib.styles import getSampleStyleSheet,ParagraphStyle
from reportlab.lib import colors
from reportlab.pdfgen.canvas import Canvas
R=Path(__file__).resolve().parent
styles=getSampleStyleSheet()
styles.add(ParagraphStyle('body',fontName='Times-Roman',fontSize=10.5,leading=12.5,spaceAfter=6))
styles.add(ParagraphStyle('eqn',fontName='Times-Roman',fontSize=10,leading=13,alignment=1,spaceAfter=10))
styles['Title'].fontName='Times-Bold';styles['Title'].fontSize=20;styles['Title'].leading=23
styles['Heading2'].fontName='Times-Bold';styles['Heading2'].fontSize=13
cert=json.loads((R/'certificate.json').read_text());story=[]
def table(data,widths):
 t=Table(data,colWidths=widths,repeatRows=1,hAlign='CENTER')
 t.setStyle(TableStyle([('FONTNAME',(0,0),(-1,-1),'Times-Roman'),('FONTSIZE',(0,0),(-1,-1),9),('ALIGN',(0,0),(-1,-1),'CENTER'),('BACKGROUND',(0,0),(-1,0),colors.HexColor('#e9edf0')),('LINEBELOW',(0,0),(-1,0),.5,colors.grey),('TOPPADDING',(0,0),(-1,-1),2),('BOTTOMPADDING',(0,0),(-1,-1),2)]))
 return t
for kind,txt in json.loads((R/'paper.json').read_text()):
 if kind=='totals':
  story.append(KeepTogether([table([['p','A total','B total']]+[[p,a,b] for p,a,b in zip(cert['primes'],*cert['totals'])],[65,90,90]) ]));story.append(Spacer(1,10))
 elif kind=='matrix':
  story.append(table([['t']+cert['primes']]+[[t]+row for t,row in zip(cert['A']+cert['B'],cert['rows'])],[30]+[36]*11));story.append(Spacer(1,10))
 else:
  style={'title':'Title','subtitle':'eqn','p':'body','eq':'eqn','h':'Heading2'}[kind]
  story.append(Paragraph(txt.replace('Jevtić','Jevtic').replace('&','&amp;').replace('<','&lt;').replace('>','&gt;'),styles[style]))
def footer(c,d):
 c.setFont('Times-Roman',9);c.setFillColor(colors.grey);c.drawCentredString(306,30,str(d.page))
class StableCanvas(Canvas):
 def __init__(self,*a,**kw):kw['invariant']=1;super().__init__(*a,**kw)
doc=SimpleDocTemplate(str(R/'paper.pdf'),pagesize=(612,792),leftMargin=60,rightMargin=60,topMargin=47,bottomMargin=47,title='A distinct-support factorial-product collision',author='Research manuscript')
doc.build(story,onFirstPage=footer,onLaterPages=footer,canvasmaker=StableCanvas)
