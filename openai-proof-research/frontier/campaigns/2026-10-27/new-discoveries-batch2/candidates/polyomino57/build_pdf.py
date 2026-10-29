from pathlib import Path
import resource,signal,os,sys,html,json,hashlib
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1')
import reportlab
from reportlab.pdfgen import canvas
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,PageBreak,Flowable
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
L=Path(__file__).resolve().parent
font=L/'fonts/LiberationSans-Regular.ttf'
for n,f in [('Body',font),('Bold',font.with_name('LiberationSans-Bold.ttf'))]:pdfmetrics.registerFont(TTFont(n,str(f)))
pdfmetrics.registerFont(TTFont('Math',str(L/'fonts/NotoSansMath-Regular.ttf')))
style=ParagraphStyle('body',fontName='Body',fontSize=9.25,leading=13.3,spaceAfter=8,textColor='#203145')
head=ParagraphStyle('head',parent=style,fontName='Bold',fontSize=13,leading=17,spaceBefore=6,spaceAfter=12)
title=ParagraphStyle('title',parent=head,fontSize=19,leading=24)
class Figure(Flowable):
 def __init__(self):Flowable.__init__(self);self.width=516;self.height=174
 def draw(self):
  c=self.canv;s=14;ox=258;oy=86
  for x in range(-5,6):
   for y in range(-5,6):
    if abs(x)+abs(y)>5:continue
    hole=abs(x)==abs(y)==2
    c.setFillColorRGB(*((1,1,1) if hole else (.22,.48,.65)));c.setStrokeColorRGB(.48,.61,.68);c.setLineWidth(.4)
    a=ox+x*s;b=oy+y*s;c.rect(a-s/2,b-s/2,s,s,stroke=1,fill=1)
    if hole:
     c.setStrokeColorRGB(.7,.25,.2);c.line(a-4,b-4,a+4,b+4);c.line(a-4,b+4,a+4,b-4)
def footer(c,d):
 c.setFont('Body',8);c.setFillColorRGB(.4,.46,.52);c.drawString(48,28,'Polyomino57 | proof replay and final review completed');c.drawRightString(564,28,str(d.page))
class Fixed(canvas.Canvas):
 def __init__(self,*a,**k):k['invariant']=1;super().__init__(*a,**k)
output=Path(sys.argv[1]) if len(sys.argv)>1 else L/'paper.pdf'
doc=SimpleDocTemplate(str(output),pagesize=(612,792),rightMargin=48,leftMargin=48,topMargin=40,bottomMargin=45,title='A 57-cell container for every fixed 11-omino',author='Research candidate')
flow=[]
for pi,page in enumerate((L/'paper.txt').read_text().split('---PAGE---')):
 if pi:flow.append(PageBreak())
 for para in page.strip().split('\n\n'):
  if para.startswith('[[FIGURE]]'):
   flow.append(Figure());para=para.removeprefix('[[FIGURE]]').strip()
  if para.startswith('# ' ) or para.startswith('## '):
   first,_,rest=para.partition('\n')
   st=title if first.startswith('# ') else head
   flow.append(Paragraph(html.escape(first.lstrip('# ')),st));para=rest.strip()
  if not para:continue
  txt=html.escape(para).replace('\n','<br/>')
  for ch in '⊆∅↦∈∪':txt=txt.replace(ch,'<font name="Math">'+ch+'</font>')
  flow.append(Paragraph(txt,style))
doc.build(flow,onFirstPage=footer,onLaterPages=footer,canvasmaker=Fixed)
# Standalone, deterministic vector diagram source.
svg=['<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 220 220">']
for x in range(-5,6):
 for y in range(-5,6):
  if abs(x)+abs(y)>5:continue
  hole=abs(x)==abs(y)==2;a=100+18*x;b=100-18*y
  svg.append(f'<rect x="{a}" y="{b}" width="18" height="18" fill="{("white" if hole else "#387ba6")}" stroke="#7b9bad"/>')
  if hole:svg.append(f'<path d="M {a+4},{b+4} l 10,10 m -10,0 l 10,-10" stroke="#b34033"/>')
svg.append('</svg>');(L/'container.svg').write_text('\n'.join(svg)+'\n')
print(json.dumps(dict(pdf_sha256=hashlib.sha256(output.read_bytes()).hexdigest(),reportlab=reportlab.Version,font_sha256=hashlib.sha256(font.read_bytes()).hexdigest())))
