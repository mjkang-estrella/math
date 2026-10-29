import sys,hashlib,json,platform
from pathlib import Path
import reportlab
from reportlab.pdfgen.canvas import Canvas
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,KeepTogether
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
R=Path(__file__).resolve().parent
font=R/'assets/LiberationSerif-Regular.ttf'
pdfmetrics.registerFont(TTFont('Paper',str(font)))
pdfmetrics.registerFont(TTFont('Symbols',str(R/'assets/Symbola.ttf')))
styles={
 'body':ParagraphStyle('body',fontName='Paper',fontSize=10.5,leading=15,spaceAfter=8,allowWidows=0,allowOrphans=0),
 'head':ParagraphStyle('head',fontName='Paper',fontSize=12,leading=16,spaceBefore=12,spaceAfter=9,keepWithNext=True),
 'title':ParagraphStyle('title',fontName='Paper',fontSize=18,leading=23,alignment=1,spaceAfter=13),
 'center':ParagraphStyle('center',fontName='Paper',fontSize=9,leading=13,alignment=1,spaceAfter=8),
 'eq':ParagraphStyle('eq',fontName='Paper',fontSize=10,leading=17,leftIndent=12,spaceBefore=4,spaceAfter=10),
}
story=[]
for block in (R/'paper.txt').read_text().strip().split('\n\n'):
 tag,sep,text=block.partition(': ')
 key={'TITLE':'title','AUTHOR':'center','DATE':'center','H':'head','EQ':'eq'}.get(tag,'body')
 if key=='body':text=block if tag not in ['ABSTRACT','THEOREM'] else tag.title()+'. '+text
 for ch in sorted(set(text)):
  if ord(ch)>127 and ord(ch) not in pdfmetrics.getFont('Paper').face.charToGlyph:
   assert ord(ch) in pdfmetrics.getFont('Symbols').face.charToGlyph,ch
   text=text.replace(ch,'<font name="Symbols">'+ch+'</font>')
 story.append(Paragraph(text,styles[key]))
def page(c,d):
 c.setFont('Paper',8);c.drawString(52,28,'Research manuscript · Rényi threshold · review pending')
 c.drawRightString(560,28,str(d.page))
class FixedCanvas(Canvas):
 def __init__(self,*a,**kw):kw['invariant']=1;super().__init__(*a,**kw)
out=Path(sys.argv[1]) if len(sys.argv)>1 else R/'paper.pdf'
doc=SimpleDocTemplate(str(out),pagesize=(612,792),rightMargin=52,leftMargin=52,topMargin=45,bottomMargin=48,title='Truncated exponentials defeat every subunit Rényi threshold',author='Research manuscript',pageCompression=1)
doc.build(story,onFirstPage=page,onLaterPages=page,canvasmaker=FixedCanvas)
print(json.dumps({'pdf_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'reportlab':reportlab.Version,'python':platform.python_version(),'font_sha256':hashlib.sha256(font.read_bytes()).hexdigest()}))
