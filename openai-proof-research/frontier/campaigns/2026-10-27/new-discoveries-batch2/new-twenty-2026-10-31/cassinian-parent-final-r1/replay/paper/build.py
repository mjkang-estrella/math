from pathlib import Path
import sys,os,resource
D=Path(__file__).resolve().parent
os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]));resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
sys.path.insert(0,str(D.parent/'tmp/pdfdeps'))
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,PageBreak,Table,TableStyle
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib.enums import TA_LEFT
from xml.sax.saxutils import escape
pdfmetrics.registerFont(TTFont('Open','/usr/share/fonts/open-sans/OpenSans-Regular.ttf'))
pdfmetrics.registerFont(TTFont('OpenBold','/usr/share/fonts/open-sans/OpenSans-Bold.ttf'))
styles={
 'body':ParagraphStyle('body',fontName='Open',fontSize=9.4,leading=13.3,spaceAfter=8),
 'title':ParagraphStyle('title',fontName='OpenBold',fontSize=18,leading=23,spaceAfter=12),
 'heading':ParagraphStyle('heading',fontName='OpenBold',fontSize=12,leading=16,spaceAfter=11),
 'math':ParagraphStyle('math',fontName='Open',fontSize=8.6,leading=12,spaceAfter=9,leftIndent=12),
 'refs':ParagraphStyle('refs',fontName='Open',fontSize=7.6,leading=10,spaceAfter=5),
}
def footer(c,d):
 c.setFont('Open',7.5);c.drawString(48,28,'DRAFT | MathDB 331705 | AI-assisted | No priority claim');c.drawRightString(564,28,str(d.page))
story=[]
for page,txt in enumerate((D/'manuscript.txt').read_text().split('===PAGE===')):
 if page:story.append(PageBreak())
 for i,block in enumerate(txt.strip().split('\n\n')):
  block=block.strip();key='body'
  if page==0 and i==0:key='title'
  elif block[0:2] in ['1.','2.','3.','4.','5.','6.'] or block in ['Abstract','References']:key='heading'
  elif block.startswith('['):key='refs'
  elif '\n' in block or block.startswith(('c_D','B_c','K =','y =','boundary U','20b','F(s','c_U','p_0','|p_0|','|z|²','p interval','s interval','F_+','Q(t)','F_-','(222','(504','(840','c_G')):key='math'
  if block.startswith(('Paper content','s interval')):
   import re
   rows=[]
   for line in block.splitlines():
    cells=re.split(r' {2,}',line.strip(),maxsplit=1)
    if len(cells)==1:
     rows[-1][1]+=' '+cells[0]
    else:rows.append(cells)
   data=[[Paragraph(escape(c),styles['math']) for c in row] for row in rows]
   tab=Table(data,colWidths=[190,326],hAlign='LEFT')
   tab.setStyle(TableStyle([('VALIGN',(0,0),(-1,-1),'TOP'),('LINEBELOW',(0,0),(-1,0),0.5,__import__('reportlab').lib.colors.grey),('BOTTOMPADDING',(0,0),(-1,-1),3)]))
   story.append(tab);story.append(Spacer(1,8))
  else:story.append(Paragraph(escape(block).replace('\n','<br/>'),styles[key]))
doc=SimpleDocTemplate(str(D/'draft.pdf'),pagesize=(612,792),rightMargin=48,leftMargin=48,topMargin=43,bottomMargin=47,title='A wedge-complement domain with a nonstarlike Cassinian ball',author='AI-assisted draft; no human author asserted')
doc.build(story,onFirstPage=footer,onLaterPages=footer)
print(D/'draft.pdf')
