from pathlib import Path
import re,html,json
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,PageBreak,Preformatted
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib import colors
D=Path(__file__).resolve().parents[1]
for n,f in [('Body','LiberationSerif-Regular.ttf'),('Bold','LiberationSerif-Bold.ttf'),('Mono','LiberationMono-Regular.ttf')]:
 folder='liberation-mono-fonts' if n=='Mono' else 'liberation-serif-fonts'
 pdfmetrics.registerFont(TTFont(n,'/usr/share/fonts/'+folder+'/'+f))
pdfmetrics.registerFont(TTFont('Math','/usr/share/fonts/google-noto/NotoSansMath-Regular.ttf'))
styles={'body':ParagraphStyle('body',fontName='Body',fontSize=10.5,leading=13.4,spaceAfter=7), 'title':ParagraphStyle('title',fontName='Bold',fontSize=19,leading=22,spaceAfter=13),'head':ParagraphStyle('head',fontName='Bold',fontSize=13,leading=16,spaceBefore=8,spaceAfter=9),'code':ParagraphStyle('code',fontName='Mono',fontSize=8.2,leading=11,spaceBefore=3,spaceAfter=8)}
def esc(s,font='Body'):
 out=[]
 for c in s.replace('**',''):
  t=html.escape(c)
  if ord(c)>127 and ord(c) not in pdfmetrics.getFont(font).face.charToGlyph:
   assert ord(c) in pdfmetrics.getFont('Math').face.charToGlyph,repr(c)
   t='<font name="Math">'+t+'</font>'
  out.append(t)
 return ''.join(out)
story=[]
for pi,page in enumerate((D/'paper-source.md').read_text().split('---PAGE---')):
 if pi:story.append(PageBreak())
 for b in page.strip().split('\n\n'):
  if b.startswith('# '):story.append(Paragraph(esc(b[2:]),styles['title']))
  elif b.startswith('## '):story.append(Paragraph(esc(b[3:]),styles['head']))
  elif b.startswith('    '):story.append(Paragraph('<br/>'.join(esc(x[4:],'Mono').replace(' ','&#160;') for x in b.splitlines()),styles['code']))
  else:story.append(Paragraph(esc(b),styles['body']))
def footer(c,d):
 c.setStrokeColor(colors.HexColor('#b8c4ce'));c.line(48,40,564,40)
 c.setFont('Body',9);c.drawString(48,27,'DRAFT • MathDB 380362 • AI-assisted • Zero accepted credit');c.drawRightString(564,27,str(d.page))
doc=SimpleDocTemplate(str(D/'paper.pdf'),pagesize=(612,792),leftMargin=48,rightMargin=48,topMargin=40,bottomMargin=53)
doc.build(story,onFirstPage=footer,onLaterPages=footer)
print('created paper.pdf')
