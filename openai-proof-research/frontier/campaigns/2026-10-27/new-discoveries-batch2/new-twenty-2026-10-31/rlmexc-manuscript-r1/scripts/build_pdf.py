import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,xml.etree.ElementTree as ET
import sys
sys.path.insert(0,"/home/mj-kang/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/lib/python3.12/site-packages")
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,PageBreak,Table,TableStyle
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib import colors
pdfmetrics.registerFont(TTFont('Body','/usr/share/fonts/google-noto-vf/NotoSerif[wght].ttf'))
pdfmetrics.registerFont(TTFont('Math','/usr/share/fonts/google-noto/NotoSansMath-Regular.ttf'))
pdfmetrics.registerFont(TTFont('Bold','/usr/share/fonts/liberation-serif-fonts/LiberationSerif-Bold.ttf'))
pdfmetrics.registerFont(TTFont('Italic','/usr/share/fonts/liberation-serif-fonts/LiberationSerif-Italic.ttf'))
pdfmetrics.registerFontFamily('Body',normal='Body',bold='Bold',italic='Italic',boldItalic='Bold')
styles={
 'p':ParagraphStyle('body',fontName='Body',fontSize=10,leading=13.5,spaceAfter=8),
 'math':ParagraphStyle('math',fontName='Body',fontSize=10,leading=15,leftIndent=13,spaceAfter=9),
 'h':ParagraphStyle('heading',fontName='Bold',fontSize=13,leading=16,spaceBefore=4,spaceAfter=9),
 'title':ParagraphStyle('title',fontName='Bold',fontSize=18,leading=21,spaceAfter=14),
 'cell':ParagraphStyle('cell',fontName='Body',fontSize=9,leading=12)}
def P(s,kind='p'):
 s=''.join(('<font name="Math">'+ch+'</font>') if ord(ch)>127 and ord(ch) not in pdfmetrics.getFont('Body').face.charToGlyph else ch for ch in s)
 return Paragraph(s,styles[kind])
def table(rows,widths=None):
 t=Table([[P(str(v),'cell') for v in row] for row in rows],colWidths=widths,hAlign='LEFT')
 t.setStyle(TableStyle([('VALIGN',(0,0),(-1,-1),'TOP'),('BACKGROUND',(0,0),(-1,0),colors.HexColor('#edf0f4')),('LINEBELOW',(0,0),(-1,0),.5,colors.grey),('LINEBELOW',(0,-1),(-1,-1),.4,colors.grey),('TOPPADDING',(0,0),(-1,-1),5),('BOTTOMPADDING',(0,0),(-1,-1),5)]));return t
root=ET.parse('manuscript.xml').getroot();story=[]
for page in root:
 if story:story.append(PageBreak())
 for el in page:
  if el.tag in styles:
   text=(el.text or '')+''.join(ET.tostring(child,encoding='unicode') for child in el)
   story.append(P(text,el.tag))
  elif el.tag=='tails':
   rows=[['Name','Tail at positions c,…,c+4','Cycle lengths','inv at n=9']]
   tails=['c+2, 1, c+1, c+5, c+3','c+2, 1, c+5, c+1, c+3','c+2, c+5, 1, c+1, c+3','1, c+2, c+1, c+5, c+3','1, c+2, c+5, c+1, c+3','c+5, c+2, 1, c+1, c+3','1, c+2, c+1, c+3, c+5','c+2, 1, c+1, c+3, c+5']
   types=['n−3, 3','n','n−4, 4','n−5, 3, 2','n−5, 5','n','n−5, 2, 2, 1','n−3, 2, 1']
   f=next(v for v in json.loads(Path('outputs/family.json').read_text()) if v['n']==9)
   for row,t,cy in zip(f['rows'],tails,types):rows.append([row['name'],t,cy,row['inv']])
   story += [table(rows,[43,220,110,100]),Spacer(1,9)]
  elif el.tag=='counts':
   rows=[['n','Permutations','k','Positive coefficients','Negative coefficients']]
   for n,k in [(8,3),(9,3),(10,3),(10,4)]:
    a=json.loads(Path('outputs/full-n%d.json'%n).read_text());d=a['counts'][str(k)]
    rows.append([n,format(a['permutations'],','),k,d['positive'],d['negative']])
   story +=[table(rows,[30,90,25,162,166]),Spacer(1,9)]
def foot(canvas,doc):
 canvas.setFont('Body',8);canvas.setFillColor(colors.HexColor('#555555'))
 canvas.drawString(50,27,'DRAFT • AI-assisted • MathDB 350721 • No acceptance or priority claim')
 canvas.drawRightString(562,27,str(doc.page))
doc=SimpleDocTemplate('manuscript.pdf',pagesize=(612,792),rightMargin=50,leftMargin=50,topMargin=43,bottomMargin=45,title='A negative coefficient for every n ≥ 8',author='AI-assisted draft; no human authors asserted')
doc.build(story,onFirstPage=foot,onLaterPages=foot)
print('Built manuscript.pdf')
