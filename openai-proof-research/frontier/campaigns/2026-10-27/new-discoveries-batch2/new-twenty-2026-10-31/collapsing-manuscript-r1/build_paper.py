"""Build the eight-page DRAFT from paper-source.json; Python reportlab required."""
import json,html,sys
sys.path.insert(0,str(__import__('pathlib').Path(__file__).resolve().parent/'local-deps'))
from pathlib import Path
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,PageBreak,Preformatted
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
D=Path(__file__).resolve().parent
pdfmetrics.registerFont(TTFont('Body','/usr/share/fonts/liberation-serif-fonts/LiberationSerif-Regular.ttf'))
pdfmetrics.registerFont(TTFont('Mono','/usr/share/fonts/liberation-mono-fonts/LiberationMono-Regular.ttf'))
pdfmetrics.registerFont(TTFont('Symbols','/usr/share/fonts/gdouros-symbola/Symbola.ttf'))
def rich(text):
 return ''.join(html.escape(c) if ord(c) in pdfmetrics.getFont('Body').face.charToGlyph else '<font name="Symbols">'+html.escape(c)+'</font>' for c in text)
styles={'p':ParagraphStyle('p',fontName='Body',fontSize=10.2,leading=14.3,spaceAfter=9), 'h':ParagraphStyle('h',fontName='Body',fontSize=15,leading=20,spaceAfter=14),'code':ParagraphStyle('code',fontName='Mono',fontSize=8.2,leading=11,spaceAfter=10)}
def footer(c,d):
 c.setFont('Body',8);c.drawString(49,30,'DRAFT · AI-assisted · MathDB 378395 · zero accepted credit');c.drawRightString(562,30,str(d.page))
story=[]
for i,page in enumerate(json.loads((D/'paper-source.json').read_text())):
 if i: story.append(PageBreak())
 for kind,text in page: story.append(Preformatted(text,styles['code']) if kind=='code' else Paragraph(rich(text),styles[kind]))
SimpleDocTemplate(str(D/'paper.pdf'),pagesize=(612,792),leftMargin=49,rightMargin=49,topMargin=43,bottomMargin=49,title='An explicit non-collapsing facet of the 4 × 4 × 5 marginal cone',author='AI-assisted research draft').build(story,onFirstPage=footer,onLaterPages=footer)
