from pathlib import Path
import re,json,html,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"tmp/pdf-deps"))
from reportlab.pdfgen import canvas
from reportlab.lib.styles import ParagraphStyle
from reportlab.platypus import Paragraph,Table,TableStyle,Preformatted
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
D=Path(__file__).resolve().parents[1]
for name,file in [('Body','LiberationSerif-Regular.ttf'),('Bold','LiberationSerif-Bold.ttf'),('Mono','LiberationMono-Regular.ttf'),('Symbol','Symbola.ttf')]:
    pdfmetrics.registerFont(TTFont(name,str(D/'fonts'/file)))
pdfmetrics.registerFontFamily('Body',normal='Body',bold='Bold',italic='Body',boldItalic='Bold')
def markup(s):
    s=html.escape(s.strip().removeprefix('> '))
    s=re.sub(r'\*\*(.*?)\*\*',r'<b>\1</b>',s)
    s=re.sub(r'`([^`]+)`',r'\1',s)
    s=re.sub(r'([A-Za-zΨΦ]+)_\{([^}]+)\}',r'\1<sub>\2</sub>',s)
    s=re.sub(r'(N)_([ABH])',r'\1<sub>\2</sub>',s)
    s=re.sub(r'([A-Za-z]+)\^(\{[^}]+\}|[A-Za-z0-9]+)',lambda m:m[1]+'<super>'+m[2].strip('{}')+'</super>',s)
    s=re.sub(r'(?<!\*)\*([^*]+)\*(?!\*)',r'<i>\1</i>',s)
    return ''.join('<font name="Symbol">'+ch+'</font>' if ord(ch)>127 and ord(ch) not in pdfmetrics.getFont('Body').face.charToGlyph else ch for ch in s)
W,H=612,792; left=48; width=516; top=742; bottom=48

def flowables(src,size):
    body=ParagraphStyle('b',fontName='Body',fontSize=size,leading=size*1.23,spaceAfter=4)
    heading=ParagraphStyle('h',parent=body,fontName='Bold',fontSize=size+3,leading=(size+3)*1.2,spaceBefore=5,spaceAfter=8)
    title=ParagraphStyle('t',parent=heading,fontSize=21,leading=25,spaceAfter=10)
    out=[];blocks=re.split(r'\n\s*\n',src.strip())
    for block in blocks:
        if block.startswith('```'):
            text=block.split('\n',1)[1].rsplit('```',1)[0].rstrip()
            # Exact JSON characters retained; long string values wrap visually only.
            st=ParagraphStyle('code',fontName='Mono',fontSize=7.4,leading=9.0)
            for line in text.splitlines():
                out.append(Paragraph(html.escape(line).replace(' ','&#160;'),st))
        elif block.startswith('|'):
            rows=[[Paragraph(markup(c),ParagraphStyle('cell',parent=body,fontSize=size-0.4,leading=size*1.15)) for c in line.strip('|').split('|')] for line in block.splitlines() if not re.fullmatch(r'[| :\-]+',line)]
            cols=[190,width-190] if len(rows[0])==2 else [100,170,width-270]
            t=Table(rows,colWidths=cols,hAlign='LEFT');t.setStyle(TableStyle([('VALIGN',(0,0),(-1,-1),'TOP'),('BACKGROUND',(0,0),(-1,0),'#e8edf1'),('LINEBELOW',(0,0),(-1,0),0.5,'#607080'),('BOTTOMPADDING',(0,0),(-1,-1),5),('TOPPADDING',(0,0),(-1,-1),4)]));out.append(t)
        elif block.startswith('# '):out.append(Paragraph(markup(block[2:]),title))
        elif block.startswith('## '):out.append(Paragraph(markup(block[3:]),heading))
        elif block.startswith('- '):
            for line in block.splitlines():out.append(Paragraph('• '+markup(line.removeprefix('- ')),body))
        else:out.append(Paragraph(markup(block.replace('\n',' ')),body))
    return out
c=canvas.Canvas(str(D/'paper.pdf'),pagesize=(W,H));c.setTitle('Power-domination TAR uniqueness for complete bipartite graphs');c.setAuthor('AI-assisted draft; no human authorship asserted')
receipts=[]
for i,src in enumerate((D/'paper.md').read_text().split('<!-- PAGE -->'),1):
    for size in [10.5,10.3,10.1,9.9,9.7,9.5]:
        fs=flowables(src,size); heights=[f.wrap(width,10000)[1]+f.getSpaceBefore()+f.getSpaceAfter() for f in fs]
        if sum(heights)<=top-bottom:break
    assert sum(heights)<=top-bottom,(i,sum(heights))
    y=top
    c.setFont('Body',8);c.setFillColorRGB(.3,.35,.4);c.drawString(left,768,'DRAFT  •  MathDB 353203  •  PD-TAR uniqueness');c.setFillColorRGB(0,0,0)
    for f in fs:
        y-=f.getSpaceBefore();h=f.wrap(width,10000)[1];f.drawOn(c,left,y-h);y-=h+f.getSpaceAfter()
    c.setFont('Body',8);c.drawString(left,28,'AI-assisted draft • Root adjudication pending');c.drawRightString(W-left,28,str(i));c.showPage()
    receipts.append({'page':i,'font_size':size,'content_height':round(sum(heights),2),'bottom_y':round(y,2)})
c.save();(D/'qa/layout.json').write_text(json.dumps(receipts,indent=2)+'\n');print(receipts)
