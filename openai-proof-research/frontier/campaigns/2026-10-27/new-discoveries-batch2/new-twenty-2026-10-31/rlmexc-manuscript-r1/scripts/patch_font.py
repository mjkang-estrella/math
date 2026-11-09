from pathlib import Path
p=Path('scripts/build_pdf.py');s=p.read_text().replace("pdfmetrics.registerFont(TTFont('Bold'", "pdfmetrics.registerFont(TTFont('Math','/usr/share/fonts/google-noto/NotoSansMath-Regular.ttf'))\npdfmetrics.registerFont(TTFont('Bold'")
s=s.replace("def P(s,kind='p'):return Paragraph(s,styles[kind])",'''def P(s,kind='p'):
 s=''.join(('<font name="Math">'+ch+'</font>') if ord(ch)>127 and ord(ch) not in pdfmetrics.getFont('Body').face.charToGlyph else ch for ch in s)
 return Paragraph(s,styles[kind])''')
p.write_text(s)
