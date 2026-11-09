from pathlib import Path
D=Path(__file__).resolve().parents[1];p=D/'scripts/render.py';s=p.read_text();s=s.replace("s=getSampleStyleSheet();", "pdfmetrics.registerFont(TTFont('Math','/usr/share/fonts/google-noto/NotoSansMath-Regular.ttf'))\ns=getSampleStyleSheet();")
s=s.replace("story.append(Paragraph(html.escape(block).replace('\\n','<br/>'),s[style]))", "block=html.escape(block).replace('≅','<font name=\"Math\">≅</font>').replace('□','QED')\n   story.append(Paragraph(block.replace('\\n','<br/>'),s[style]))")
p.write_text(s)
# Put date/status into a separate paragraph, leaving title concise.
p=D/'manuscript.md';s=p.read_text().replace('realizes\nDRAFT','realizes\n\nDRAFT');p.write_text(s)
