from pathlib import Path
p=Path(__file__).resolve().parents[1]/'paper/manuscript.py';s=p.read_text()
s=s.replace("('Serif','DejaVuSerif.ttf'),('Bold','DejaVuSerif-Bold.ttf'),('Mono','DejaVuSansMono.ttf')", "('Serif','liberation-serif-fonts/LiberationSerif-Regular.ttf'),('Bold','liberation-serif-fonts/LiberationSerif-Bold.ttf'),('Mono','liberation-mono-fonts/LiberationMono-Regular.ttf'),('Symbols','gdouros-symbola/Symbola.ttf')")
s=s.replace("'/usr/share/fonts/truetype/dejavu/'","'/usr/share/fonts/'")
s=s.replace("def p(t,sty='Body'):story.append(Paragraph(t,ss[sty]))", """def p(t,sty='Body'):
 font=pdfmetrics.getFont(ss[sty].fontName)
 t=''.join(ch if ord(ch) in font.face.charToGlyph or ord(ch)<128 else '<font name="Symbols">'+ch+'</font>' for ch in t)
 story.append(Paragraph(t,ss[sty]))""")
s=s.replace("def eq(t):p(t,'Code2')","def eq(t):p(t.replace('\\n','<br/>').replace('  ','&nbsp;&nbsp;'),'Code2')")
s=s.replace('abstract on convex-QP recognition','“Convex quadratic programming applied to the stability number of a graph”')
p.write_text(s)
