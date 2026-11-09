from pathlib import Path
D=Path(__file__).resolve().parents[1];p=D/'scripts/recompute.py';s=p.read_text().replace("'cycle':cycle,'forcing_table':table", "'comparison_graph':[sorted(es) for es in graph(witness)],'cycle':cycle,'forcing_table':table")
s=s.replace("rest=set(ps)-set(base);", "assert set(base)=={p for p in ps if all(red(q) not in [(0,2,1),(1,0,2)] for q in __import__('itertools').combinations(p,3))}\nassert all(v in graph(base)[u] for u,v in [(4,1),(7,4),(1,7)])\nrest=set(ps)-set(base);")
p.write_text(s)
p=D/'scripts/render.py';s=p.read_text().replace("block=html.escape(block).replace('≅','<font name=\"Math\">≅</font>').replace('□','QED')", "block=''.join(html.escape(ch) if ord(ch) in pdfmetrics.getFont(s[style].fontName).face.charToGlyph else '<font name=\"Math\">'+html.escape(ch)+'</font>' for ch in block.replace('□','QED'))")
p.write_text(s)
