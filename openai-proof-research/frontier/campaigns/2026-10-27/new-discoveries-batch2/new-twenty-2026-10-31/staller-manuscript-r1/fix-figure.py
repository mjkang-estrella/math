from pathlib import Path
r=Path(__file__).resolve().parent;s=(r/'paper.tex').read_text().replace('longtable,tikz,hyperref','longtable,hyperref');a=s.index(r'\begin{tikzpicture}');b=s.index(r'\end{tikzpicture}',a)+len(r'\end{tikzpicture}');pos={1:(10,55),5:(250,55),0:(130,105),6:(130,55),2:(70,10),3:(130,10),4:(190,10)};edges=[(1,0),(0,5),(1,6),(6,5),(1,2),(2,3),(3,4),(4,5)];pic=r'\setlength{\unitlength}{1pt}\begin{picture}(270,120)'+'\n'
for u,v in edges:
 x,y=pos[u];z,w=pos[v];pic+=r'\qbezier(%s,%s)(%s,%s)(%s,%s)'%(x,y,(x+z)/2,(y+w)/2,z,w)+'\n'
for n,(x,y) in pos.items():pic+=r'\put(%s,%s){\circle*{17}}\put(%s,%s){\makebox(0,0){\color{white}%s}}'%(x,y,x,y,n)+'\n'
pic+=r'\end{picture}';s=s[:a]+pic+s[b:];s=s.replace('including generated anonymous-example declarations','including any generated declarations; anonymous examples are checked during compilation and are not retained as declarations');(r/'paper.tex').write_text(s)
(r/'paper-template.tex').write_text(s)
(r/'author-paper.py').write_text('from pathlib import Path\nr=Path(__file__).resolve().parent\n(r/"paper.tex").write_bytes((r/"paper-template.tex").read_bytes())\n')
