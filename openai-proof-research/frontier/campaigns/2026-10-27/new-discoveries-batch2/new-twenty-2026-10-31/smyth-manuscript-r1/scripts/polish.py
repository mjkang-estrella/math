from pathlib import Path
import re
p=Path(__file__).with_name('paper.py');s=p.read_text()
s=s.replace('.nr PS 11', '.EQ\ndelim $$\n.EN\n.nr PS 11',1)
s=re.sub(r'U sup (\w+) sub (\w+)',r'U sub \2 sup \1',s)
a=s.index('.H "Conjecture 1.5');b=s.index('.bp',a)
s=s[:a]+r'''.H "Conjecture 1.5 [1] (verbatim)"
.QP
For all integer $A,a,B,b$ with $A >= B >= 0$ and $a >= b >= 0$ there is an
injection
.EQ
 gamma : U sub b sup A times U sub a sup B ~ "\(->" ~ U sub a sup A times U sub b sup B
.EN
.QP
such that for all $(lambda sub 1 , mu sub 1 ) ~ member ~ U sub b sup A times U sub a sup B$,
$(lambda sub 2 , mu sub 2 ) = gamma ((lambda sub 1 , mu sub 1 )) ~ member ~ U sub a sup A times U sub b sup B$
satisfies $lambda sub 1 mu sub 1$ \[dom] $lambda sub 2 mu sub 2$.
.PP
The source's dominance symbol means that the domain concatenation dominates
its image. The injection arrow above is printed as an ordinary arrow;
its injectivity is asserted in the quoted sentence. The original TeX, PDF,
and exact MathDB raw line are included in the dossier.
''' +s[b:]
p.write_text(s)
