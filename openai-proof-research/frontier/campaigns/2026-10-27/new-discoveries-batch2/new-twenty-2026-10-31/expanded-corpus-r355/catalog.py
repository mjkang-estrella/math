exec(compile((__import__('pathlib').Path(__file__).parent/'research.py').read_text(),'research.py','exec'))
root=P.parents[5]; data=(root/'sources/CONTENTS.md').read_text(); lines=data.splitlines(); terms=['bicol','typical rank','hinged','Roberts','saturated','alternating descent','coefficientwise total','nesting poset','Ding','additive complexity']; out=[]
for n,line in enumerate(lines):
 if 'crown' in line.lower(): continue
 if any(t.lower() in line.lower() for t in terms): out.append(dict(line=n+1,text=line))
js('catalog-scoped.json',out)
for x in out: print(x)
