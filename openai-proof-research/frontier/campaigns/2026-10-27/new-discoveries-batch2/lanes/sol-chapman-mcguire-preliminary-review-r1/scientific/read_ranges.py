from retrieve import *
for spec in sys.argv[1:]:
 ident,a,b=spec.split(':');p=L/'sources'/(ident+'.txt');lines=p.read_text().splitlines();print('\n###',spec,'\n','\n'.join(lines[int(a)-1:int(b)]))
