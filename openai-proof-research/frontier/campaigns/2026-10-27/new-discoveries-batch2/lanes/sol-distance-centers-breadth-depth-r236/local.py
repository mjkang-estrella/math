from research import *
import re
rows=[]
for root,dirs,files in os.walk(B.parent.parent.parent.parent):
 dirs[:]=[d for d in dirs if d not in ['.git','node_modules','.lake','frozen','copies','administrative','context','assigned-inputs','inputs']]
 for n in files:
  if re.search(r'47721|v63n2|tmna.*023|center.*dist|dist.*center',n,re.I):rows.append(str(pathlib.Path(root)/n))
save('local-source-paths.json',rows);print(rows[:100])
