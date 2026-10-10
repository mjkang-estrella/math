"""Pure lossless decoded-field index. Raw JSON remains the authoritative byte record."""
import json,re
from collections import defaultdict

def decode(contexts,load):
 lines=[];ids={};fields=[]
 def line_ids(text):
  out=[]
  for line in text.splitlines(keepends=True):
   if line not in ids:ids[line]=len(lines);lines.append(line)
   out.append(ids[line])
  return out
 def walk(x,path):
  if isinstance(x,dict):
   for k,v in x.items():walk(v,path+[k])
  elif isinstance(x,list):
   for i,v in enumerate(x):walk(v,path+[i])
  elif isinstance(x,str):
   try:z=json.loads(x)
   except (ValueError,TypeError):z=None
   if isinstance(z,(dict,list)):
    fields.append(dict(path=path,kind='json-string'));walk(z,path+['<JSON>']);return
   for m in re.finditer(r'(?m)^\{',x):
    try:z=json.loads(x[m.start():])
    except ValueError:continue
    if isinstance(z,dict):
     fields.append(dict(path=path,kind='text-plus-JSON',prefix=line_ids(x[:m.start()])));walk(z,path+['<parent JSON>']);return
   fields.append(dict(path=path,kind='string',lines=line_ids(x)))
  else:fields.append(dict(path=path,kind='scalar',value=x))
 for c in contexts:walk(load(c['snapshot']),[c['snapshot']])
 scalars=defaultdict(list)
 for r in fields:
  if r['kind']=='scalar':scalars[json.dumps([r['path'][-1],r['value']],ensure_ascii=False)].append(r['path'])
 view=''.join(str(i)+': '+line+('' if line.endswith('\n') else '\n') for i,line in enumerate(lines))
 return lines,fields,view,dict(scalars),'\n'.join(scalars)+'\n'
