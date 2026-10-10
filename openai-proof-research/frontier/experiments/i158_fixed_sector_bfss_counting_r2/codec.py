"""Pure task decoder, independently maintained in I158; no input executes."""
import json,re

def decode(contexts,base):
 lines=list(base);lookup={s:i for i,s in enumerate(lines)};fields=[]
 def ids(s):
  out=[]
  for line in s.splitlines(keepends=True):
   if line not in lookup:lookup[line]=len(lines);lines.append(line)
   out.append(lookup[line])
  return out
 def walk(x,p):
  if isinstance(x,dict):
   fields.append(dict(path=p,kind='object',keys=list(x)))
   for k,v in x.items():walk(v,p+[k])
  elif isinstance(x,list):
   fields.append(dict(path=p,kind='array',length=len(x)))
   for i,v in enumerate(x):walk(v,p+[i])
  elif isinstance(x,str):
   try:z=json.loads(x)
   except ValueError:z=None
   if isinstance(z,(dict,list)):
    fields.append(dict(path=p,kind='json-string'));walk(z,p+['<JSON>']);return
   for m in re.finditer(r'(?m)^\{',x):
    try:z=json.loads(x[m.start():])
    except ValueError:continue
    if isinstance(z,dict):
     fields.append(dict(path=p,kind='text-plus-JSON',prefix=ids(x[:m.start()])));walk(z,p+['<parent JSON>']);return
   fields.append(dict(path=p,kind='string',lines=ids(x)))
  else:fields.append(dict(path=p,kind='scalar',value=x))
 for path,x in contexts:walk(x,[path])
 return lines,fields

def embedded(contexts):
 """Retain every valid JSON object/array embedded in strings, including nonterminal blocks.
 Container/string/scalar values remain exact, with occurrence paths and source-string offsets.
 """
 out=[];dec=json.JSONDecoder()
 def walk(x,p):
  if isinstance(x,dict):
   for k,v in x.items():walk(v,p+[k])
  elif isinstance(x,list):
   for i,v in enumerate(x):walk(v,p+[i])
  elif isinstance(x,str):
   used=0
   for m in re.finditer(r'(?m)^[ \t]*[\{\[]',x):
    a=m.end()-1
    if a<used:continue
    try:z,n=dec.raw_decode(x[a:])
    except ValueError:continue
    if not isinstance(z,(dict,list)):continue
    used=a+n
    out.append(dict(path=p,start=a,end=used,value=z))
    walk(z,p+['<embedded>',a])
 for path,x in contexts:walk(x,[path])
 return out
