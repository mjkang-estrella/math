"""Lossless recursive decoded-field view; occurrences retained separately."""
import json,re

def decode(contexts):
 lines=[]; lookup={}; fields=[]
 def ids(s):
  out=[]
  for line in s.splitlines(keepends=True):
   if line not in lookup:lookup[line]=len(lines);lines.append(line)
   out.append(lookup[line])
  return out
 def walk(x,p):
  if isinstance(x,dict):
   for k,v in x.items():walk(v,p+[k])
  elif isinstance(x,list):
   for i,v in enumerate(x):walk(v,p+[i])
  elif isinstance(x,str):
   try:z=json.loads(x)
   except ValueError:z=None
   if isinstance(z,(dict,list)):
    fields.append({'path':p,'kind':'json-string'});walk(z,p+['<JSON>']);return
   for m in re.finditer(r'(?m)^\{',x):
    try:z=json.loads(x[m.start():])
    except ValueError:continue
    if isinstance(z,dict):
     fields.append({'path':p,'kind':'text-plus-JSON','prefix':ids(x[:m.start()])});walk(z,p+['<parent JSON>']);return
   fields.append({'path':p,'kind':'string','lines':ids(x)})
  else:fields.append({'path':p,'kind':'scalar','value':x})
 for path,x in contexts:walk(x,[path])
 return lines,fields
