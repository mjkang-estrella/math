import urllib.request, pathlib, hashlib, json, datetime, subprocess
root=pathlib.Path("frontier/sources/i29_common_base_entropy/literature"); root.mkdir(parents=True,exist_ok=True)
items=[("aov-current","https://arxiv.org/abs/1807.00929","html"),("aov-v2","https://arxiv.org/pdf/1807.00929v2","pdf"),("chen-liu-current","https://arxiv.org/abs/2610.06724","html"),("chen-liu-v1","https://arxiv.org/html/2610.06724v1","html"),("tu-current","https://arxiv.org/abs/2609.39917","html"),("tu-v1","https://arxiv.org/pdf/2609.39917v1","pdf")]
rows=[]
for name,url,ext in items:
 try:
  req=urllib.request.Request(url,headers={"User-Agent":"Research source comparison"})
  with urllib.request.urlopen(req,timeout=50) as r: b=r.read();meta=dict(r.headers); final=r.url
  path=root/(name+"."+ext);path.write_bytes(b)
  row={"url":url,"final_url":final,"path":str(path),"retrieved":datetime.datetime.now(datetime.timezone.utc).isoformat(),"headers":meta,"sha256":hashlib.sha256(b).hexdigest(),"bytes":len(b)}
  if ext=="pdf" and b.startswith(b"%PDF"):
   txt=path.with_suffix(".txt"); subprocess.run(["pdftotext","-layout",str(path),str(txt)],check=True);row["text_path"]=str(txt);row["text_sha256"]=hashlib.sha256(txt.read_bytes()).hexdigest()
  rows.append(row);print(name,len(b),flush=True)
 except Exception as ex: rows.append({"url":url,"error":str(ex)})
(root/"manifest.json").write_text(json.dumps(rows,indent=2)+"\n")
