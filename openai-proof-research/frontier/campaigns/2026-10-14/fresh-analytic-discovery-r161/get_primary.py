import pathlib,urllib.request,json,hashlib,subprocess,sys
R=pathlib.Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r161/private/primary'); name,url=sys.argv[1:]; record={'name':name,'requested_url':url}
try:
 with urllib.request.urlopen(url,timeout=45) as f:b=f.read();record['resolved_url']=f.url
 assert b.startswith(b'%PDF'), 'not PDF'
 p=R/(name+'.pdf');p.write_bytes(b);record.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
 subprocess.run(['pdftotext','-layout',str(p),str(R/(name+'.txt'))],check=True)
 t=(R/(name+'.txt')).read_bytes();record.update(text_bytes=len(t),text_sha256=hashlib.sha256(t).hexdigest())
except Exception as e:record['failure']=repr(e)
p=R/'identities.json';a=json.loads(p.read_text()) if p.exists() else [];a.append(record);p.write_text(json.dumps(a,indent=2)+'\n');print(json.dumps(record))
