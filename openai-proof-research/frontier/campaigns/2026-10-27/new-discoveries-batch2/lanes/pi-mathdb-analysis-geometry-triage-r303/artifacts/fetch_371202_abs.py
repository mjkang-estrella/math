import json,urllib.request,time,hashlib
for name,url in [('abs','https://arxiv.org/abs/2510.24882')]:
    req=urllib.request.Request(url,headers={"User-Agent":"openai-proof-research-scout/0.1 (read-only)"})
    b=urllib.request.urlopen(req,timeout=30).read()
    open(f'artifacts/src-{name}-2510.24882.html','wb').write(b)
    print(name,len(b),hashlib.sha256(b).hexdigest()[:12])
    import re
    t=re.search(r'<meta property="og:description" content="([^"]+)"',b.decode('utf8','ignore'))
    print((t.group(1) if t else 'no-abs')[:1500])
