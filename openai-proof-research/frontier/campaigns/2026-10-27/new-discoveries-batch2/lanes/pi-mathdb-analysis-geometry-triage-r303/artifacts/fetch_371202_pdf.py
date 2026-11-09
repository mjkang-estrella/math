import urllib.request,hashlib
req=urllib.request.Request('https://arxiv.org/pdf/2510.24882',headers={"User-Agent":"openai-proof-research-scout/0.1 (read-only)"})
b=urllib.request.urlopen(req,timeout=60).read()
open('artifacts/src-2510.24882.pdf','wb').write(b)
print(len(b), hashlib.sha256(b).hexdigest())
