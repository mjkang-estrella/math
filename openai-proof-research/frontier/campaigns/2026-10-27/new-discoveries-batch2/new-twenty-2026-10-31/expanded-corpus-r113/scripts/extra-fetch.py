from fetch import get
for key,url in [('stamps-v2.html','https://arxiv.org/html/2503.23661v2')]:print(get((key,url)),flush=True)
