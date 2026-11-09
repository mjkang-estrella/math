import sys,pathlib
sys.path.insert(0,str(pathlib.Path(sys.argv[1])/'scripts'));from fetch import fetch
for url,label in [('https://arxiv.org/abs/2404.12204','saturation-new-abs'),('https://arxiv.org/html/2404.12204','saturation-new-body'),('https://arxiv.org/html/2503.18409','factor-original-body')]:fetch(url,label)
