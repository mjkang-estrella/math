import sys,pathlib,json,re
exec((pathlib.Path(__file__).parent/'fetch.py').read_text())
if mode=='primary':
 for a in ['2601.04514','2505.21989','2503.12144']:
  get('https://arxiv.org/abs/'+a,a+'-abs.html');get('https://arxiv.org/html/'+a,a+'-body.html')
