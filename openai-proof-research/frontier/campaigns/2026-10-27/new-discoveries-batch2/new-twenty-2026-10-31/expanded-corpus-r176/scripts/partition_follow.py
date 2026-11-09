import sys,pathlib
exec((pathlib.Path(__file__).parent/'fetch.py').read_text())
if mode=='partition':
 a='2503.12583';get('https://arxiv.org/abs/'+a,a+'-abs.html');get('https://arxiv.org/html/'+a,a+'-body.html')
