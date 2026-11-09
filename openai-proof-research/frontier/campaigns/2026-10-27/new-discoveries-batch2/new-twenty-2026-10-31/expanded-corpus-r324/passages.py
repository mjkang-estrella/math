from html.parser import HTMLParser
exec((P/'read.py').read_text().split('for l in')[0])
for l in (P/'http-receipts.jsonl').read_text().splitlines():
 r=json.loads(l)
 if 'file' not in r or 'arxiv.org/html' not in r['url']:continue
 if len(sys.argv)>2 and sys.argv[2] not in r['url']:continue
 f=P/r['file'];parser=Text();parser.feed(f.read_text());t=''.join(parser.parts);f.with_suffix('.txt').write_text(t)
 import re
 print('\nURL',r['url'])
 if len(sys.argv)>3:
  pos=t.lower().find(sys.argv[3].lower());print(t[max(0,pos-100):pos+int(sys.argv[4])]);continue
 for m in list(re.finditer(r'Conjecture\s+\d',t))[-3:]:print(t[max(0,m.start()-60):m.start()+1700])
