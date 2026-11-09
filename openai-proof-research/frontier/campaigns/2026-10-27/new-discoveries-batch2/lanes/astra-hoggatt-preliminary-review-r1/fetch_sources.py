"""Read-only public source retrieval; writes only this review lane, no retries."""
from pathlib import Path
import urllib.request, json, hashlib, datetime
from html.parser import HTMLParser

class Text(HTMLParser):
    def __init__(self):
        super().__init__(); self.parts=[]; self.inmath=0
    def handle_starttag(self, tag, attrs):
        if tag=='math':
            self.parts.append(dict(attrs).get('alttext','')); self.inmath+=1
        elif tag in ('p','div','section','h1','h2','h3','h4','h5','h6','li','tr') and not self.inmath:
            self.parts.append('\n')
    def handle_endtag(self,tag):
        if tag=='math':self.inmath-=1
    def handle_data(self,data):
        if not self.inmath:self.parts.append(data)

LANE = Path(__file__).resolve().parent
OUT = LANE / 'sources'
OUT.mkdir(exist_ok=True)
targets = [
 ('fzz-abs.html', 'https://arxiv.org/abs/2505.05873'),
 ('fzz.html', 'https://arxiv.org/html/2505.05873v1'),
 ('lamprecht-abs.html', 'https://arxiv.org/abs/1210.1102'),
 ('lamprecht.html', 'https://arxiv.org/html/1210.1102v1'),
 ('leake-ryder-abs.html', 'https://arxiv.org/abs/1712.02499'),
 ('qconvolution-abs.html', 'https://arxiv.org/abs/2606.15003'),
 ('mathdb-368343.json', 'https://mathdb.com/api/posts/368343'),
 ('realrooted-1332-comments.json', 'https://api.github.com/repos/PerAlexandersson/RealRooted/issues/1332/comments?per_page=100'),
]
records = []
for name,url in targets:
    rec = dict(file=name,url=url,accessed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    try:
        req = urllib.request.Request(url, headers={'User-Agent':'Mathematical-Source-Review/1.0'})
        with urllib.request.urlopen(req, timeout=15) as response:
            data=response.read();rec.update(status=response.status, final_url=response.url,sha256=hashlib.sha256(data).hexdigest())
        (OUT/name).write_bytes(data)
        if name.endswith('.html'):
            parser=Text();parser.feed(data.decode('utf-8'))
            (OUT/(name[:-5]+'.txt')).write_text(''.join(parser.parts), encoding='utf-8')
    except Exception as error:
        rec['error']=str(error)
    records.append(rec)
    print(name,rec.get('status',rec.get('error')),flush=True)
    (LANE/'retrieval-manifest.json').write_text(json.dumps(records,indent=2)+'\n')
