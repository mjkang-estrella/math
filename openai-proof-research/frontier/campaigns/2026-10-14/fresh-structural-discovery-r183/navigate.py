import runpy,json,re,hashlib
from pathlib import Path
G=runpy.run_path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r183/guard.py');r=G['ROOT']
pat=re.compile(r'separable.{0,30}quotient|quotient.{0,30}separable|predual|real.valued measur|Saxon|Hagler|Odell.Rosenthal|closed.kernel|\\mathfrak\s*\{?b\}?|strictly singular|James.tree',re.I)
out=[];n=bad=0
for p in G['eligible']('frontier'):
 b=p.read_bytes()
 try:s=b.decode('utf8')
 except UnicodeDecodeError: bad+=1;continue
 n+=1; lines=s.splitlines(keepends=True);off=0;heading=None;hs=0;level=0
 for line in lines:
  m=re.match(r'^(#{1,6})\s+(.*)',line)
  if m: heading=line.strip();hs=off;level=len(m[1])
  if pat.search(line): out.append(dict(path=p.as_posix(),line_byte=off,heading=heading,heading_start=hs,level=level,match=line.strip()))
  off+=len(line.encode())
(r/'private/history-navigation.json').write_text(json.dumps(dict(utf8_files=n,non_utf8=bad,hits=out),indent=2))
print('Eligible UTF8',n,'non-UTF8',bad,'hits',len(out))
for x in out:print(json.dumps(x,ensure_ascii=False))
