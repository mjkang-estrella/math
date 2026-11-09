import re
for l in (P/'http-receipts.jsonl').read_text().splitlines():
 r=json.loads(l)
 if sys.argv[2] not in r['url'] or 'file' not in r:continue
 t=(P/r['file']).read_text();print(r['url'])
 if 'github' in r['url']:print(sorted(set(re.findall(r'href="([^"]+)"',t)))[:180])
 else:
  parser_text=(P/r['file']).with_suffix('.txt').read_text()
  pos=parser_text.lower().find(sys.argv[3].lower());print(parser_text[max(0,pos-150):pos+6500])
