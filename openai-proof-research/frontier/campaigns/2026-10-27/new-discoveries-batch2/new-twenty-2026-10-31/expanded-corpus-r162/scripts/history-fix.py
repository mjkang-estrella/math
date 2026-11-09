import pathlib,json,re
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'reservation.json').read_text())
rx=re.compile(r'\b(?:'+'|'.join(map(str,r['ids']))+r')\b')
titles=[x['title'].casefold() for x in r['rows']]
hits=[]
for line in (D/'history-matches.txt').read_text().splitlines():
 if rx.search(line) or any(t in line.casefold() for t in titles):hits.append(line)
(D/'history-bounded.txt').write_text('\n'.join(hits)+'\n')
(D/'scripts/history-ids.txt').write_text('\n'.join(r'\b'+str(i)+r'\b' for i in r['ids']))
(D/'scripts/history-titles.txt').write_text('\n'.join(x['title'] for x in r['rows']))
print('historical exact ID/title hits',len(hits))
for line in hits:print(line[:1500])
