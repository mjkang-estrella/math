import pathlib,json,hashlib,re
D=pathlib.Path(__file__).resolve().parents[1];B=D.parent
x=json.loads((D/'extracted.json').read_text());l=json.loads((B/'ledger.json').read_text())
(D/'ledger-read-summary.json').write_text(json.dumps({'sha256':hashlib.sha256((B/'ledger.json').read_bytes()).hexdigest(),'accepted':l.get('accepted'),'excluded':l.get('excluded_after_review')},indent=2))
# Drop unrelated embedded integers/hashes from history matches.
lines=(D/'history-matches.txt').read_text().splitlines();ids='|'.join(x)
lines=[s for s in lines if re.search(r'(?<![0-9a-f])(?:'+ids+r')(?![0-9a-f])',s) or any(o['title'].lower() in s.lower() for o in x.values())]
(D/'history-filtered.txt').write_text('\n'.join(s[:1800] for s in lines)+'\n')
todo=[(o['source_url'],i+'-abs') for i,o in x.items()]
todo += [('https://api.github.com/repos/'+r+'/commits/HEAD',k+'-head') for k,r in [('leanpool','Vilin97/lean-pool'),('openai','openai/math'),('omega','the-omega-institute/trureturing')]]
(D/'fetch-abs.json').write_text(json.dumps(todo))
