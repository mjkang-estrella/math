import sys,pathlib,json
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import fetch,L
for r in json.loads((L/'reservation.json').read_text())['rows']:fetch(r['source_url'],str(r['mathdb_id'])+'-abs')
fetch('https://arxiv.org/html/2608.09754','pentanomial-resolution')
