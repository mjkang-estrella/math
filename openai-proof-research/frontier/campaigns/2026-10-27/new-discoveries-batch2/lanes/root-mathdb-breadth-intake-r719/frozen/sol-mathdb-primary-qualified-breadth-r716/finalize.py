import pathlib,json
P=pathlib.Path(__file__).resolve().parent
p=P/'source-provenance.json';d=json.loads(p.read_text())
for s in d:
 s['coverage']='selected primary definitions/question and source-internal result passages only; no whole-body or full-dependency audit'
 if s['arxiv']=='2510.09219':s['coverage']='v1 exact Conjecture1 passage' if s['version']==1 else 'v2 successor Theorems5.10/5.11 and actual target-producing proof passage; underlying2019 proof unread'
 s['body_locators']='source-coverage.json';s['fetch_method']='standard-library urllib; generic Python-urllib/3 User-Agent; no Referer or private headers'
p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
