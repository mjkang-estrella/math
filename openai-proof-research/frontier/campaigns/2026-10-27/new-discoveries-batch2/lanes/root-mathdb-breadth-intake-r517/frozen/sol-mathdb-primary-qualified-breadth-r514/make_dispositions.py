import pathlib,json
P=pathlib.Path(__file__).resolve().parent
notes={}
for line in (P/'notes.tsv').read_text().splitlines():
 i,d,n=line.split('\t',2);notes[int(i)]=(d,n)
a=json.loads((P/'assigned-records.json').read_text());assert len(notes)==len(a)==50
out=[]
passages={357943:('2304.00742v2','450-468; theorem/construction context 82-98'),358938:('2306.15702v1','46-52,280-309'),359377:('2308.01685v1','35-75,178-262,300-320'),358439:('2305.10560v4','125-150,620-630; 2305.10828v3:28-80,159-180,270-327; 2310.07926v6:128-169,485-510')}
for r in a:
 i=r['mathdb_id'];d,n=notes[i]
 x={k:v for k,v in r.items() if k!='record'};x.update(title=r['record']['title'],source_url=r['record']['source_url'],source_name=r['record']['source_name'],disposition=d,technical_reason=n,accepted_credit=0,literal_statement_read=True,primary_passage=passages.get(i),whole_body_read=False,full_dependency_audit=False,current_registry_cleared=False,novelty_pass=False,local_proof='No new candidate proof; rejected wording diagnostics only' if i in [357943,358938,359377] else 'none',primary_body_coverage='selected passages' if i in passages else 'not read')
 out.append(x)
(P/'dispositions.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');(P/'proposals.json').write_text('[]\n')
