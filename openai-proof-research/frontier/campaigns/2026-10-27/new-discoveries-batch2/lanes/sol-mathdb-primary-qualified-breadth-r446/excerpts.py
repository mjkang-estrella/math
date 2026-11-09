import pathlib,json
R=pathlib.Path(__file__).resolve().parent
sel={'owr2018-50':[28,34,39,46],'owr2019-13':[55,56],'owr2019-19':[20,43,62,68],'owr2019-27':[43],'owr2019-39':[26,27],'owr2019-47':[24,25]}
out=[]
for n,pages in sel.items():
 s=(R/'sources'/f'{n}.txt').read_text().split('\f')
 for p in pages:out.append({'file':f'sources/{n}.txt','pdf_page':p,'text':s[p-1]})
(R/'source-excerpts.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
for e in out:print('\n====',e['file'],e['pdf_page'],'====\n',e['text'])
