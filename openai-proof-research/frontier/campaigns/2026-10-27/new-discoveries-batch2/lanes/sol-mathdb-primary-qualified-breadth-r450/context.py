import pathlib,json
L=pathlib.Path(__file__).resolve().parent
select={'7155451':[19,20],'4990374':[48,60],'8415356':[24],'8415359':[14],'8415360':[9,10],'9790365':[22],'9790367':[13,17,18],'10252928':[38,39],'10252929':[36]}
out=[]
for f,ns in select.items():
 pages=(L/'sources'/('ems-'+f+'.txt')).read_text().split('\f')
 for n in ns:
  t=pages[n-1];out.append({'source':f,'pdf_page':n,'text':t});print('\nSOURCE',f,'PAGE',n,'\n',t)
(L/'additional-sections.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
