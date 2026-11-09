import pathlib,re,json
L=pathlib.Path(__file__).resolve().parent
spec={322120:r'λ.*?past',322219:r'Conjecture 3\.4 The',322548:r'Theorem 1\.3 \.',323487:r'Conjecture 1 \(',323660:r'Conjecture\s*\.',323809:r'α>0|alpha>0|Lackenby',323829:r'Conjecture 11 \.',324316:r'blocking number 2',323760:r'Theorem 4',323759:r'Theorem 4', 'ascent-successor':r'Theorem 3\.3','planar-successor':r'Theorem 1 \.', 'sensitivity-successor':r'Theorem 1\.4','123-successor':r'Theorem 1'}
out=[]
for i,k in spec.items():
 s=(L/'sources'/f'{i}.txt').read_text();m=re.search(k,s)
 if m:j=m.start()
 else:
  print(i,'MATCH FAILED',k);continue
 text=s[max(0,j-130):j+1300];print('\n',i,'OFFSET',j,text);out.append(dict(id=i,path=f'sources/{i}.txt',start=max(0,j-130),end=j+1300,passage=text))
(L/'supplement-passages.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
