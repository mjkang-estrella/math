import pathlib,re,json
L=pathlib.Path(__file__).resolve().parent
keys={322120:'past',322219:'Conjecture 3.4',322250:'Conjecture 1 (',322282:'Conjecture 3.1',322333:'Conjecture 5.1',322356:'Conjecture 1.6',322402:'Conjecture 12.5',322454:'Conjecture 1.4',322548:'Theorem 1.3',322562:'Conjecture 6.4',322572:'Conjecture 4.1',322584:'Conjecture 6.9',322607:'Conjecture 1.3',322611:'Conjecture 2.4',322646:'Conjecture 9',322663:'Conjecture 1.4',322702:'Conjecture 1 .',323063:'Conjecture 1.1',323126:'Conjecture 2.1',323140:'Conjecture 2.5',323178:'Conjecture 3 (',323232:'Conjecture 5.4',323301:'Conjecture 5.1',323303:'Conjecture 1 l',323347:'Conjecture 1 .',323487:'Conjecture 1 .',323515:'Conjecture 1.1',323550:'Conjecture 5.1',323626:'Conjecture 1 .',323627:'Conjecture 1.2',323639:'Conjecture 3 .',323660:'Conjecture 1',323693:'Conjecture 1 .',323759:'Conjecture 1 .',323760:'Theorem 4.1',323809:'Conjecture 1',323822:'Conjecture 2 (',323829:'Conjecture 1',323850:'Conjecture 1',324031:'Conjecture 1',324305:'Conjecture 1 (',324316:'Conjecture 1',324344:'Conjecture 1.4',324362:'Conjecture 5.10',324390:'Conjecture 1.3',324431:'Conjecture 12',324452:'Conjecture 2.3',324496:'Our second conjecture',324568:'Conjecture 2 .',324569:'Conjecture 3 .'}
out=[]
for i,k in keys.items():
 s=(L/'sources'/f'{i}.txt').read_text();j=s.find(k)
 if j<0:
  ms=list(re.finditer('conjecture',s,re.I));j=ms[-1].start() if ms else 0
 out.append(dict(id=i,path=f'sources/{i}.txt',start=j,end=min(j+1100,len(s)),key=k,key_found=k in s,passage=s[j:j+1100]))
 print(i,'exact' if k in s else 'FALLBACK',s[j:j+500])
(L/'target-passages.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
