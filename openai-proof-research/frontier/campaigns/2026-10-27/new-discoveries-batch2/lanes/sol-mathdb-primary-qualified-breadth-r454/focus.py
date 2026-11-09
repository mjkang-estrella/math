import pathlib,json,re
L=pathlib.Path(__file__).resolve().parent
terms={404452:'lower bound',404479:'Burau',404486:'strict',404489:'orbifold',404501:'well',404552:'probing',404567:'r3',404570:'subsequent discussion',404575:'Woodall',404576:'strengthening',404577:'∆',404579:'Steiner',404587:'self-conjugate',404591:'XY',404592:'global minimum',404620:'convergence',404639:'µ(n)',404661:'second order',404676:'function space',404683:'smoothing',404695:'infinitely',404696:'equiangular',404697:'h(r)',404699:'planar',404726:'minimal decomposition',404733:'optimal constant',404738:'Conjecture',404739:'Conjecture 2',404740:'Conjecture 2',404743:'transitive subgroups',404758:'d5',404778:'backbone',404779:'suborbits',404789:'C1',404790:'log2',404801:'Hilbert series',404825:'homomorphic',404838:'determine',404878:'index',404882:'threshold',404890:'Γ',404891:'factorization',404901:'essential',404902:'essential',404907:'contractible',404933:'counting',404940:'Griesmer',404941:'additive',404947:'Conjecture',404955:'sumset'}
out=[]
for x in json.loads((L/'assigned-records.json').read_text()):
 r=x['record'];p=L/'sources'/(r['source_url'].split('/')[-1]+'.txt')
 if not p.exists():continue
 pages=p.read_text().split('\f');n=int(re.search(r'page (\d+)',r['source_name'])[1]);s='\n'.join(pages[max(0,n-2):n+1]);term=terms[r['mathdb_id']];ms=list(re.finditer(re.escape(term),s,re.I));pos=ms[-1].start() if ms else len(s)//2
 excerpt=s[max(0,pos-800):pos+1800];out.append(dict(id=r['mathdb_id'],source=r['source_url'],pdf_page=n,term=term,located=bool(ms),passage=excerpt,three_page_context=s))
(L/'primary-sections.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
for x in out:print('\nID',x['id'],'LOCATED',x['located'],'\n',x['passage'])
