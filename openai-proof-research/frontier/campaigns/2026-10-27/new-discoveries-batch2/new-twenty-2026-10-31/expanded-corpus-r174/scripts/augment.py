import pathlib,json,re,hashlib
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r174')
d=json.loads((L/'outputs/intake.json').read_text());reg=json.loads((L/'outputs/registry-screen.json').read_text())
terms={361653:['Guan','Ramos','FI-graph'],361990:['Bailey','Brown','Snyder','Turner','tropical','dot product'],362118:['Meier','Shi','Zeng','transchromatic'],362188:['Folsom','Homma','Ryu','Tong','Zmija','ary partition'],362279:['Defant','Foster','Propp','benzel'],362478:['Kawai','Ferreira','alternative division'],371333:['Aubian','Ibiapina','Kuffner','Naserasr','Pujol','Robin','Zhou','Gyárfás'],371334:['balanced chromatic','Gyárfás'],371465:['Umans','Wang','divisor'],371714:['Zhang','Tian','Steiner'],371808:['Bui','Rosenfeld','square-free'],371811:['Baril','Couceiro','Lagerkvist','semiring'],371851:['Louf','Barnette'],372089:['Sahasrabudhe','Beck','Fiala'],372147:['Costa','Luu','Wood','Yip','diameter'],372151:['Esperet','Hendrey','Lagoutte','Marseloo','Norin','Steiner','flow reconfiguration'],372160:['Kanungo','sequence saturation'],372766:['Haag','Samanta','Swisher','Treneer','Visser','colored partition'],373304:['Shen','Carnero','total cut'],374736:['Kang','Nikiforov','Yuan','Liu','Luo','chromatic hypergraph']}
texts={str(p.relative_to(L)):p.read_text(errors='replace') for p in [L/'sources/leanpool-projects.yml',*list((L/'sources').glob('pool-*'))]}
for i,ts in terms.items():
 reg['by_id'][str(i)]['author_keyword_screen']={'terms':ts,'hits':{term:[{'path':p,'snippet':s[max(0,z.start()-90):z.end()+130]} for p,s in texts.items() for z in list(re.finditer(re.escape(term),s,re.I))[:2]] for term in ts}}
reg['known_exact_exclusion']={'371714':{'path':'sources/ZhangTianSteinerTreeRadius.lean','declaration':'D5.S3.Combinatorics.Graph.Eccentric.ZhangTianSteinerTreeRadius.result','body_read':'definitions of steinerDist, steinerRadius, claim and result; pointwise counting proof inspected; no local kernel replay of upstream proof','sha256':hashlib.sha256((L/'sources/ZhangTianSteinerTreeRadius.lean').read_bytes()).hexdigest()}}
(L/'outputs/registry-screen.json').write_text(json.dumps(reg,indent=2))
# concise contextual inherited families
out={}
for p in (L/'outputs').glob('context-*.json'):
 x=json.loads(p.read_text());out[p.name]={k:x[k] for k in ['accepted','excluded','excluded_after_review','held_candidates'] if k in x}
(L/'outputs/inherited-families.json').write_text(json.dumps(out,indent=2))
print('author/keyword screens retained; ambiguous surname hits are not exclusions')
