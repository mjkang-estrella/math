from research import *
ids=['math/9803030v2','2011.11467v1','1210.4605v1']
# Exact source/author aliases before further body investment; no historical body copying.
files=[str(p) for p in L.parent.glob('*/*.md') if p.parent!=L and p.name in ['SUMMARY.md','SCOUTING.md','discovery.md']]
for pattern in ['9803030|Burdzy.*Werner','Leinster.*Willerton','Herzog.*Vladoiu','Haglund.*Remmel.*Wilson','Alon.*Lubetzky','Linusson.*bunkbed','Neggers.Stanley','Fon.der.Flaass']:
 r=subprocess.run(['rg','-il',pattern,*files],capture_output=True,text=True);log('alias-checks.jsonl',dict(pattern=pattern,paths=r.stdout.splitlines(),scope='direct lane top-level reports only, not full historical database'))
for id in ids:
 key=id.replace('/','-')+'.pdf';fetch(key,'https://arxiv.org/pdf/'+id)
 if (L/'primary'/key).exists():extract(L/'primary'/key)
fetch('breadth-current.atom','https://export.arxiv.org/api/query?id_list='+urllib.parse.quote('0908.1582,0811.0949,0712.2308,1509.07058,math/0408312,cs/0608021,1008.4707,math/9803030,2011.11467,1210.4605,1509.08580,2503.17580'))
