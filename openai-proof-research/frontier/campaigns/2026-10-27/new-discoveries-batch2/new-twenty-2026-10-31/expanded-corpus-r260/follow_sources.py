import runpy,pathlib,re,json
L=pathlib.Path(__file__).resolve().parent
# Load helpers without invoking the initial collection again.
s=(L/'fetch_sources.py').read_text().split('items=[]')[0];g={'__file__':str(L/'fetch_sources.py')};exec(compile(s,str(L/'fetch_sources.py'),'exec'),g)
items=[];inventory={}
for f in sorted((L/'sources').glob('*.abs.html')):
 a=f.name.split('.abs')[0];versions=sorted(set(re.findall(r'\[v(\d+)\]',f.read_text())),key=int);inventory[a]=versions
 for v in versions:items.append((a+'v'+v+'.pdf','https://arxiv.org/pdf/'+a+'v'+v))
(L/'version-inventory.json').write_text(json.dumps(inventory,indent=2))
items.extend([
('pirates-2017.pdf','https://math.colgate.edu/~integers/rg3/rg3.pdf'),
('pirates-journal.pdf','https://math.colgate.edu/~integers/ng3/ng3.pdf'),
('swanepoel-journal-author.pdf','https://researchonline.lse.ac.uk/id/eprint/59891/1/__lse.ac.uk_storage_LIBRARY_Secondary_libfile_shared_repository_Content_Swanepoel%2C%20K_Swanepoel_Set_Unit_Vectors_Swanepoel_Set_Unit_Vectors_2014.pdf'),
('shnol.pdf','https://arxiv.org/pdf/1706.04869'),('gauss-later.pdf','https://arxiv.org/pdf/2108.04148'),('cry-typeC.pdf','https://arxiv.org/pdf/1704.02701'),('cry-typeD.pdf','https://arxiv.org/pdf/1407.3467'),
('openai-HEAD-README.md','https://raw.githubusercontent.com/openai/math/HEAD/README.md'),('omega-HEAD-README.md','https://raw.githubusercontent.com/the-omega-institute/trureturing/HEAD/README.md'),('leanpool-projects.yml','https://raw.githubusercontent.com/Vilin97/lean-pool/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/projects.yml'),('leanpool-root-projects.yml','https://raw.githubusercontent.com/Vilin97/lean-pool/01db1d7049cf9668bda1e9e106875ee1278b43e6/projects.yml')])
with g['concurrent'].futures.ThreadPoolExecutor(max_workers=2) as e:list(e.map(g['fetch'],items))
