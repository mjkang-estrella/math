import runpy,pathlib,concurrent.futures,json
r=pathlib.Path(__file__).resolve().parent
# Reuse bounded HTTP helper without running its main block.
s=(r/'fetch.py').read_text().split('mode=sys.argv')[0];ns={"__file__":str(r/"fetch.py")};exec(compile(s,str(r/'fetch.py'),'exec'),ns)
jobs=[
('journal-370439.html','https://www.sciencedirect.com/science/article/pii/S0166218X26001204'),
('journal-381125.html','https://www.sciencedirect.com/science/article/pii/S0925772113000412'),
('author-337975.pdf','https://pageperso.lis-lab.fr/kolja.knauer/NL_extensionsubmit.pdf'),
('prior-grid.html','https://probxiv.com/problems/grid-drawings-and-the-chromatic-number'),
('registry-openai-head.html','https://github.com/openai/math'),
('registry-openai-contents.md','https://raw.githubusercontent.com/openai/math/HEAD/CONTENTS.md'),
('registry-leanpool-projects.yml','https://raw.githubusercontent.com/leanprover-community/leanprover-community.github.io/HEAD/data/projects.yml'),
('registry-truth.html','https://www.trureturing.org/conjectures'),
('343137-companion.abs.html','https://arxiv.org/abs/1306.5970'),
('374916-companion1.abs.html','https://arxiv.org/abs/2507.00515'),
('374916-companion2.abs.html','https://arxiv.org/abs/2003.10161'),
('citing-removal.abs.html','https://arxiv.org/abs/2609.20237'),
('citing-precolor.abs.html','https://arxiv.org/abs/2310.09973'),
('older-rainbow.pdf','https://www.renyi.hu/~gyarfas/Cikkek/136_orthogonal.pdf')]
receipts=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 for rec in pool.map(ns['get'],jobs): receipts.append(rec);print(json.dumps(rec),flush=True)
(r/'receipts-extra.json').write_text(json.dumps(receipts,indent=2)+'\n')
