from fetch import *
todo=[('loop-journals.html','https://www.cs.du.edu/~petr/in_research_journals.html'),('loop-share-author.pdf','https://cs.du.edu/~petr/data/papers/Moufang_loops_that_share_associator.pdf'),('cli-supplement.pdf','https://proceedings.neurips.cc/paper_files/paper/2020/file/eea5d933e9dce59c7dd0f6532f9ea81b-Supplemental.pdf'),('stable-ranks-correct.pdf','https://arxiv.org/pdf/0806.3109'),('hopf-later.pdf','https://arxiv.org/pdf/2212.06547'),('window-paper.pdf','https://github.com/ipitchford/sharp-shannon-window-law/releases/download/v1.0.0-candidate/sharp-shannon-window-law-1.0.0-candidate.pdf')]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for v in ex.map(get,todo):print(v,flush=True)
