import pathlib,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
urls={'tree-counterexample':'https://pisrt.org/psr-press/journals/odam/04-vol-5-2022-issue-3/on-the-largest-real-root-of-the-independence-polynomial-of-a-unicyclic-graph/','star-proof-pdf':'https://www.ias.edu/sites/default/files/math/csdm/12-13/hhuang_on_the_maximum_induced_density_of_directed_stars.pdf','mixing-proof-pdf':'https://arxiv.org/pdf/2008.12185','subtraction-survey-pdf':'https://library.slmath.org/books/Book71/files/GONC6-02.pdf','mixing-vor-pdf':'https://wrap.warwick.ac.uk/id/eprint/104251/1/WRAP-mixing-homomorphisms-circular-precolorings-Noel-2015.pdf'}
for n,u in urls.items():subprocess.run(['python3','-I',str(D/'scripts/fetch.py'),n,u],check=True)
