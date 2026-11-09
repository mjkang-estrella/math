from fetch import get
items=[('omega-root-tree.json', 'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/4c7a89d97001d86901a192a7d002be32def54ac3'), ('0507308.html', 'https://arxiv.org/html/math/0507308'), ('0607326.html', 'https://arxiv.org/html/math/0607326'), ('0608109.html', 'https://arxiv.org/html/math/0608109'), ('0701553.html', 'https://arxiv.org/html/math/0701553'), ('2211.00738.html', 'https://arxiv.org/html/2211.00738'), ('0304058.html', 'https://arxiv.org/html/math/0304058')]
for i in items: print(get(i),flush=True)
