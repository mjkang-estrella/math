exec(open('refresh.py').read().split('urls=')[0])
urls={'omega-root':'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/d9854fe46af29589f4c49a5fa65ca44e508663ca','anticode-count':'https://arxiv.org/html/2610.31618v1','linear-anticode':'https://arxiv.org/html/2406.07112v1'}
exec(open('refresh.py').read().split('for name,url in urls.items():')[1].join(['for name,url in urls.items():','']))
