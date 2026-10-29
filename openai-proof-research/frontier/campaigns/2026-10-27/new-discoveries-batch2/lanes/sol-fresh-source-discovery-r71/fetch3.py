exec(open('fetch.py').read().split('urls=')[0])
urls={'kmo-v2.html':'https://arxiv.org/html/2501.06415v2','aims.html':'https://www.aimspress.com/article/doi/10.3934/math.20261151'}
exec('rows=[]'+open('fetch.py').read().split('rows=[]')[1].replace("(root/'sources/fetch.json')","(root/'sources/fetch3.json')"))
