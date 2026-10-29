exec(open('fetch.py').read().split('urls=')[0])
urls={'aims.pdf':'https://www.aimspress.com/aimspress-data/math/2026/9/PDF/math-11-09-1151.pdf'}
exec('rows=[]'+open('fetch.py').read().split('rows=[]')[1].replace("(root/'sources/fetch.json')","(root/'sources/fetch4.json')"))
