exec(open(__file__.replace('more.py','fetch.py')).read().split('rows=list')[0])
items=[('mellin','https://arxiv.org/pdf/1512.01490'),('plucker-recursion','https://arxiv.org/pdf/2312.06430')]
rows=list(ThreadPoolExecutor(max_workers=2).map(fetch,items));(out/'more-receipts.json').write_text(json.dumps(rows,indent=2));print(rows)
