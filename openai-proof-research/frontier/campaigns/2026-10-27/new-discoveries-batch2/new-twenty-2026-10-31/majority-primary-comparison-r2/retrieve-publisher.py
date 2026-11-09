exec(open(__file__.replace('retrieve-publisher.py','retrieve.py')).read().split('a=list(')[0])
jobs=[('greedy-publisher','https://www.sciencedirect.com/science/article/pii/S157252861100017X'),('directed-publisher','https://www.sciencedirect.com/science/article/pii/S0166218X12000054')]
a=list(concurrent.futures.ThreadPoolExecutor(max_workers=2).map(fetch,jobs));(P/'publisher-receipts.json').write_text(json.dumps(a,indent=2)); print(json.dumps(a,indent=2))
