from fetch import get
for key,url in [('2201.08814.html', 'https://arxiv.org/html/2201.08814'), ('keith2017.html', 'https://arxiv.org/html/1502.02070'), ('partition-journal.html', 'https://link.springer.com/article/10.1007/s11139-026-01419-0')]:
 print(get((key,url)),flush=True)
