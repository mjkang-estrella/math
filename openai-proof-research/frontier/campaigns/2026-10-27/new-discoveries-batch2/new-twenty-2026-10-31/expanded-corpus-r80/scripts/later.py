from fetch import get
for key,url in [('2609.12951.html', 'https://arxiv.org/html/2609.12951'), ('2604.25394.html', 'https://arxiv.org/html/2604.25394'), ('keith2016.pdf', 'https://pages.mtu.edu/~wjkeith/CombinatoricsSeminar/ComSmrFall2016.pdf'), ('hurlbert-pubs.html', 'https://glennhurlbert.github.io/pubs.html'), ('sopp-head.json', 'https://api.github.com/repos/sorenson64/sopp/commits/HEAD')]:
 print(get((key,url)),flush=True)
