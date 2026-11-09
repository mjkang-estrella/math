from fetch import get
items=[('2609.30201.html','https://arxiv.org/html/2609.30201'),('2102.12830.html','https://arxiv.org/html/2102.12830'),('precolor-probxiv.html','https://probxiv.com/problems/extending-partial-edge-colorings-of-cartesian-products-of-graphs')]
for x in items:print(get(x))
