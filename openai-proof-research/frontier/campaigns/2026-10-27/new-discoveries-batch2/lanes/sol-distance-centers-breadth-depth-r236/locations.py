from research import *
print(fetch('https://api.openalex.org/works/https://doi.org/10.12775/TMNA.2023.023','openalex.json'))
print(fetch('https://api.crossref.org/works/10.12775/TMNA.2023.023','crossref.json'))
print(fetch('https://arxiv.org/search/?query=%22center+of+distances%22&searchtype=title','arxiv-title.html'))
