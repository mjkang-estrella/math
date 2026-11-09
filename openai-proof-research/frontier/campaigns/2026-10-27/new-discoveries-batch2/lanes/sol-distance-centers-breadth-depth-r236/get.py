from research import *
import sys
for url,name in [
 ('https://doi.org/10.12775/TMNA.2023.023','tmna-landing.html'),
 ('https://arxiv.org/abs/2512.17285','survey-current.html'),
 ('https://arxiv.org/pdf/2512.17285v1','survey.pdf'),
 ('https://arxiv.org/search/?query=%22center+of+distances%22&searchtype=all','arxiv-centers.html'),
 ('https://www.google.com/search?q=%22operator+of+center+of+distances%22','search-tmna.html')]:
 print(fetch(url,name))
