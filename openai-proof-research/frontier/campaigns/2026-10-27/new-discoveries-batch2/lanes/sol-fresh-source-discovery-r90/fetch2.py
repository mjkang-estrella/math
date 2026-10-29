exec(open(__file__.replace('fetch2.py','fetch.py')).read().split('urls=')[0])
urls={
'mmpp.html':'https://arxiv.org/html/1905.01736v1',
'mmpp-published.html':'https://www.cambridge.org/core/journals/anziam-journal/article/stationary-markovian-arrival-processes-results-and-open-problems/B037C27C281FB3B22AA591EEB0B5CF99',
'he.html':'https://www.cambridge.org/core/journals/journal-of-applied-probability/article/bounds-on-the-mean-and-squared-coefficient-of-variation-of-phasetype-distributions/7C9F1F0FAF437475C9041F9EE7B5309A',
'withdrawn.html':'https://arxiv.org/html/1802.08400'}
exec(open(__file__.replace('fetch2.py','fetch.py')).read().split('r=[]')[1].replace("(b/'http.json')","(b/'http2.json')").join(['r=[]','']))
