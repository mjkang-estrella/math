from retrieve import get,L
import urllib.parse
get('https://pages.uoregon.edu/mbownik/papers/','bownik-index.html')
get('https://www.impan.pl/en/publishing-house/journals-and-series/studia-mathematica/all/159/3/86241/frame-wavelets-and-spectral-properties-of-shift-invariant-spaces','impan.html')
get('https://export.arxiv.org/api/query?search_query='+urllib.parse.quote('au:Bownik AND (all:frame OR all:wavelet)')+'&max_results=35&sortBy=submittedDate&sortOrder=descending','wavelet-current.xml')
