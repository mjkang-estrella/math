exec(open(__file__.replace('fetch_last.py','fetch_review.py')).read().split('jobs=')[0])
from urllib.parse import quote
jobs={'openalex-exact-redundant':'https://api.openalex.org/works?per-page=8&search='+quote('"distance-redundant"'), 'openalex-diameter-product':'https://api.openalex.org/works?per-page=4&search='+quote('diameter direct product graphs')}
exec('def get'+open(__file__.replace('fetch_last.py','fetch_review.py')).read().split('def get')[1])
