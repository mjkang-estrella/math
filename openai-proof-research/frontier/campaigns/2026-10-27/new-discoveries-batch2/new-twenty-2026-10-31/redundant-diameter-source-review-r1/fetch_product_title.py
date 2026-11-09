exec(open(__file__.replace('fetch_product_title.py','fetch_review.py')).read().split('jobs=')[0])
jobs={'openalex-product-title':'https://api.openalex.org/works?per-page=5&filter=title.search:diameter%20direct%20product%20graphs'}
exec('def get'+open(__file__.replace('fetch_product_title.py','fetch_review.py')).read().split('def get')[1])
