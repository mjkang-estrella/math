exec(open(__file__.replace('fetch_followup.py','fetch_review.py')).read().split('jobs=')[0])
from urllib.parse import quote
jobs={'omega-D5':'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/0eb158c0c595bfb991e61a48d6b3521abd2aa0c7?recursive=1','distance-critical-2025':'https://link.springer.com/content/pdf/10.1007/s00373-025-02943-4.pdf','openalex-product':'https://api.openalex.org/works?per-page=8&search='+quote('distance redundant direct product graphs'), 'openalex-2025':'https://api.openalex.org/works/https://doi.org/10.1007/s00373-025-02943-4'}
exec('def get'+open(__file__.replace('fetch_followup.py','fetch_review.py')).read().split('def get')[1])
