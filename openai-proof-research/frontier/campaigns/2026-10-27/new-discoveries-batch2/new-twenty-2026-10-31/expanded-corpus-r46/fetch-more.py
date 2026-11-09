exec(open(__file__.replace('fetch-more.py','fetch.py')).read().split('urls=')[0])
urls={'2406.00243':'https://arxiv.org/pdf/2406.00243','drury-original':'https://files.ele-math.com/articles/mia-21-37.pdf','openai-contents':'https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/CONTENTS.md'}
exec(open(__file__.replace('fetch-more.py','fetch.py')).read().split('def fetch')[1].join(['def fetch','']).split('with concurrent.futures')[0])
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:list(ex.map(lambda kv:fetch(*kv),urls.items()))
