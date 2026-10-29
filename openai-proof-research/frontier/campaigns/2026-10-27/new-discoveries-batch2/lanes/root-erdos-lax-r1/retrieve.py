import concurrent.futures, datetime, hashlib, json, pathlib, urllib.request

BASE = pathlib.Path(__file__).resolve().parent
URLS = {
    'rubin-thesis.pdf': 'https://lucris.lub.lu.se/ws/portalfiles/portal/197481927/Avhandling_Olof_Rubin_LUCRIS-2.pdf',
    'arxiv-abs.html': 'https://arxiv.org/abs/2309.02047',
    'omega-head.json': 'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD',
    'openai-head.json': 'https://api.github.com/repos/openai/math/commits/HEAD',
    'publisher.html': 'https://www.sciencedirect.com/science/article/pii/S0021904524000340',
}

def fetch(item):
    name, url = item
    record = {'url':url, 'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        req=urllib.request.Request(url, headers={'User-Agent':'Research source verification'})
        with urllib.request.urlopen(req,timeout=45) as response:
            data=response.read(); record.update(status=response.status, final_url=response.url)
        if name.endswith('.pdf') and not data.startswith(b'%PDF'):
            raise ValueError('Response is not a PDF')
        (BASE/'sources'/name).write_bytes(data)
        record.update(path='sources/'+name,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
    except Exception as exc:
        record['error']=str(exc)
    return record

if __name__=='__main__':
    with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool:
        records=list(pool.map(fetch,URLS.items()))
    (BASE/'retrieval.json').write_text(json.dumps(records,indent=2)+'\n')
    print(json.dumps(records,indent=2))
