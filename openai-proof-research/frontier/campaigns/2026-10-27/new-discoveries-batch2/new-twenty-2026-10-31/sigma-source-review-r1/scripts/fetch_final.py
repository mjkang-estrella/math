from fetch import get
import concurrent.futures
urls={
'bell-body':'https://www.sciencedirect.com/science/article/pii/002437959290004T/pdf',
'citing-list':'https://api.openalex.org/works?filter=cites:W4415114651&per-page=100',
'omega-root-live':'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/3ca0ba6c579f2685c52d95a4a6b8a07d037382c9',
'variance-search':'https://api.openalex.org/works?search=%22degree%20variance%22%20%22triangle%22&per-page=10',
}
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as e:
 for r in e.map(get,urls.items()):print(r,flush=True)
