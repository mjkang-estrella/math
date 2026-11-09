from fetch import get
import concurrent.futures
urls={
'later-v1':'https://arxiv.org/html/2507.14568v1',
'openalex-title':'https://api.openalex.org/works?search=Some%20results%20on%20sigma_t-irregularity&per-page=10',
'bell-metadata':'https://api.openalex.org/works?search=Bell%20A%20note%20on%20the%20irregularity%20of%20graphs&per-page=5',
'omega-tree-live':'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/3ca0ba6c579f2685c52d95a4a6b8a07d037382c9?recursive=1',
'arxiv-related':'https://export.arxiv.org/api/query?search_query=all:%222411.04881%22&max_results=50',
'gap-search':'https://api.openalex.org/works?search=triangle-free%20Zagreb%20strict%20bound&per-page=10',
}
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as e:
 for r in e.map(get,urls.items()):print(r,flush=True)
