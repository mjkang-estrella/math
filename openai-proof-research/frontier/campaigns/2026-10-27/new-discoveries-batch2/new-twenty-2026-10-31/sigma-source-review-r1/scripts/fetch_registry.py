from fetch import get
import concurrent.futures
urls={
'omega-D5-live':'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/a3b7a6be44c3e997f0a1114cf91862ee2d1db45c?recursive=1',
'omega-Problems-live':'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/0b45ced5e033ab15556c8f7a9177458bc5ad1de6?recursive=1',
'journal':'https://amc-journal.eu/index.php/amc/article/download/3268/2206',
}
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as e:
 for r in e.map(get,urls.items()):print(r,flush=True)
