from research import *
queries={
'magnitude':'ti:"magnitude" AND au:Willerton',
'bunkbed':'ti:"bunkbed" AND au:Linusson',
'stanleydepth':'ti:"Stanley depth" AND au:Herzog AND au:Zheng',
'deltaconjecture':'ti:"Delta conjecture" AND au:Haglund AND au:Wilson',
'neggerstanley':'ti:"Counterexamples" AND au:Branden AND all:"Stanley"',
'rook':'ti:"rook" AND au:Haglund AND all:conjecture',
'shannon':'ti:"Shannon capacity" AND au:Alon',
'turan':'ti:"Turan" AND au:Razborov',
'shuffle-wider':'all:"random-to-random" AND all:conjecture',
}
for key,q in queries.items():fetch(key+'.atom','https://export.arxiv.org/api/query?search_query='+urllib.parse.quote(q)+'&max_results=5&sortBy=submittedDate&sortOrder=ascending')
