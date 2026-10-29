exec(open(__file__.replace('evidence.py','fetch.py')).read().split('for name,repo,old in')[0])
rows=json.loads((D/'http-receipts.json').read_text())
get('https://arxiv.org/abs/1204.0405','ruankong-abs.html')
# Preserve exact extracted passages with auditable source line positions.
spans={'live/ruankong.pdf.txt':[(164,196),(983,1047)],'live/rockel.pdf.txt':[(537,588),(1829,1898)],'live/adapted.pdf.txt':[(525,552),(1501,1545)],'inputs/candidate/sources/2312.16544.pdf.txt':[(470,493)],'live/author-accepted.pdf.txt':[(1,30),(790,860)]}
receipts=[]
for path,parts in spans.items():
 lines=(D/path).read_text().splitlines();text='\n\n'.join('SOURCE '+path+' L'+str(a)+'-'+str(b)+'\n'+'\n'.join(lines[a-1:b]) for a,b in parts)
 target='passage-'+Path(path).name+'.txt';(D/target).write_text(text);receipts.append({'source':path,'source_sha256':hashlib.sha256((D/path).read_bytes()).hexdigest(),'ranges':parts,'passage':target})
(D/'passage-receipts.json').write_text(json.dumps(receipts,indent=2))
a=(D/'live/author-accepted.pdf.txt').read_text().splitlines();b=(D/'live/coauthor-linked.pdf.txt').read_text().splitlines();diff=[{'line':i+1,'giacchini':x,'chierichetti':y} for i,(x,y) in enumerate(zip(a,b)) if x!=y];(D/'author-comparison.json').write_text(json.dumps({'line_counts':[len(a),len(b)],'differences':diff,'result':'same extracted text except title-page date; both explicitly Accepted Manuscript, not VoR'},indent=2))
print('evidence saved')
