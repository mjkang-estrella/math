from explore import *
ids=['1904.00563v1','1904.00725v1','1904.00779v4','1904.00971v2','1904.01204v1','1904.01282v1','1904.01394v2','1904.01436v1','1904.01858v2','1904.01925v2','1904.02229v2','1904.02313v1','1904.02550v1','1904.02595v1','1904.02627v2','1904.02694v3','1609.07639v2','2605.03284v2','2410.14063v2']
log=[]
for ident in ids:
 p=L/'sources'/(ident+'.txt');before=digest(p);s=p.read_text();i=s.find('Proof.');i=i if i>=0 else s.find('Proof of');i=i if i>=0 else 0
 piece=s[i:i+1900];print('\nBODY',ident,'offset',i,'\n',piece)
 assert before==digest(p);log.append(dict(id=ident,text_sha256=before,offset=i,length=len(piece)))
(L/'proof-read-log.json').write_text(json.dumps(log,indent=2))
