import pathlib,re,hashlib,json,sys
R=pathlib.Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r161')
name=sys.argv[1]; starts=[int(x) for x in sys.argv[2:]]; p=pathlib.Path(name);b=p.read_bytes();ls=b.splitlines(keepends=True)
records=[]
for st in starts:
 h=re.match(rb'^(#{1,6}) ',ls[st-1]); assert h
 level=len(h.group(1));en=next((i for i in range(st,len(ls)) if (m:=re.match(rb'^(#{1,6}) ',ls[i])) and len(m.group(1))<=level),len(ls))
 part=b''.join(ls[st-1:en]);dest=R/'private/history'/(p.stem+'-L'+str(st)+'.md');dest.write_bytes(part)
 records.append({'original':name,'original_bytes':len(b),'original_sha256':hashlib.sha256(b).hexdigest(),'start_line':st,'end_line':en,'selected':str(dest.relative_to(R)),'selected_bytes':len(part),'selected_sha256':hashlib.sha256(part).hexdigest()})
 print('ORIGINAL SECTION',name,st,en); print(part.decode())
log=R/'private/history/selected-identities.json';old=json.loads(log.read_text()) if log.exists() else [];log.write_text(json.dumps(old+records,indent=2)+'\n')
