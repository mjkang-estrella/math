import sys
for p in sys.argv[2:]:
    t=open(p,encoding='utf-8').read();k=sys.argv[1];i=t.find(k);n=0
    while i>=0 and n<3:
        print(p.split('/')[-2],'|',t[max(0,i-250):i+150].replace('\n',' '));i=t.find(k,i+1);n+=1
