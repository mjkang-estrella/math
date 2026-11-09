import sys; sys.path.insert(0,sys.argv[1])
exec(open(sys.argv[1]+'/srg_search.py').read().split('hits=[]')[0].split('path=sys.argv[2]')[0])
