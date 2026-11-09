import sys; sys.argv=['x','3','0','3']
exec(open(sys.path[0]+'/defective_gs_search.py').read().split('subsets=')[0])
m=(7,7,2)  # source example: pairs (0,1),(0,2),(1,2)
print('source example 7,7,2 d=3: 4 colours ok?',colourable(m,4),' 5 colours ok?',colourable(m,5))
