import itertools, json
def rc(w, m): return ''.join(m[x] for x in reversed(w))
def opt(S, alpha, m, maxlen):
    for L in range(0, maxlen+1):
        wit=[]
        for t in itertools.product(alpha, repeat=L):
            w=''.join(t)
            if all(s in w or rc(s,m) in w for s in S): wit.append(w)
        if wit: return L, len(wit), wit[0]
    return None
out={}
m1={'b':'b','c':'c'}
out['ex1']=opt(['bbcbbc','bcbbcb','cbbcbb'],'bc',m1,8)
m2={'a':'b','b':'a','c':'c'}
out['ex2']=opt(['aaa','aab','abcaa','accc'],'abc',m2,11)
A='abcacb'*4; mi={'a':'a','b':'b','c':'c'}
rots=[(A[i:i+6],i) for i in range(6)]
out['lexmax_rotation_starts']=[i for r,i in rots if r==max(r for r,_ in rots)]
out['self_reversed_text']= rc('abcacb',mi) in [ 'abcacb'[i:]+'abcacb'[:i] for i in range(6)]
out['pal_len7_starts']=[i for i in range(6) if A[i:i+7]==A[i:i+7][::-1]]
out['pal_len8_starts']=[i for i in range(6) if A[i:i+8]==A[i:i+8][::-1]]
out['start4_windows']=[A[4:11],A[4:12], A[4:11]==A[4:11][::-1], A[4:12]==A[4:12][::-1]]
print(json.dumps(out))
