"""Exact finite algebra only. No external packages, writes, or network."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import runpy,json,hashlib
from fractions import Fraction
HERE=Path(__file__).resolve().parent
P=runpy.run_path(str(HERE/'moment_probe.py'))

def independent_rows(rows,cols,prime=1000003):
    piv={};chosen=[];det=1
    for i,orig in enumerate(rows):
        row={k:v%prime for k,v in orig.items() if v%prime}
        while row:
            j=min(row);v=row[j]
            if j not in piv:
                inv=pow(v,-1,prime);piv[j]={k:w*inv%prime for k,w in row.items()};chosen.append(i);break
            for k,w in piv[j].items():
                z=(row.get(k,0)-v*w)%prime
                if z:row[k]=z
                elif k in row:del row[k]
        if len(chosen)==cols:break
    return chosen

def det_mod(rows,cols,p=1000003):
    a=[[row.get(j,0)%p for j in range(cols)] for row in rows];ans=1
    for j in range(cols):
        k=next((k for k in range(j,cols) if a[k][j]),None)
        if k is None:return 0
        if j!=k:a[j],a[k]=a[k],a[j];ans=-ans
        v=a[j][j];ans=ans*v%p;inv=pow(v,-1,p)
        for k in range(j+1,cols):
            c=a[k][j]*inv%p
            if c:
                for l in range(j,cols):a[k][l]=(a[k][l]-c*a[j][l])%p
    return ans%p

def check():
    counts=[]
    for r in range(1,6):
        rows,keys=P['matrix'](r);rr=P['rank'](rows)
        raw,_=P['matrix'](r,False)
        counts.append(dict(degree=r,rows=len(rows),columns=len(keys),rank=rr,kernel=len(keys)-rr,ungauged_kernel=len(keys)-P['rank'](raw)))
    assert [x['kernel'] for x in counts]==[12,12,8,0,0]
    rows,keys=P['matrix'](4);chosen=independent_rows(rows,len(keys));det=det_mod([rows[i] for i in chosen],len(keys));assert len(chosen)==165 and det
    # 24 independent symmetric Hessian entries, with trace and physical divergence constraints.
    keysH=[(q,a,b) for q in range(4) for a in range(3) for b in range(a,3)];index={k:i for i,k in enumerate(keysH)}
    rowsH=[]
    for q in range(4):rowsH.append({index[q,a,a]:1 for a in range(3)})
    for a in range(3):rowsH.append({index[q,min(a,q),max(a,q)]:1 for q in range(3)})
    assert P['rank'](rowsH)==7
    # C C* = 5/3 identity on vector tracefree Hessians, with tensor Frobenius pairing.
    def cstar(t,q,a,b):return (Fraction((a==q)*t[b]+(b==q)*t[a],2)-Fraction(a==b,3)*t[q])
    gram=[]
    for k in range(3):
        t=[int(k==i) for i in range(3)];out=[sum(cstar(t,q,a,q) for q in range(3)) for a in range(3)];gram.append(out)
        assert out==[Fraction(5,3)*int(a==k) for a in range(3)]
    return dict(status='PASS finite exact algebra only',physical_hessian_dimension=24-P['rank'](rowsH),annihilator_gram=[[str(x) for x in row] for row in gram],prolongations=counts,certificate=dict(prime=1000003,degree=4,dimension=165,row_indices=chosen,determinant_mod_prime=det),scope='Finite linear maps; no universal inverse-problem or contribution certification')
if __name__=='__main__':print(json.dumps(check(),indent=2))
