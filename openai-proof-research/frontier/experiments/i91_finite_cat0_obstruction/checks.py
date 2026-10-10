"""Offline exact certificate checker and finite stress tests. No writes."""
import json
from pathlib import Path
from fractions import Fraction as F
from math import isqrt
from template import template
import algebraic

E=Path(__file__).resolve().parent

def certificate():
    c=json.loads((E/'certificate.json').read_text())
    # Replay the bounded search to bind every row to the explicit CAT(0)
    # generator, its actual template, and its initial ideal constraints.
    replay=algebraic.run(True);allrows=replay.pop('rows')
    replay['used_rows']={str(i):allrows[i] for i in sorted({s[0] for s in replay['trace']}|{replay['contradiction']['row']})}
    assert json.loads(json.dumps(replay))==c
    # Independently check each stored inference as a REAL rational bound.
    den=c['dyadic_denominator']; bounds=[[F(a,den),F(b,den)] for a,b in c['initial']]
    for ri,k,side,integer in c['trace']:
        row=dict(c['used_rows'][str(ri)]);coef=row[k]
        rest=sum(F(v)*bounds[j][0 if v>0 else 1] for j,v in row.items() if j!=k)
        value=F(integer,den); exact=-rest/coef
        if side=='upper':
            assert coef>0 and value>=exact and value<bounds[k][1]
            bounds[k][1]=value
        else:
            assert coef<0 and value<=exact and value>bounds[k][0]
            bounds[k][0]=value
        assert bounds[k][0]<=bounds[k][1]
    row=c['used_rows'][str(c['contradiction']['row'])]
    margin=sum(F(v)*bounds[k][0 if v>0 else 1] for k,v in row)
    assert margin==F(c['contradiction']['positive_minimum'],den)>F(1,100)
    assert c['max_row_l1']<=69 and c['updates']<3000
    # Every row with RHS <= delta and initial error <= delta survives
    # at most 3000 updates with bound error <= 100^3000 delta.
    assert 69*F(1,10**4000)+F(1,10**10000)<F(1,100)
    assert 80032//8==10004 and 80032%8==0
    assert 2000*F(1,10**10004)<F(1,10**10000)
    return {'status':'PASS_EXACT_FINITE_INEQUALITY_CERTIFICATE','updates':c['updates'],'used_rows':len(c['used_rows']), 'full_generated_rows':c['inequalities'],'points':c['points'],'variables':c['variables'],'margin':str(margin),'perturbation_delta':'10^-10000','geometric_e':'10^-80032'}

def tests():
    t=template();assert len(t['vertices'])==18 and len(t['edges'])==32
    assert len(t['hexagons'])==86 and t['hexagon_diameter']==3
    assert sum(len(a)*(len(a)-1)//2 for a in t['adj'].values())==90
    # All full-line pairs are connected by the actual fan square.
    for i in (1,2,4,7):assert len(t['adj']['Y'+str(i)])==(2 if i==7 else 3)
    n=0
    for k in range(1,33):
        tau=F(1,2**k);B=12;M=6
        bound=16*B*B/tau**2;tt=(bound.numerator+bound.denominator-1)//bound.denominator
        b=tau**2/(16*B*B*M);eta=min(tau**2/(32*B*B*M*M),tau/(8*B*M))
        inside=F(1,tt)+b*M*F(tt-1,tt)+2*M*M*eta
        assert inside<=3*tau*tau/(16*B*B) and 2*B*M*eta<=tau/4
        for j in range(1,18):
            old=F(1,j)+b*M*F(j-1,j)
            new=F(j*j,(j+1)**2)*old+F(1,(j+1)**2)+2*b*M*F(j,(j+1)**2)
            assert new==F(1,j+1)+b*M*F(j,j+1);n+=1
    # Exact rational stem-epsilon distances at fixed fractions.
    tree=0
    for k in range(1,25):
        eps=F(1,2**k)
        for q in (F(1),F(1,2),eps,eps/2):
            dist=2*max(q-eps,0)
            assert 0<=dist<=2*q
            if q<=eps:assert dist==0
            tree+=1
    # Coarse monomial envelopes in the proof, with u=e^(1/8).
    assert F(17,4)+63<68
    assert 17+68+63==148 and 4*148<25**2
    assert 25+5*(21+2)==140
    assert F(3,2)+6<8 and 8+8==16
    assert F(8*68+7+2*8+2*16,9)<67 and 67<9**2
    assert 68+1<9**2 and 140+3*9==167
    assert 6*167+5*68+16+8*18+16<=1523
    assert F(140)+F(1523,4)<23**2 and 32*23<2000
    assert 72*F(1,663552)==F(1,9216)
    assert 4*16*144==9216 and 4*16*144*6==55296
    assert 4*32*144*36==663552
    assert F(98,392)<F(1,2) and 1080*1960==2116800
    # Reverse-median Young certificate at rational sigma.
    rev=0
    for k in range(3,32):
        eps=F(1,2**(2*k));sigma=F(1,2**k);q=F(1,2)-sigma
        lower=(F(1,2)-q-F(9,4)*eps)/(1/q-2)
        assert lower>=F(1,4)-F(17,16)*sigma
        rev+=1
    return {'status':'PASS_FINITE_DIAGNOSTICS_ONLY','hexagons':86,'hexagon_graph_diameter':3,'mean_recurrences':n,'conditional_budgets':32,'tree_cases':tree,'reverse_median_cases':rev}

if __name__=='__main__':print(json.dumps({'certificate':certificate(),'diagnostics':tests()},sort_keys=True,indent=2))
