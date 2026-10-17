#!/usr/bin/env python3
"""Finite controls for the original two-bank program; not a universal proof. MIT."""
import json

def program(h, relation, defect=None):
    w=[]
    for j in range(h):
        for i in range(h):
            x,y=(-i)%h,(-j)%h
            if defect=='wrong_sign': x,y=i,j
            w.extend(('E' if (x,y) in relation else 'I','U'))
        if defect!='omit_V':w.append('V')
    w.extend(('S','D') if defect=='reverse_DS' else ('D','S'))
    return w

def step(h, states, letter):
    out=set()
    for x in states:
        if letter=='I':out.add(x)
        elif letter=='U':out.add((x+1)%h if x<h else x)
        elif letter=='V':out.add(x if x<h else h+(x-h+1)%h)
        elif letter=='E':
            out.add(x)
            if x==0:out.add(h)
        elif letter=='D':
            if x>=h:out.add(x)
        elif letter=='S':out.add(x+h if x<h else x-h)
    return out

def run(h, states, w):
    for letter in w:states=step(h,states,letter)
    return states

def check():
    total=0; mutants={k:None for k in ['wrong_sign','omit_V','reverse_DS']}
    alphabet='IUVEDS'; codes={s:format(i,'03b') for i,s in enumerate(alphabet)}
    for h in (2,3):
        for mask in range(1<<(h*h)):
            relation={(i,j) for i in range(h) for j in range(h) if mask>>(i*h+j)&1}
            w=program(h,relation)
            assert len(w)==2*h*h+h+2
            binary=''.join(codes[s] for s in w)
            decoded=[alphabet[int(binary[k:k+3],2)] for k in range(0,len(binary),3)]
            assert decoded==w
            for inputs in range(1<<h):
                states={i for i in range(h) if inputs>>i&1}
                expected={j for i,j in relation if i in states}
                assert run(h,states,w)==expected
                total+=1
                for key in mutants:
                    if mutants[key] is None and run(h,states,program(h,relation,key))!=expected:
                        mutants[key]={'h':h,'relation_mask':mask,'input_mask':inputs}
    assert all(v is not None for v in mutants.values())
    return {'status':'FINITE_CHECKS_PASS','relation_subset_cases':total,'h':[2,3],
            'binary_code_roundtrips':16+512,'rejected_mutants':mutants,
            'limits':'Exhaustive only at h=2,3. Does not test arbitrary two-way machines or prove the source lower bounds.'}
if __name__=='__main__':print(json.dumps(check(),indent=2,sort_keys=True))
