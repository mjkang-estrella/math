"""Fresh finite lock, helper, patch and reduction checks on retained data only."""


def difference_components(p, u, edges):
    ee = [e for e, a, b in zip(edges, p, u) if a != b]
    vertices = sorted({v for e in ee for v in e})
    groups, _ = components(vertices, ee)
    return [sorted(e for e in ee if set(e) <= set(vv)) for vv in groups]


def toggle(bits, edges, changed):
    changed = set(changed)
    return tuple(1-b if e in changed else b for e, b in zip(edges, bits))


def word_signature(vertices, chosen):
    groups, adj = components(vertices, chosen)
    words, cycles, singles, pairing = [], [], [], []
    for group in groups:
        if not adj[group[0]]:
            singles.append(group[0])
            continue
        ends = [v for v in group if len(adj[v]) == 1]
        at = min(ends or group)
        word, used = [at], set()
        while True:
            options = sorted((v,i) for v,i in adj[at] if i not in used)
            if not options:
                break
            at,i = options[0]
            used.add(i)
            word.append(at)
            if at == word[0]:
                break
        assert len(used) == sum(len(adj[v]) for v in group)//2
        words.append(word)
        if ends:
            pairing.append(edge(*ends))
        else:
            cycles.append(word)
    return {"words":words,"cycles":cycles,"pairing":sorted(pairing),"singletons":singles}


def lock(read_json, S):
    ref = read_json(REF)["I179_lock"]
    P = S["local"][(0,1)][((0,1),)]
    U = S["states"][0]["X"]
    assert len(P) == 5 and len(U) == 1
    edges, vertices, u = S["xe"], S["X"], U[0]
    masks = switches = failures = 0
    rows = []
    for pi, p in enumerate(P):
        pieces = difference_components(p,u,edges)
        valid, degree_sets = [], set()
        for mask in range(1 << len(pieces)):
            changed = {e for i, comp in enumerate(pieces) if mask >> i & 1 for e in comp}
            q, v = toggle(p,edges,changed), toggle(u,edges,changed)
            degree_sets.add(q)
            ok = (q in P and v in U) or (q in U and v in P)
            if ok:
                valid.append(mask)
            if mask.bit_count() == 1:
                switches += 1
                if not ok:
                    failures += 1
                    assert any(signature(vertices, [e for e,b in zip(edges,z) if b])["cycles"]
                               for z in (q,v))
            masks += 1
        assert valid == [0, (1 << len(pieces))-1]
        # Independent edge-assignment exhaustion, no component premises.
        diff = [j for j,(a,b) in enumerate(zip(p,u)) if a != b]
        common = {j for j,(a,b) in enumerate(zip(p,u)) if a == b == 1}
        degp = {v:sum(p[j] for j,e in enumerate(edges) if v in e) for v in vertices}
        degu = {v:sum(u[j] for j,e in enumerate(edges) if v in e) for v in vertices}
        all_assignments = set()
        for assignment in product((0,1), repeat=len(diff)):
            chosen = common | {j for j,bit in zip(diff,assignment) if bit}
            q = tuple(int(j in chosen) for j in range(len(edges)))
            deg = {v:sum(q[j] for j,e in enumerate(edges) if v in e) for v in vertices}
            if deg in (degp,degu):
                all_assignments.add(q)
        assert all_assignments == degree_sets
        rows.append({"p":pi,"components":pieces,"valid_masks":valid})
    assert (masks,switches,failures) == (18,9,8)
    assert normalize(rows) == ref["records"]
    return {"status":"PASS","masks":masks,"single_switches":switches,
            "cycle_failures":failures,"records":rows}


def helper_identities(read_json, S):
    ref = read_json(REF)["helper"]["parent_identities"]
    P, edges = S["local"][(0,1)][((0,1),)], S["xe"]
    rows = []
    for qi,q in enumerate(P[1:],1):
        for si,st in enumerate(S["states"]):
            for ui,u in enumerate(st["X"]):
                for vi,v in enumerate(st["X"]):
                    if plus(P[0],u) != plus(q,v):
                        continue
                    changed = [e for e,a,b in zip(edges,P[0],q) if a!=b]
                    pieces = difference_components(P[0],u,edges)
                    whole = changed in pieces
                    sig = signature(sorted({v for e in changed for v in e}),changed)
                    single = whole and len(sig["cycles"])==1 and not sig["paths"]
                    rows.append({"P_index":qi,"state":si,"u_index":ui,
                                 "up_index":vi,"changed_edges":changed,
                                 "single_alternating_cycle":single})
    assert normalize(rows)==ref
    assert len(rows)==12 and sum(r["single_alternating_cycle"] for r in rows)==3
    return {"status":"PASS","identities":rows}


def helper_graph(read_json, S):
    ref = read_json(REF)["helper"]
    P, edges = S["local"][(0,1)][((0,1),)], S["xe"]
    witnesses, rejected, graph = [], [], set()
    overlays = moves = 0
    for pi,p in enumerate(P):
        for si,st in enumerate(S["states"]):
            for ui,u in enumerate(st["X"]):
                overlays += 1
                for cc in difference_components(p,u,edges):
                    vv = sorted({v for e in cc for v in e})
                    sig = signature(vv,cc)
                    if sig["paths"]:
                        continue
                    assert len(sig["cycles"]) == 1
                    moves += 1
                    q,v = toggle(p,edges,cc),toggle(u,edges,cc)
                    assert plus(p,u)==plus(q,v)
                    if q in P and v in st["X"]:
                        qi,vi = P.index(q),st["X"].index(v)
                        graph.add(edge(pi,qi))
                        witnesses.append({"p_index":pi,"q_index":qi,"state":si,
                                          "u_index":ui,"v_index":vi,"cycle_edges":cc})
                    else:
                        assert signature(S["X"],[e for e,b in zip(edges,q) if b])["cycles"]
                        rejected.append({"p_index":pi,"state":si,"u_index":ui,
                            "cycle_edges":cc,
                            "q":word_signature(S["X"],[e for e,b in zip(edges,q) if b]),
                            "v":word_signature(S["X"],[e for e,b in zip(edges,v) if b])})
    assert (overlays,moves,len(witnesses),len(rejected)) == (130,123,24,99)
    assert normalize(sorted(graph))==ref["graph"]
    for actual,key in ((witnesses,"witnesses"),(rejected,"rejected")):
        assert normalize(actual)==ref[key],key
    exact_forward = []
    for pi,qi in combinations(range(5),2):
        for si,st in enumerate(S["states"]):
            for ui,u in enumerate(st["X"]):
                for vi,v in enumerate(st["X"]):
                    if plus(P[pi],u)!=plus(P[qi],v):
                        continue
                    cc = [e for e,a,b in zip(edges,P[pi],P[qi]) if a!=b]
                    if cc in difference_components(P[pi],u,edges):
                        sig = signature(sorted({v for e in cc for v in e}),cc)
                        if len(sig["cycles"])==1 and not sig["paths"]:
                            exact_forward.append((pi,qi,si,ui,vi))
    assert normalize(exact_forward)==ref["exact_forward"]
    distances = [sum(a!=b for a,b in zip(p,P[4])) for p in P]
    assert distances == [8,8,8,6,0] == ref["distances"]
    pdiff = [S["embed"](z,S["xe"]) for z in differences(P)]
    ranks = [rank(pdiff),rank(S["wx"]),rank(pdiff+S["wx"])]
    assert ranks == [4,5,5] == ref["ranks"]
    return {"status":"PASS","overlays":overlays,"cycle_moves":moves,
            "witnesses":witnesses,"rejected":rejected,"exact_forward":exact_forward,
            "graph":sorted(graph),"distances":distances,"ranks":ranks}


def all_pairings(vertices):
    if not vertices:
        yield []
    else:
        a,*tail = vertices
        for b in tail:
            for rest in all_pairings([v for v in tail if v != b]):
                yield [edge(a,b)]+rest


def patch_control(read_json):
    ref = read_json(REF)["I181_patch_reattachment"]
    boundary = [edge(i,(i+1)%6) for i in range(6)]
    chord, continuations = (0,3),[(1,6),(2,7),(5,8),(4,9)]
    edges = boundary+[chord]+continuations
    A, B = boundary[::2],boundary[1::2]
    degree_correct, forced = [], []
    for bits in product((0,1),repeat=11):
        chosen = [e for e,b in zip(edges,bits) if b]
        if not all(sum(v in e for e in chosen)==2 for v in range(6)):
            continue
        degree_correct.append(chosen)
        if set(chosen)&set(boundary) in (set(A),set(B)):
            forced.append(chosen)
            assert chord in chosen and set(continuations)<=set(chosen)
            sig=signature(range(10),chosen)
            assert sig["paths"]==[(6,7),(8,9)] and not sig["cycles"]
    assert len(degree_correct)==10 and len(forced)==2
    routes = [A+[chord],B+[chord]]
    rows=[]
    for ports in ([6,7],[6,7,8,9]):
        for segments in all_pairings([1,2,4,5]+ports):
            outcomes=[]
            for routing in routes:
                sig=signature(list(range(6))+ports,routing+segments)
                assert not sig["singletons"]
                outcomes.append({"cycles":len(sig["cycles"]),"pairing":sig["paths"]})
            quotient=signature([1,2,4,5]+ports,[(1,2),(4,5)]+segments)
            assert outcomes[0]==outcomes[1]
            assert outcomes[0]=={"cycles":len(quotient["cycles"]),"pairing":quotient["paths"]}
            rows.append({"ports":ports,"segments":segments,"reattachments":outcomes,
                         "pairing":outcomes[0]["pairing"],
                         "quotient_cycles":len(quotient["cycles"])})
    assert len(rows)==120 and normalize(rows)==ref["rows"]
    return {"status":"PASS","degree_correct_subsets":len(degree_correct),
            "forced":forced,"rows":rows,"rows_count":len(rows)}


def reduction(read_json,S):
    ref=read_json("frontier/experiments/i182_controlled_extension/extension-attempt-01.json")
    graph=read_json(P177+"experiment-attempt-03.json")["child"]["graph"]
    edges, X, vertices = S["edges"],set(S["X"]),sorted(S["X"]+S["Y"])
    faces=[f for f in graph["faces"] if len(f)==4]
    patches,excluded=[],[]
    for f,g in combinations(faces,2):
        fe={edge(a,b) for a,b in zip(f,f[1:]+f[:1])}
        ge={edge(a,b) for a,b in zip(g,g[1:]+g[:1])}
        if len(fe&ge)!=1: continue
        vv=set(f)|set(g)
        if not vv<=X or vv&set(S["xp"]):
            excluded.append((f,g));continue
        boundary=sorted(fe^ge); chord=next(iter(fe&ge))
        assert len(vv)==6 and len(boundary)==6
        patches.append((boundary,chord,vv))
    patches.sort()
    assert len(patches)==3 and len(excluded)==4
    P=S["local"][(0,1)][((0,1),)]
    instances=[];checks=0
    for boundary,chord,vv in patches:
        for pi,p in enumerate(P):
            q=toggle(p,S["xe"],boundary)
            if q not in P:continue
            A=[e for e in boundary if p[S["xe"].index(e)]]
            B=[e for e in boundary if e not in A]
            assert len(A)==len(B)==3 and sorted(v for e in A for v in e)==sorted(vv)
            continuation=[e for e in edges if len(set(e)&vv)==1]
            assert len(continuation)==4
            terminals=sorted(next(v for v in e if v not in vv) for e in continuation)
            assert len(set(terminals))==4
            ee=[e for e in edges if not set(e)&vv]; vs=sorted(set(vertices)-vv)
            forced=B+[chord]+continuation
            sig=signature(sorted(vv|set(terminals)),forced)
            localpair=sig["paths"]
            assert len(localpair)==2 and not sig["cycles"]
            matches=factors(vs,ee,{v:1 for v in vs})
            counts=dict(total=len(matches),hamiltonian=0,controlled=0,lost_P=0,lost_D=0,
                        parallel_pairing=0,with_closed_components=0)
            controlled=set();hit=defaultdict(int); first={}
            for m in matches:
                checks+=1
                M=sorted(A+[e for e,b in zip(ee,m) if b])
                assert sorted(v for e in M for v in e)==vertices
                hprime=[e for e,b in zip(ee,m) if not b]
                psig=signature(vs,hprime)
                assert not psig["singletons"] and len(psig["paths"])==2
                topology=not psig["cycles"] and psig["paths"]!=localpair
                H=[e for e in edges if e not in M]
                fullsig=signature(vertices,H)
                assert topology==(len(fullsig["cycles"])==1 and not fullsig["paths"])
                assert sorted(hprime+forced)==H
                if psig["cycles"]:
                    counts["with_closed_components"]+=1
                elif psig["paths"]==localpair:
                    counts["parallel_pairing"]+=1
                else:
                    counts["hamiltonian"]+=1
                    z=bits_for(S["xe"],[e for e in H if e in S["xe"]])
                    state=next((i for i,st in enumerate(S["states"]) if z in st["X"]),None)
                    if state is not None:
                        counts["controlled"]+=1;hit[str(state)]+=1
                        controlled.add(tuple(M));first.setdefault(str(state),M)
                    elif z in P:counts["lost_P"]+=1
                    else:
                        assert z in S["local"][(0,1,3,4)][((0,1),(3,4))]
                        counts["lost_D"]+=1
            products_set=set(); helpers=cyclic=0
            for st in S["states"]:
                for u in st["X"]:
                    if {e for e in boundary if u[S["xe"].index(e)]}!=set(B):continue
                    helpers+=1
                    assert toggle(u,S["xe"],boundary) in st["X"]
                    for py,ys in S["exterior"][st["J"]].items():
                        for y in ys:
                            H=S["glue"](u,y,st["J"])
                            hs=signature(vertices,[e for e,b in zip(edges,H) if b])
                            if len(hs["cycles"])!=1:
                                cyclic+=1;assert py==st["px"];continue
                            M=tuple(e for e,b in zip(edges,H) if not b)
                            assert set(A)<=set(M)
                            products_set.add(M)
            assert products_set==controlled and (helpers,len(controlled),cyclic)==(3,5,9)
            qi=P.index(q)
            expected=next(z for z in ref["instances"]
                          if z["patch_boundary"]==normalize(boundary) and z["p_index"]==pi)
            assert counts==expected["matchings"] and dict(hit)==expected["fibres_hit"]
            assert expected["q_index"]==qi
            assert expected["half_A"]==normalize(A) and expected["half_B"]==normalize(B)
            # Every retained example matching must occur, not just its count.
            assert all(tuple(map(tuple,m)) in controlled for m in expected["witness_matchings"].values())
            for y in S["exterior"][(0,1)][((0,1),)]:
                H=S["glue"](q,y,(0,1))
                assert set(A)<={e for e,b in zip(edges,H) if not b}
            instances.append({"patch_boundary":boundary,"p_index":pi,"q_index":qi,
                              "matchings":counts,"fibres_hit":dict(hit),
                              "controlled_matchings":sorted(controlled),
                              "helpers_total":helpers,"products_cyclic":cyclic})
    assert checks==626 and len(instances)==6
    return {"status":"PASS","patches_internal":len(patches),"excluded":excluded,
            "instances":instances,"reduction_checks":checks,"E183":"UNRESOLVED"}
