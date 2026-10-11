"""Finite validation of remote-splice certificates and prism loss transport."""
from itertools import permutations


def prism(length):
    L = length
    es = [edge(i, (i+1) % L) for i in range(L)]
    es += [edge(L+i, L+(i+1) % L) for i in range(L)]
    es += [(i, L+i) for i in range(L)]
    faces = [list(range(L)), list(range(2*L-1, L-1, -1))]
    faces += [[(i+1) % L, i, L+i, L+(i+1) % L] for i in range(L)]
    return dict(n=2*L, edges=sorted(es), faces=faces, history="prism-"+str(L))


def rotations(record):
    turns = {}
    for f in record["faces"]:
        for i, v in enumerate(f):
            turns.setdefault(v, {})[f[i-1]] = f[(i+1) % len(f)]
    return turns


def face_walk(turns):
    darts = {(a, b) for b, link in turns.items() for a in link}
    faces = []
    while darts:
        first = min(darts)
        a, b = first
        f = []
        while True:
            darts.remove((a, b))
            f.append(a)
            a, b = b, turns[b][a]
            if (a, b) == first:
                break
        faces.append(f)
    return faces


def splice(base, z, attachment, h):
    """Select first sphere rotation from six explicit port bijections."""
    g, a = Graph(base), Graph(attachment)
    trans = {v: max(g.vertices)+1+i for i, v in enumerate(a.vertices)}
    at = dict(n=a.n, edges=[edge(trans[u], trans[v]) for u, v in a.edges],
              faces=[[trans[v] for v in f] for f in attachment["faces"]])
    h = trans[h]
    gt, ht = rotations(base), rotations(at)
    ports = sorted(gt[z])
    other = sorted(ht[h])
    attempts = []
    for target in permutations(other):
        turns = {v: dict(t) for v, t in (gt | ht).items() if v not in (z, h)}
        mapping = dict(zip(ports, target))
        for u, v in mapping.items():
            turns[u] = {(v if x == z else x): (v if y == z else y)
                        for x, y in turns[u].items()}
            turns[v] = {(u if x == h else x): (u if y == h else y)
                        for x, y in turns[v].items()}
        faces = face_walk(turns)
        edges = sorted({edge(v, w) for v in turns for w in turns[v]})
        record = dict(n=g.n+a.n-2, edges=edges, faces=faces,
                      history=base["history"]+" splice "+str(z)+" "+attachment["history"])
        chi = record["n"]-len(edges)+len(faces)
        attempts.append(dict(mapping=sorted(mapping.items()), euler=chi))
        if chi != 2:
            continue
        Graph(record).validate()
        return record, mapping, trans, attempts
    raise AssertionError("no sphere port map")


def same_step(record, e, f, length):
    target = {edge(*e), edge(*f)}
    matches = []
    for step in steps(record, length):
        face = record["faces"][step[0]]
        if {edge(face[k], face[(k+1) % len(face)]) for k in step[1:]} == target:
            matches.append(step)
    assert len(matches) == 1, matches
    return matches[0]


def affine_certificate(g, F):
    # Keep a basis-sized subset of Hamiltonian vertices for readable support.
    cycles = g.cycles()
    chosen = [cycles[0]]
    rows, r = [], 0
    for C in cycles[1:]:
        v = sub(C, chosen[0])
        nr = rank(rows+[v])
        if nr > r:
            chosen.append(C)
            rows.append(v)
            r = nr
    matrix = [[C[i] for C in chosen] for i in range(g.m)]
    matrix.append([1]*len(chosen))
    coeff = solve(matrix, list(F)+[1], len(chosen))
    assert add(*(scale(c, C) for c, C in zip(coeff, chosen))) == F
    assert sum(coeff) == 1
    return [(C, c) for C, c in zip(chosen, coeff) if c]


def project_cycle(source, target, z, mapping, C):
    result = []
    for a, b in source.edges:
        if z in (a, b):
            u = b if a == z else a
            i = target.eid[edge(u, mapping[u])]
        else:
            i = target.eid[(a, b)]
        result.append(C[i])
    return tuple(result)


def remote_splices():
    mandatory()
    results = []
    cube = prism(4)
    # Six genuine larger graphs, both square deletion types. These are
    # theorem-validation instances, not a coefficient-discovery census.
    for L in (4, 6, 8):
        base = prism(L)
        g = Graph(base)
        g.validate()
        z = 2
        for attachment in (cube, prism(6)):
            child, mapping, trans, attempts = splice(base, z, attachment, 0)
            G = Graph(child)
            G.validate()
            G.cycles()
            projection = {C: project_cycle(g, G, z, mapping, C) for C in G.cycles()}
            assert set(projection.values()) == set(g.cycles())
            for e, f in (((0, L), (1, L+1)), ((0, 1), (L, L+1))):
                st, tt = same_step(base, e, f, 4), same_step(child, e, f, 4)
                row, d = analyze(g, st, True)
                rr, dd = analyze(G, tt, True)
                assert rr["alpha"] == row["alpha"] == str(-Q(L-3, L-2))
                assert (rr["ell"], rr["t"], rr["eta"]) == (row["ell"], row["t"], row["eta"])
                u, v, x, y = g.families(st)[1]
                s = sub(add(g.unit(u, v), g.unit(x, y)), add(g.unit(u, x), g.unit(v, y)))
                S = d["families"]["N10"]+d["families"]["N01"]+d["families"]["N11"]
                port = lambda C: tuple(C[g.eid[edge(z, w)]] for w in sorted(mapping))
                assert len({port(C) for C in S}) == 3
                kernel_dim = rank(differences(G.cycles()))-rank(differences(g.cycles()))
                assert rank(dd["L"])-rank(d["L"]) == kernel_dim
                # Build a prescribed affine lift using a fixed attachment
                # cycle in each omitted-port class, choosing the actual
                # prescribed N' lift in its class.
                Nprime = dd["families"]["N00"][0]
                N = projection[Nprime]
                F = add(N, s)
                cert = affine_certificate(g, F)
                reference = {}
                for C in G.cycles():
                    reference.setdefault(port(projection[C]), C)
                reference[port(N)] = Nprime
                lifted = []
                source_interior = {edge(a, b) for a, b in g.edges if z not in (a, b)}
                cut = {edge(a, b) for a, b in mapping.items()}
                attachment_indices = [i for i, ee in enumerate(G.edges)
                                      if ee not in source_interior and ee not in cut]
                for C, coefficient in cert:
                    ref = reference[port(C)]
                    lifts = [Z for Z in G.cycles() if projection[Z] == C and
                             all(Z[i] == ref[i] for i in attachment_indices)]
                    assert len(lifts) == 1
                    lifted.append((lifts[0], coefficient))
                up, vp, xp, yp = G.families(tt)[1]
                sp = sub(add(G.unit(up, vp), G.unit(xp, yp)), add(G.unit(up, xp), G.unit(vp, yp)))
                Fprime = add(Nprime, sp)
                # Terminal conventions may swap retained and deleted pairs
                # only if same_step is wrong; the exact equality checks it.
                assert add(*(scale(a, C) for C, a in lifted)) == Fprime
                total = sum(a for C, a in lifted if C in dd["families"]["N00"])
                assert total == Q(1, L-2)
                results.append(dict(L=L, attachment=attachment, splice_vertex=z,
                                    port_mapping=sorted(mapping.items()), rotation_attempts=attempts,
                                    graph=child, base_graph=base, base_row=row, row=rr,
                                    cycles=G.cycles(), families=dd["families"],
                                    N=Nprime, F=Fprime, kernel_dimension=kernel_dim,
                                    coefficients=[dict(C=C, coefficient=str(a)) for C, a in lifted],
                                    N00_coefficient_total=str(total)))
    return dict(cases=len(results), rows=results, theorem_scope="remote vertex splices; not all braces")


def loss_transport():
    mandatory()
    records = []
    # A prescribed high-loss rung pair on the lateral face of even prisms.
    # Lengthen both boundary arcs by expanding top and bottom cap edges.
    # The second cap-edge choice is exhaustive at L=6,8,10, not random.
    for L in (6, 8, 10):
        base = prism(L)
        g = Graph(base)
        g.validate()
        root_step = same_step(base, (0, L), (1, L+1), 4)
        root_row = analyze(g, root_step)
        assert root_row["ell"] == L-3
        for j in range(2, L-1, 2):
            st = same_step(base, (0, 1), (j, j+1), L)
            top = expand(base, st)
            top_g = Graph(top)
            top_step = same_step(top, (0, L), (1, L+1), 6)
            top_row = analyze(top_g, top_step)
            for k in range(2, L-1, 2):
                bottom_step = same_step(top, (L, L+1), (L+k, L+k+1), L)
                child = expand(top, bottom_step)
                G = Graph(child)
                target = same_step(child, (0, L), (1, L+1), 8)
                row, detail = analyze(G, target, True)
                assert row["arcs"] == [3, 3]
                records.append(dict(L=L, top_partner=j, bottom_partner=k,
                                    base_graph=base, base_row=root_row, intermediate_graph=top,
                                    intermediate_row=top_row, graph=child, row=row,
                                    cycles=G.cycles(), families=detail["families"],
                                    toggles=detail["toggles"], bridge=detail["b"]))
    return dict(construction="two cap expansions protecting the original rung pair",
                steps=len(records), high_loss=[i for i, z in enumerate(records) if z["row"]["ell"] >= 2],
                histogram=dict(sorted(Counter(str(tuple(z["row"][k] for k in ("ell", "t", "eta")))
                                              for z in records).items())), records=records)


def cut_octagons():
    mandatory()
    results = []
    for L in (4, 6, 8, 10):
        base = prism(L)
        g = Graph(base)
        g.validate()
        source_step = same_step(base, (0, L), (1, L+1), 4)
        base_row, bd = analyze(g, source_step, True)
        first, map1, trans1, tries1 = splice(base, 0, prism(4), 0)
        e = edge(L, map1[L])
        middle_step = same_step(first, e, (1, L+1), 6)
        mid = Graph(first)
        mid_row, md = analyze(mid, middle_step, True)
        second, map2, trans2, tries2 = splice(first, L+1, prism(4), 0)
        f = edge(1, map2[1])
        target = same_step(second, e, f, 8)
        G = Graph(second)
        row, dd = analyze(G, target, True)
        assert row["arcs"] == [3, 3]
        assert row["ell"] == mid_row["ell"] == base_row["ell"] == L-3
        # Directly verify the survival-spanning kernel mechanism at both cuts.
        cut_checks = []
        for small, large, small_d, large_d, vertex, mapping in (
            (g, mid, bd, md, 0, map1), (mid, G, md, dd, L+1, map2)):
            survivor = small_d["families"]["N10"]+small_d["families"]["N01"]+small_d["families"]["N11"]
            ports = sorted(mapping)
            signatures = {tuple(C[small.eid[edge(vertex, a)]] for a in ports) for C in survivor}
            assert signatures == {(0, 1, 1), (1, 0, 1), (1, 1, 0)}
            projection = [project_cycle(small, large, vertex, mapping, C) for C in large.cycles()]
            assert set(projection) == set(small.cycles())
            kd = rank(differences(large.cycles()))-rank(differences(small.cycles()))
            assert rank(large_d["L"])-rank(small_d["L"]) == kd == 3
            cut_checks.append(dict(signatures=sorted(signatures), kernel_dimension=kd))
        L0, V, U = dd["L0"], dd["V"], dd["U"]
        # Select and retain actual old-direction and residual generators,
        # together with exact independent rank increments.
        old_basis, old_added = list(L0), []
        for v in V:
            if rank(old_basis+[v]) > rank(old_basis):
                old_added.append(v)
                old_basis.append(v)
        recovered, u_added = list(L0), []
        for a in U:
            if rank(recovered+[a]) > rank(recovered):
                u_added.append(a)
                recovered.append(a)
        assert row["t"] >= row["ell"]-1
        assert row["delta_R"] >= row["delta_V"]+row["epsilon"]-1
        beta = add(dd["families"]["Pux"][0], dd["families"]["Pvy"][0],
                   dd["families"]["D11"][0], scale(2, add(G.unit(*e), G.unit(*f))),
                   scale(-1, dd["families"]["N10"][0]),
                   scale(-1, dd["families"]["N01"][0]),
                   scale(-1, dd["families"]["N11"][0]))
        c = add(dd["families"]["N00"][0], scale(-1, dd["families"]["N10"][0]),
                scale(-1, dd["families"]["N01"][0]), dd["families"]["N11"][0])
        sep = solve(dd["L"]+dd["U"]+[dd["b"]],
                    [0]*(len(dd["L"])+len(dd["U"]))+[1], G.m) if row["eta"] else None
        results.append(dict(L=L, base_graph=base, base_row=base_row,
                            intermediate_graph=first, intermediate_row=mid_row,
                            graph=second, row=row, e=e, f=f,
                            first_mapping=sorted(map1.items()), second_mapping=sorted(map2.items()),
                            rotation_attempts=[tries1, tries2], cut_checks=cut_checks,
                            cycles=G.cycles(), families=dd["families"],
                            toggles=dd["toggles"], old_basis_mod_L0=old_added,
                            U_basis_mod_L0=u_added, bridge=dd["b"], beta=beta, c=c,
                            bridge_separator=list(map(str, sep)) if sep else None))
    return dict(construction="cube vertex splices at opposite square corners",
                records=results, steps=len(results),
                high_loss_cases=sum(z["row"]["ell"] >= 2 for z in results))


def residual_certificates():
    results = []
    for record in cut_octagons()["records"]:
        L = record["L"]
        g = Graph(record["graph"])
        row, data = analyze(g, record["row"]["step"], True)
        # Label-independent core coordinates are precisely the prism edges
        # not incident with either replaced vertex.
        base = Graph(record["base_graph"])
        core = [i for i, e in enumerate(g.edges)
                if e in base.eid and 0 not in e and L+1 not in e]
        local = [i for i in range(g.m) if i not in core]
        N0 = data["families"]["N00"][0]
        chosen = [N for N in data["families"]["N00"] if all(N[i] == N0[i] for i in local)]
        assert len(chosen) == L-3
        P0 = next(P for P in data["families"]["Pux"] if all(P[i] == N0[i] for i in core)
                  and all(P[i] == N0[i] for i, e in enumerate(g.edges)
                          if any(v >= 2*L+8 for v in e)))
        offset = sub(P0, N0)
        assert all(offset[i] == 0 for i in core)
        translated = [add(N, offset) for N in chosen]
        assert all(P in data["families"]["Pux"] for P in translated)
        directions = differences(chosen)
        assert differences(translated) == directions
        assert rank(data["L"]+directions)-rank(data["L"]) == L-4
        # Every compatible old family is empty, but these are residual paths.
        assert all(a["good_count"] == 0 for a in row["classes"].values())
        assert row["delta_V"] == L-4 and row["epsilon"] == 1
        assert row["delta_R"] >= L-4
        toggle_summary = {}
        for name in ("Pux", "Pvy", "D11"):
            selected = [t for t in data["toggles"] if t["family"] == name]
            toggle_summary[name] = dict(
                nonbinary=sum(not t["binary"] for t in selected),
                binary_component_histogram=dict(sorted(Counter(str(len(t["components"]))
                                                               for t in selected if t["binary"]).items())))
        results.append(dict(L=L, graph=record["graph"], row=row, N0=N0, P0=P0,
                            translation_offset=offset, old_cycles=chosen, residual_paths=translated,
                            recovered_directions=directions, rank_mod_L=L-4,
                            toggle_summary=toggle_summary))
    return dict(scope="explicit residual translation on all four cut-octagon checks", records=results)


def cut_projection():
    results = []
    for record in cut_octagons()["records"]:
        L = record["L"]
        base, mid, g = (Graph(record[k]) for k in ("base_graph", "intermediate_graph", "graph"))
        mapping1, mapping2 = dict(record["first_mapping"]), dict(record["second_mapping"])
        def pi(C):
            return project_cycle(base, mid, 0, mapping1,
                                 project_cycle(mid, g, L+1, mapping2, C))
        source, bd = analyze(base, record["base_row"]["step"], True)
        row, dd = analyze(g, record["row"]["step"], True)
        projected_families = {}
        for key, rows in dd["families"].items():
            counts = Counter(pi(C) for C in rows)
            assert set(counts) == set(bd["families"][key]), key
            assert set(counts.values()) == {4}, key
            projected_families[key] = dict(vectors=sorted(counts), fibre_size=4)
        assert rank(bd["L"]+bd["V"]+[sub(pi(dd["b"]), bd["b"])]) == rank(bd["L"]+bd["V"])
        assert all(pi(v) in differences(bd["families"]["Pux"]) or
                   rank(bd["V"]+[pi(v)]) == rank(bd["V"]) for v in dd["U"])
        # Explicit cube-minus-0 local path lists in prism(4) labels.
        cube = Graph(prism(4))
        deleted = [i for i, e in enumerate(cube.edges) if 0 in e]
        all_local = {}
        # Use an independent simple-path traversal on seven vertices.
        for a, b in ((1, 4), (3, 4), (1, 3)):
            paths = []
            def walk(path):
                if len(path) == 7:
                    if path[-1] == b:
                        paths.append(path)
                    return
                if path[-1] == b:
                    return
                for w, i in cube.adj[path[-1]]:
                    if i not in deleted and w not in path:
                        walk(path+[w])
            walk([a])
            assert len(paths) == 2
            all_local[str((a, b))] = sorted(paths)
        results.append(dict(L=L, graph=record["graph"], base_graph=record["base_graph"],
                            row=row, source_row=source, projected_families=projected_families,
                            projected_bridge=pi(dd["b"]), source_bridge=bd["b"],
                            bridge_quotient_scalar=str(Q(L, L-2)),
                            local_cube_paths=all_local,
                            exact_dimensions=dict(d=L+7, L=10, L0=8, L0V=L+4,
                                                  L0U=L+4, L0VU=L+4)))
        assert rank(dd["L0"]+dd["V"]) == rank(dd["L0"]+dd["U"]) == rank(dd["L0"]+dd["V"]+dd["U"]) == L+4
    return dict(statement="all seven classes project bijectively with constant fibre four",
                records=results)
