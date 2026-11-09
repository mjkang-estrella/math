import pathlib,sys
D=pathlib.Path(__file__).resolve().parents[1];sys.dont_write_bytecode=True;sys.path.insert(0,str(D.parent/'expanded-corpus-r58/deps'));sys.path.insert(0,str(D/'scripts'));import networkx as nx,finite
finite.graphs=lambda mode:((len(g),list(g.edges()),'atlas-'+str(i)) for i,g in enumerate(nx.graph_atlas_g()) if len(g))
finite.run(sys.argv[1])
