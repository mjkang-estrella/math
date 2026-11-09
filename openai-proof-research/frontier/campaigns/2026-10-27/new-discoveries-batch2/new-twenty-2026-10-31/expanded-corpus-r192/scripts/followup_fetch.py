import pathlib,runpy,sys
D=pathlib.Path(__file__).resolve().parents[1]
sys.argv=[str(D/'scripts/fetch.py'),'supersimple-exact-followup','https://arxiv.org/pdf/1410.4785','morotti-vor-denied','https://www.sciencedirect.com/science/article/pii/S0021869315005888','tadpole-vor','https://doi.org/10.1088/0951-7715/28/7/2343','jordan-vor','https://doi.org/10.1016/j.laa.2018.01.017'];runpy.run_path(sys.argv[0],run_name='__main__')
