# statistics over all pseudo-chord arrangements (from chords.py machinery): demand inequalities
import sys,json,runpy,collections
sys.argv=['chords.py','0','1']
g=runpy.run_path(__file__.replace('chords_stats.py','chords.py'),run_name='lib')  # runs nothing for M=0? (loop empty)
