exec((__import__('pathlib').Path(__file__).parent/'refresh.py').read_text().split('coverage={}')[0])
get('arrangement.html','https://arxiv.org/html/2610.33653v1')
get('arrangement-abs.html','https://arxiv.org/abs/2610.33653')
get('clopen-arrangement.html','https://clopen.solutions/?q=arrangement')
