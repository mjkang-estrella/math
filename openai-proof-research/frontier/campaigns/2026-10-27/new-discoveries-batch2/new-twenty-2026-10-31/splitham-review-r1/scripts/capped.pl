use strict; use warnings; use POSIX qw(setpgid WNOHANG); use Time::HiRes qw(time sleep);
my $root='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/splitham-review-r1';
$ENV{TMPDIR}="$root/tmp"; $ENV{XDG_CACHE_HOME}="$root/cache"; $ENV{PYTHONDONTWRITEBYTECODE}=1; $ENV{MALLOC_ARENA_MAX}=2;
open my $fh,'<','/proc/self/status'; my $s=do{local $/;<$fh>}; $s =~ /Cpus_allowed_list:\s*(\d+)(?:-(\d+))?/; my $a=$1; my $cpus="$a,".($a+1);
my $pid=fork(); die 'fork' unless defined $pid;
if(!$pid){setpgid(0,0);exec 'prlimit','--cpu=120','--','taskset','-c',$cpus,@ARGV;die 'exec';}
my $t=time;my $max=0;my $reason='normal';
while(1){my $w=waitpid($pid,WNOHANG);if($w==$pid){my $rc=$?;print STDERR "watchdog: reason=$reason peak_group_rss_kib=$max wall=".(time-$t)." status=$rc cpus=$cpus\n";exit($rc>>8 || ($rc&127 ? 128+($rc&127):0));}
my $rss=0;for my $p(glob('/proc/[0-9]*')){open my $f,'<',"$p/stat" or next;my $st=<$f>;close $f;next unless $st =~ /^\d+ \(.*\) \S+ \d+ (\d+)/ && $1==$pid;open my $r,'<',"$p/status" or next;while(<$r>){$rss+=$1 if /^VmRSS:\s+(\d+)/;}close $r;}
$max=$rss if $rss>$max;if($rss>6*1024*1024 || time-$t>140){$reason=$rss>6*1024*1024?'rss':'wall';kill 9,-$pid;}sleep 0.1;
}
