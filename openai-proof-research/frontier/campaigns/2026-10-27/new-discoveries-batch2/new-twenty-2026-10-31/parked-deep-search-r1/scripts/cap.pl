use strict; use warnings; use POSIX qw(:sys_wait_h setpgid); use Time::HiRes qw(time sleep);
my $pid=fork(); die unless defined $pid;
if (!$pid) {setpgid(0,0); exec 'bash','-c','ulimit -t 120; exec taskset -c 0,1 "$@"','cap',@ARGV; die $!;}
my $start=time; my $peak=0;
while (1) {my $done=waitpid($pid,WNOHANG); if ($done==$pid) {my $s=$?; print STDERR "WATCHDOG wall=",time-$start," peak_kib=$peak status=$s\n"; exit($s&127 ? 128+($s&127) : $s>>8);}
my $rss=0; if(open my $f,'<',"/proc/$pid/status") {while(<$f>){$rss=$1 if /^VmRSS:\s+(\d+)/;} close $f;} $peak=$rss if $rss>$peak;
if(time-$start>140 || $rss>6*1024*1024) {kill 'KILL',-$pid; waitpid($pid,0); die "WATCHDOG limit wall/rss\n";} sleep .05;}
