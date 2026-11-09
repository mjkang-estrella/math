use strict; use warnings; use POSIX qw(setsid WNOHANG);
my $pid=fork(); die "fork" unless defined $pid;
if (!$pid) { setsid(); $ENV{MALLOC_ARENA_MAX}=2; exec 'bash','-c','ulimit -t 120; exec taskset -c 0,1 "$@"','guard',@ARGV; die "exec"; }
my $start=time; my $peak=0; my $reason='';
while (1) {
 my $r=waitpid($pid,WNOHANG); if ($r==$pid) { my $s=$?; print STDERR "GUARD peak_kib=$peak elapsed=".(time-$start)." status=$s reason=$reason\n"; exit($s&127 ? 128+($s&127) : $s>>8); }
 my $rss=0;
 for my $p (glob('/proc/[0-9]*/stat')) {
  open(my $f,'<',$p) or next; my $v=<$f>; close $f;
  next unless defined($v); next unless $v =~ /^\d+ \(.*\) (.*)$/; my @a=split / /,$1;
  next unless $a[2]==$pid;
  $rss+=$a[21]*4;
 }
 $peak=$rss if $rss>$peak;
 if ($rss>6*1024*1024 || time-$start>=140) { $reason=$rss>6*1024*1024?'RSS':'WALL'; kill 'KILL',-$pid; }
 select undef,undef,undef,0.05;
}
