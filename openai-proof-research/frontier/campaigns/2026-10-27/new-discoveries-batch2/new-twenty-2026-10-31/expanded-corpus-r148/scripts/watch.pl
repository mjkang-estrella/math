use strict; use warnings; use POSIX qw(setpgid WNOHANG); use Time::HiRes qw(time sleep);
my $pid=fork(); die 'fork' unless defined $pid;
if(!$pid){setpgid(0,0); exec @ARGV; die 'exec';}
my $start=time(); my $peak=0;
while(1){my $done=waitpid($pid,WNOHANG); if($done==$pid){my $s=$?; print STDERR "watchdog elapsed=".(time()-$start)." peak_kib=$peak status=$s\n"; exit($s&127 ? 128+($s&127) : $s>>8);}
my $rss=0; for my $f(glob('/proc/[0-9]*/stat')){open my $h,'<',$f or next; my $v=<$h>; close $h; next unless $v =~ /^\d+ \(.*\) (.*)$/; my @a=split / /,$1; next unless $a[2]==$pid; $rss += $a[21]*4;}
$peak=$rss if $rss>$peak;
if($rss>6*1024*1024 || time()-$start>140){kill 'KILL',-$pid; waitpid($pid,0); print STDERR "watchdog KILLED rss_kib=$rss elapsed=".(time()-$start)."\n";exit 124;} sleep .1;}
