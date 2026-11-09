use strict; use warnings; use POSIX qw(setpgid WNOHANG);
my $child = fork(); die 'fork failed' unless defined $child;
if (!$child) {setpgid(0,0); exec @ARGV; die 'exec failed';}
my $start=time; my $peak=0;
while (1) {
 my $done=waitpid($child,WNOHANG);
 if ($done==$child) {my $status=$?; print STDERR "CAP peak_kib=$peak wall=".(time-$start)."\n"; exit(($status & 127) ? 128+($status & 127) : $status >> 8);}
 my @todo=($child); my $rss=0;
 while (@todo) {my $p=shift @todo;
  if(open(my $f,'<',"/proc/$p/status")){while(<$f>){$rss+=$1 if /^VmRSS:\s+(\d+)/;}close $f;}
  if(open(my $f,'<',"/proc/$p/task/$p/children")){my $v=<$f>; push @todo, split /\s+/,($v // ''); close $f;}
 }
 $peak=$rss if $rss>$peak;
 if ($rss>6291456 || time-$start>=140) {kill 'KILL',-$child; waitpid($child,0); print STDERR "CAP LIMIT rss=$rss\n"; exit 124;}
 select undef,undef,undef,0.1;
}
