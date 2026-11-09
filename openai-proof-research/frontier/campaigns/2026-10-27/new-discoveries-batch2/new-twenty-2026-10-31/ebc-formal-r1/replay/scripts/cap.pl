#!/usr/bin/perl
use strict; use warnings; use POSIX qw(:sys_wait_h setpgid);
my $pid=fork(); die "fork" unless defined $pid;
if (!$pid) { setpgid(0,0); exec @ARGV; die "exec: $!"; }
my $start=time; my $peak=0;
while (1) {
 my $done=waitpid($pid,WNOHANG);
 if ($done==$pid) {my $code=($? & 127) ? 128+($? & 127) : $? >> 8;
 print STDERR "CAP exit=$code peak_rss_kib=$peak wall_s=".(time-$start)."\n"; exit $code;}
 my @q=($pid); my $rss=0;
 while (@q) {my $p=shift @q; if(open(my $f,'<',"/proc/$p/status")){while(<$f>){$rss+=$1 if /^VmRSS:\s+(\d+)/;}close $f;}
 if(open(my $f,'<',"/proc/$p/task/$p/children")){my $s=<$f>; push @q, split /\s+/,($s // ''); close $f;}}
 $peak=$rss if $rss>$peak;
 if($rss>6*1024*1024 || time-$start>=140) {print STDERR "CAP FAILURE rss_kib=$rss elapsed=".(time-$start)."\n";kill 'KILL',-$pid;waitpid($pid,0);exit 124;}
 select undef,undef,undef,0.10;
}
