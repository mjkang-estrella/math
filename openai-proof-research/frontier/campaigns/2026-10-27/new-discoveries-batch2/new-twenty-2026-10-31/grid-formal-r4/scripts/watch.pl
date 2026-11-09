use strict; use warnings; use POSIX qw(setsid WNOHANG); use Time::HiRes qw(time sleep);
my $start=time; my $pid=fork(); die unless defined $pid;
if(!$pid){setsid(); exec @ARGV; die "exec: $!";}
my $peak=0; my $status;
while(1){
 my $rss=0; open(my $ps,"-|","ps","-eo","pgid=,rss=") or die;
 while(<$ps>){$rss+=$2 if /^\s*(\d+)\s+(\d+)/ && $1==$pid;} close $ps;
 $peak=$rss if $rss>$peak;
 if($rss>6*1024*1024 || time-$start>140){kill 9,-$pid; waitpid($pid,0);$status=137;last;}
 if(waitpid($pid,WNOHANG)==$pid){$status=($? & 127) ? 128+($? & 127) : $? >> 8;last;} sleep .1;
}
printf STDERR "RESOURCE wall_s=%.3f peak_rss_kib=%d exit=%d\n",time-$start,$peak,$status;
exit $status;
