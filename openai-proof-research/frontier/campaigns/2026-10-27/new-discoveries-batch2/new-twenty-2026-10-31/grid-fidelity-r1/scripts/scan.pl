use strict; use warnings;
for my $f (@ARGV) {
 open my $in,'<',$f or die $!; local $/; my $s=<$in>;
 my ($i,$line,$depth)=(0,1,0);
 while($i<length($s)){
  my $two=substr($s,$i,2);my $c=substr($s,$i,1);
  if($depth){if($two eq '/-'){$depth++;$i+=2}elsif($two eq '-/'){$depth--;$i+=2}else{$line++ if $c eq "\n";$i++} next}
  if($two eq '/-'){$depth=1;$i+=2;next}
  if($two eq '--'){ $i++ while $i<length($s) && substr($s,$i,1) ne "\n";next }
  if($c eq '"'){$i++;while($i<length($s)){my $ch=substr($s,$i++,1);$line++ if $ch eq "\n";if($ch eq '\\'){$i++}elsif($ch eq '"'){last}}next}
  if(substr($s,$i)=~/\A([A-Za-z_][A-Za-z_0-9]*)/){my $t=$1;print "$f:$line:$t\n" if $t =~ /^(sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool|implemented_by|extern)$/;$i+=length($t);next}
  $line++ if $c eq "\n";$i++;
 }
}
