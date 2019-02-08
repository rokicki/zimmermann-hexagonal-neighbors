#
#   Encode the hex Al Zimmermann problem as a SAT problem.
#
#   Variable names are as follows.  We use symbolic names and
#   linearize them later, but we always use a specific initial
#   ordering to make it easy to extract the solution.
#
my $hi = shift ;
my $sf = shift ;
my $h = 0 ;
while (<>) {
   chomp ;
   $lin = $_ ;
   for ($i=0; $i<length($lin); $i++) {
      $w = $i+1 if $i >= $w ;
      $b[$h][$i] = substr($lin, $i, 1) ;
   }
   $h++ ;
}
open F, $sf or die "Can't read $sf" ;
$lin = <F> ;
close F ;
chomp $lin ;
@f = split " ", $lin ;
for (@f) {
   $seen{$_}++ ;
}
sub good {
   my $i = shift ;
   my $j = shift ;
   return 0 if $i < 0 || $j < 0 || $i >= $h || $j >= $w || $b[$i][$j] eq '.' ;
   return 1 ;
}
$base = 0 ;
for ($i=0; $i<$h; $i++) {
   for ($j=0; $j<$w; $j++) {
      if (good($i, $j)) {
         $known = ($b[$i][$j] ne '?') ;
         if ($known) {
            print $b[$i][$j] ;
            $sc += $b[$i][$j] ;
         } else {
            $seen = 0 ;
            for ($v=1; $v<$hi; $v++) {
               if ($seen{$base+$v}) {
                  print "$v" ;
                  $sc += $v ;
                  $seen |= 1<<$v ;
               }
            }
            if ($seen == 0) {
               print "$hi" ;
               $sc += $hi ;
            }
            $base += $hi-1 ;
         }
      } else {
         print "." ;
      }
   }
   print "\n" ;
}
print "Score $sc\n" ;
