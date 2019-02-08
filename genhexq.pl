my $n = shift ;
my $nn = 2 * $n - 1 ;
for ($i=0; $i<$nn; $i++) {
   for ($j=0; $j<$nn; $j++) {
      if (abs($i-$j) >= $n) {
         print "." ;
      } else {
         print "?" ;
      }
   }
   print "\n" ;
}
