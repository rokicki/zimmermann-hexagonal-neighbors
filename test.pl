my @dx = qw(1 1 0 -1 -1 0) ;
my @dy = qw(1 0 -1 -1 0 1) ;
sub popit {
   return if !@a ;
   $n = (@a + 1) / 2 ;
   $nn = @a ;
   my $i ;
   my $j ;
   my $errors = 0 ;
   for ($i=0; $i<@a; $i++) {
      for ($j=0; $j<@a; $j++) {
         %seen = () ;
         for ($d=0; $d<6; $d++) {
            my $ii = $i + $dx[$d] ;
            my $jj = $j + $dy[$d] ;
            if ($ii >= 0 && $jj >= 0 && $ii < $nn && $jj < $nn) {
               $seen{substr($a[$ii], $jj, 1)}++ ;
            }
         }
         my $c = substr($a[$i], $j, 1) ;
         if ('2' le $c && $c le '7') {
            for ($d=1; $d<$c; $d++) {
               if (!$seen{$d}) {
                  print "Error at $i $j val $c missing $d\n" ;
                  $errors++ ;
               }
            }
         }
      }
   }
   print "Errors $errors\n" ;
   @a = () ;
}
while (<>) {
   if (/ /) {
      popit() ;
      @a = () ;
   } elsif (!/ /) {
      push @a, $_ ;
   }
}
popit() ;
