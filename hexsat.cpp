#include <iostream>
#include <algorithm>
#include <cstdio>
#include <vector>
using namespace std ;
typedef long long ll ;
/*
 *   Encode the hex Al Zimmermann problem as a SAT problem.
 *   This version supports any subset of the grid as unknown,
 *   and also supports a max cell value.  It's based on
 *   penalty rather than the total score.
 */
const int MAXN = 64 ;
const int MAXNN = 128 ;
int incremental, delta, w, h ;
int hi = 2 ;
int varn = 1 ;
int var[MAXNN][MAXNN][8] ;
int evar[MAXNN][MAXNN][6] ;
const int FALSE = 1000000000 ;
const int TRUE = -FALSE ;
char b[MAXNN][MAXNN] ;
void error(const char *s) {
   cerr << s << endl ;
   exit(10) ;
}
int ring(int i, int j) {
   int n = (h + 1) / 2 ;
   int ii = abs(i-n+1) ;
   int jj = abs(j-n+1) ;
   int kk = abs(i-j) ;
   if (jj > ii)
      ii = jj ;
   if (kk > ii)
      ii = kk ;
   return n - ii ;
}
int makevar() {
   return varn++ ;
}
int n(int v) {
   return -v ;
}
int truity(int v) {
   return (v == TRUE) ;
}
int notfalsity(int v) {
   return (v != FALSE) && (v != 0) ;
}
int bc(int v) {
   int r = 1 ;
   while (v >= (1 << r))
      r++ ;
   return r ;
}
void emit(const vector<int> &v) {
   for (auto it=v.begin(); it != v.end(); it++)
      if (truity(*it))
         return ;
   for (auto it=v.begin(); it != v.end(); it++)
      if (notfalsity(*it))
         printf(" %d", *it) ;
   printf(" 0\n") ;
}
void emit(int a) {
   emit(vector<int>({a})) ;
}
void emit(int a, int b) {
   emit(vector<int>({a,b})) ;
}
void emit(int a, int b, int c) {
   emit(vector<int>({a,b,c})) ;
}
void emit(int a, int b, int c, int d) {
   emit(vector<int>({a,b,c,d})) ;
}
void fulladder(int a, int b, int c, int d, int e) {
   emit(a, b, c, n(d)) ;
   emit(a, n(b), n(c), n(d)) ;
   emit(n(a), b, n(c), n(d)) ;
   emit(n(a), n(b), c, n(d)) ;
   emit(a, b, n(c), d) ;
   emit(a, n(b), c, d) ;
   emit(n(a), b, c, d) ;
   emit(n(a), n(b), n(c), d) ;
   emit(a, b, n(e)) ;
   emit(b, c, n(e)) ;
   emit(a, c, n(e)) ;
   emit(n(a), n(b), e) ;
   emit(n(c), n(b), e) ;
   emit(n(a), n(c), e) ;
}
int good(int i, int j) {
   if (i < 0 || j < 0 || i >= h || j >= w || b[i][j] == '.')
      return 0 ;
   return 1 ;
}
void twosort(int a, int b, int c, int d) {
   emit(n(a), c) ;
   emit(n(b), c) ;
   emit(n(a), n(b), d) ;
}
int checkzero(int k, int i, int j, int delta) {
   if (j == i)
      return makevar() ;
   k = (k & ((1 << i) - (1 << j))) ;
   if (k <= delta)
      return makevar() ;
   return FALSE ;
}
int dx[] = {1, 1,  0, -1, -1, 0} ;
int dy[] = {1, 0, -1, -1,  0, 1} ;
vector<pair<int, int>> tosum ;
vector<pair<int, int>> inner ;
int cleanring = 1000 ;
int symbreak = 0 ;
ll rings = -1 ;
vector<vector<pair<int, int> > > onevs ;
ll scanrings(const char *p) {
   int v = 0 ;
   ll r = 0 ;
   for (; ; p++) {
      if ('0' <= *p && *p <= '9') {
         v = 10 * v + *p - '0' ;
      } else if (*p == ',' || *p == 0) {
         r |= 1LL << v ;
         v = 0 ;
      } else {
         error("! bad ring argument") ;
      }
      if (*p == 0)
         break ;
   }
   return r ;
}
void counts(vector<pair<int, int>> &tsi, int delta) {
   if (tsi.size() > 0) {
      sort(tsi.begin(), tsi.end()) ;
      vector<int> tosum ;
      for (auto v : tsi)
         tosum.push_back(v.second) ;
      for (int i=1; tosum.size() > (1<<(i-1)); i++) {
         for (int j=i; j>0; j--) {
            vector<int> b = tosum ;
            if (i == j) {
               for (int k=0; k<tosum.size(); k++) {
                  int m = (k ^ ((1 << j) - 1)) ;
                  if (m > k && m < tosum.size()) {
                     b[k] = checkzero(k, i, j, delta) ;
                     b[m] = checkzero(m, i, j, delta) ;
                     twosort(tosum[k], tosum[m], b[k], b[m]) ;
                  }
               }
            } else {
               for (int k=0; k<tosum.size(); k++) {
                  int m = (k ^ (1 << (j - 1))) ;
                  if (m > k && m < tosum.size()) {
                     b[k] = checkzero(k, i, j, delta) ;
                     b[m] = checkzero(m, i, j, delta) ;
                     twosort(tosum[k], tosum[m], b[k], b[m]) ;
                  }
               }
            }
            tosum = b ;
         }
         if ((1 << (i - 1)) > delta) {
            vector<int> newsum ;
            for (int k=0; k<tosum.size(); k++) {
               if ((k & (1 << (i - 1))) == 0) {
                  newsum.push_back(tosum[k]) ;
               }
            }
            tosum = newsum ;
            i-- ;
         }
      }
      emit(n(tosum[delta])) ;
   }
}
int inneravail ;
ll onebits ;
int bc2(ll v) {
   int r = 0 ;
   while (v) {
      v &= v-1 ;
      r++ ;
   }
   return r ;
}
int main(int argc, char *argv[]) {
   while (argc > 2 && argv[1][0] == '-') {
      argc-- ;
      argv++ ;
      switch (argv[0][1]) {
case 'r':
         cleanring = atol(argv[1]) ;
         argc-- ;
         argv++ ;
         break ;
case 'I':
         inneravail = atol(argv[1]) ;
         argc-- ;
         argv++ ;
         break ;
case 'O':
         onebits = scanrings(argv[1]) ;
         argc-- ;
         argv++ ;
         break ;
case 'R':
         rings = scanrings(argv[1]) ;
         argc-- ;
         argv++ ;
         break ;
case 'b':
         symbreak = atol(argv[1]) ;
         argc-- ;
         argv++ ;
         break ;
case 'i': incremental++ ; break ;
case 'h':
         hi = atol(argv[1]) ;
         argc-- ;
         argv++ ;
         break ;
default: error("! bad argument") ;
      }
   }
   if (argc > 1)
      delta = atol(argv[1]) ;
   string under ;
   h = 0 ;
   while (getline(cin, under)) {
      int seespace = 0 ;
      for (auto c:under)
         if (c == ' ')
            seespace = 1 ;
      if (seespace)
         continue ;
      for (int i=0; i<under.size(); i++)
         b[h][i] = under[i] ;
      w = max(w, (int)under.size()) ;
      h++ ;
   }
   if (incremental)
      printf("p inccnf\n") ;
   else
      printf("p cnf 1 1\n") ;
   for (int i=0; i<h; i++) {
      for (int j=0; j<w; j++) {
         if (good(i, j)) {
            for (int k=1; k<hi; k++) {
               if (b[i][j] == '?') {
                  var[i][j][k] = makevar() ;
               } else {
                  if (b[i][j] - '0' == k)
                     var[i][j][k] = TRUE ;
                  else
                     var[i][j][k] = FALSE ;
               }
            }
         }
      }
   }
   for (int i=0; i<h; i++) {
      for (int j=0; j<w; j++) {
         if (good(i, j)) {
            for (int d=0; d<3; d++) {
               int ii = i + dx[d] ;
               int jj = j + dy[d] ;
               if (good(ii, jj)) {
                  int var = FALSE ;
                  int rr = ring(i,j)+ring(ii,jj) ;
                  if (delta > 0) {
                      if (rr < cleanring && ((rings >> rr) & 1) != 0) {
                         var = makevar() ;
                         tosum.push_back(make_pair(rr, var)) ;
                      } else if (inneravail) {
                         var = makevar() ;
                         inner.push_back(make_pair(rr, var)) ;
                      } else if (((onebits >> rr) & 1) != 0) {
                         var = makevar() ;
                         if (onevs.size() <= rr)
                            onevs.resize(rr+1) ;
                         onevs[rr].push_back(make_pair(rr, var)) ;
                      }
                  }
                  evar[i][j][d] = var ;
                  evar[ii][jj][d+3] = var ;
               }
            }
         }
      }
   }
   vector<int> v ;
   for (int i=0; i<h; i++) {
      for (int j=0; j<w; j++) {
         if (good(i, j)) {
            if (b[i][j] == '?') {
               for (int k=1; k<hi; k++)
                  for (int k2=k+1; k2<hi; k2++)
                     emit(n(var[i][j][k]), n(var[i][j][k2])) ;
            }
            for (int k=1; k<hi; k++) {
               v.clear() ;
               for (int d=0; d<6; d++) {
                  int ii = i + dx[d] ;
                  int jj = j + dy[d] ;
                  if (good(ii, jj))
                     v.push_back(var[ii][jj][k]) ;
               }
               for (int k2=1; k2<=k; k2++)
                  v.push_back(var[i][j][k2]) ;
               emit(v) ;
            }
            for (int d=0; d<3; d++) {
               if (evar[i][j][d] != 0) {
                  int ii = i + dx[d] ;
                  int jj = j + dy[d] ;
                  for (int k=1; k<hi; k++) {
                     emit(evar[i][j][d], n(var[i][j][k]), n(var[ii][jj][k])) ;
                  }
               }
            }
            for (int d1=0; d1<6; d1++) {
               if (evar[i][j][d1]) {
                  int ii = i + dx[d1] ;
                  int jj = j + dy[d1] ;
                  for (int d2=0; d2<d1; d2++) {
                     if (evar[i][j][d2]) {
                        int iii = i + dx[d2] ;
                        int jjj = j + dy[d2] ;
                        for (int k=1; k<hi; k++) {
                           v.clear() ;
                           if (ring(ii, jj) <= ring(iii, jjj))
                              v.push_back(evar[i][j][d1]) ;
                           else
                              v.push_back(evar[i][j][d2]) ;
                           for (int k2=1; k2<k; k2++)
                              v.push_back(var[i][j][k2]) ;
                           v.push_back(n(var[ii][jj][k])) ;
                           v.push_back(n(var[iii][jjj][k])) ;
                           emit(v) ;
                        }
                     }
                  }
               }
            }
         }
      }
   }
   if (symbreak) {
      int n = (h + 1) / 2 ;
      vector<int> v ;
      switch(symbreak) {
case 1:
         v.push_back(var[n-1][n-1][1]) ;
         emit(v) ;
         v[0] = var[n+2][n][1] ;
         emit(v) ;
         break ;
case 2:
         v.push_back(var[n-2][n-2][1]) ;
         emit(v) ;
         v[0] = var[n+1][n-1][1] ;
         emit(v) ;
         break ;
case 3:
         v.push_back(var[n-1][n-1][1]) ;
         v.push_back(var[n-2][n-2][1]) ;
         emit(v) ;
         v[0] = var[n+2][n][1] ;
         v[1] = var[n+1][n-1][1] ;
         emit(v) ;
         break ;
default:
         error("! bad symbreak") ;
      }
   }
   printf("\n") ;
   counts(tosum, delta-inneravail-bc2(onebits)) ;
   counts(inner, inneravail) ;
   for (int i=0; i<onevs.size(); i++)
      counts(onevs[i], 1) ;
}
