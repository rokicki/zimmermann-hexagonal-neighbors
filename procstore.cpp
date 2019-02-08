#include <iostream>
#include <map>
#include <set>
#include <algorithm>
#include <fstream>
#include <cstring>
#include <cstdlib>
#include <vector>
#include <math.h>
#include <sys/time.h>
using namespace std ;
typedef long long ll ;
typedef unsigned long long ull ;
int board[64][64] ;
int done[64][64] ;
int qdone[64][64] ;
int w, h, o, n, hi, lev ;
int dx[] = { 1, 1, 0, -1, -1, 0 } ;
int dy[] = { 1, 0, -1, -1, 0, 1 } ;
const char *fn ;
void error(const char *s) {
   cerr << s << endl << flush ;
   exit(0) ;
}
const char *infile ;
void clear() {
   for (int i=0; i<64; i++)
      for (int j=0; j<64; j++) {
         board[i][j] = -1 ;
         done[i][j] = 0 ;
         qdone[i][j] = 0 ;
      }
   hi = 0 ;
}
set<string> seen ;
int processed ;
int comparerev(const string s) {
   int f = 0 ;
   int b = s.size() - 1 ;
   while (f < b && s[f] == s[b]) {
      f++ ;
      b-- ;
   }
   return s[f] - s[b] ;
}
ll tries = 0 ;
void processit(int xx, int xy, int yx, int yy) {
   vector<string> a ;
   a.push_back("") ;
   for (int x1=-n+1; x1<n; x1++) {
      string s ;
      for (int y1=-n+1; y1<n; y1++) {
         int z = x1 - y1 ;
         if (abs(z) >= n)
            continue ;
         int x = n + x1 * xx + y1 * xy ;
         int y = n + x1 * yx + y1 * yy ;
         if (x < 1 || x > w || y < 1 || y > w)
            error("! bad coordinate transform") ;
         if (board[y][x] == -1) {
            s.push_back('.') ;
         } else {
            s.push_back('0'+board[y][x]) ;
         }
      }
      a.push_back(s) ;
   }
   a.push_back("") ;
   for (int i=0; i+2<a.size(); i++) {
      vector<string> b ;
      for (int j=0; j<3; j++)
         b.push_back(a[i+j]) ;
      if (b[0].size() == b[2].size()) {
         string s0 = b[0] ;
         string s2 = b[2] ;
         int t0 = comparerev(b[0]) ;
         int t2 = comparerev(b[2]) ;
         if (t0 > 0)
            reverse(s0.begin(), s0.end()) ;
         if (t2 > 0)
            reverse(s2.begin(), s2.end()) ;
         if (s0 > s2) {
            reverse(b.begin(), b.end()) ;
            swap(t0, t2) ;
            if (t0 > 0)
               for (int i=0; i<3; i++)
                  reverse(b[i].begin(), b[i].end()) ;
         } else if (s0 == s2) {
            if (comparerev(b[1]) > 0) {
               for (int i=0; i<3; i++)
                  reverse(b[i].begin(), b[i].end()) ;
            }
         } else {
            if (t0 > 0)
               for (int i=0; i<3; i++)
                  reverse(b[i].begin(), b[i].end()) ;
         }
      } else {
         if (b[0].size() > b[2].size())
            reverse(b.begin(), b.end()) ;
         int t1 = comparerev(b[2]) ;
         if (t1 == 0) {
            t1 = comparerev(b[1]) ;
            if (t1 == 0) {
               t1 = comparerev(b[0]) ;
            }
         }
         if (t1 > 0) {
            for (int i=0; i<3; i++)
               reverse(b[i].begin(), b[i].end()) ;
         }
      }
      string s = b[0] + "/" + b[1] + "/" + b[2] ;
      tries++ ;
      if (seen.insert(s).second)
         cout << "ROW3 " << hi << " " << s << endl << flush ;
   }
}
vector<string> split(string s, char sep = ' ') {
   vector<string> r ;
   string a ;
   for (int i=0; i<s.size(); i++)
      if (s[i] == sep) {
         if (a.size()) {
            r.push_back(a) ;
            a.clear() ;
         }
      } else {
         a.push_back(s[i]) ;
      }
   if (a.size())
      r.push_back(a) ;
   return r ;
}
map<string, vector<string> > db ;
map<string, string> paths ;
void processit(const vector<string> &lins, string &hash, const string &path) {
   int linecnt = lins.size() ;
   if (hash.size()) {
      db[hash] = lins ;
      paths[hash] = path ;
   }
   processed++ ;
   w = linecnt ;
   h = linecnt ;
   n = (w + 1) / 2 ;
   if (linecnt < 3 || (linecnt & 1) == 0)
      error("! bad input lines?") ;
   vector<string> prev = split(path, '-') ;
   for (int p=prev.size()-2; p >= 0; p -= 2) {
      if (p & 1)
         error("! odd p") ;
      for (int j=1; j<=h; j++)
         for (int i=1; i<=w; i++)
            if (board[j][i] > 0)
               board[j][i]++ ;
      if (db.find(prev[p]) == db.end()) {
         cerr << "Skipping " << hash << " in " << fn << " could not find " << prev[p] << endl ;
         clear() ;
         return ;
      }
      vector<string> &pv = db[prev[p]] ;
      for (int j=1; j<=h; j++)
         for (int i=1; i<=w; i++)
            if (pv[j-1][i-1] == '1') {
               if (board[j][i] != -1)
                  error("! mistake; expected -1") ;
               board[j][i] = 1 ;
            } else if (pv[j-1][i-1] == '2') {
               if (board[j][i] < 2) {
 cerr << "Input had a 2 at location board was " << board[j][i] << endl ;
                  error("! mistake; expected 2+") ;
               }
            } else if (pv[j-1][i-1] == '.') {
               if (board[j][i] != -1)
                  error("! mistake; expected -1 again") ;
            } else {
               error("! saw char other than 1 2 .") ;
            }
      hi++ ;
   }
   processit(1, 0, 0, 1) ;
   processit(0, 1, 1, 0) ;
   processit(-1, 1, 0, 1) ;
   clear() ;
}
int main(int argc, char *argv[]) {
   srand48(time(0)) ;
   int expecthash = 0 ;
   for (int i=1; i<argc; i++) {
      fn = argv[1] ;
      if (strncmp(argv[i], "STORE-", 6) == 0)
         expecthash = 1 ;
      istream *myfile = 0 ;
      ifstream myffile ;
      if (strcmp("-", fn) == 0) {
         myfile = &cin ;
      } else {
         myffile.open(argv[i]) ;
         myfile = &myffile ;
      }
      vector<string> havelines ;
      string lin ;
      string hash ;
      string path ;
      clear() ;
      while (getline(*myfile, lin)) {
         if (lin.size() == 0)
            error("! bad line") ;
         if (expecthash && lin[0] == 'H') {
            if (havelines.size()) {
               processit(havelines, hash, path) ;
               havelines.clear() ;
               hash.clear() ;
               path.clear() ;
            }
            vector<string> f = split(lin) ;
            hash = f[1] ;
            if (f.size() > 2)
               path = f[2] ;
            else
               path.clear() ;
            continue ;
         }
         int seespace = 0 ;
         for (int i=0; i<lin.size(); i++)
            if (lin[i] == ' ') {
               seespace++ ;
               break ;
            }
         if (seespace) {
            if (havelines.size()) {
               processit(havelines, hash, path) ;
               havelines.clear() ;
               hash.clear() ;
               path.clear() ;
            }
            continue ;
         }
         int j = havelines.size() + 1 ;
         for (int i=0; i<lin.size(); i++)
            if (lin[i] >= '0' && lin[i] <= '9') {
               board[j][i+1] = lin[i]-'0' ;
               if (board[j][i+1] > hi)
                  hi = board[j][i+1] ;
            } else if (lin[i] == '.') {
               board[j][i+1] = -1 ;
            }
         havelines.push_back(lin) ;
      }
      if (havelines.size()) {
         processit(havelines, hash, path) ;
         havelines.clear() ;
         hash.clear() ;
         path.clear() ;
         hi = 0 ;
      }
   }
   cout << "Total distinct is " << seen.size() << " out of " << tries << endl ;
}
