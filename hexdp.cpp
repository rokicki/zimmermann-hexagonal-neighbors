#include <iostream>
#include <map>
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
int templat[64][64] ;
int HI = 6 ;
int LO = 1 ;
int n, w, h ;
int minx=1, maxx=100 ;
int uniq = 0 ;
int bits, lowmask ;
int dx[] = { 1, 1, 0, -1, -1, 0 } ;
int dy[] = { 1, 0, -1, -1, 0, 1 } ;
int indshift[] = { 9, 6, 3, 18, 15, 12, 0 } ;
const int POW87 = 1LL << 21 ;
unsigned char penalty[POW87] ;
void error(const char *s) {
   cerr << s << endl << flush ;
   exit(0) ;
}
static double start ;
double walltime() {
   struct timeval tv ;
   gettimeofday(&tv, 0) ;
   return tv.tv_sec + 0.000001 * tv.tv_usec ;
}
double duration() {
   double now = walltime() ;
   double r = now - start ;
   start = now ;
   return r ;
}
void showboard() {
   for (int y=1; y<=h; y++) {
      for (int x=1; x<=w; x++) {
         if (board[y][x] < 0)
            cout << "." ;
         else
            cout << (int)board[y][x] ;
      }
      cout << endl ;
   }
}
void getneighbor(int x, int y, int d, int &xx, int &yy) {
   xx = x + dx[d] ;
   yy = y + dy[d] ;
}
int getpenaltyind(int x, int y) {
   int ind = 0 ;
   int xx, yy ;
   for (int d=0; d<6; d++) {
      getneighbor(x, y, d, xx, yy) ;
      ind = (ind << 3) + board[yy][xx] + 1 ;
   }
   return (ind << 3) + board[y][x] + 1 ;
}
int getpenalty(int x, int y) {
   return penalty[getpenaltyind(x, y)] ;
}
int opt, nonz ;
int tcnt[9] ;
void recurpenalty(int togo, int at) {
   if (togo == 1) {
      int hi = 1 ;
      int zeros = tcnt[1] ;
      while (hi <= HI && (zeros > 0 || tcnt[1+hi])) {
         hi++ ;
         if (tcnt[hi] == 0)
            zeros-- ;
      }
      for (int i=-1; i<=HI; i++) {
         if (i > hi) {
            penalty[8*at+i+1] = 100 ;
         } else {
            int p = 0 ;
            for (int j=1; j<i; j++)
               if (tcnt[1+j] > 1)
                  p += 2 * (tcnt[1+j] - 1) ;
            if (i > 0 && tcnt[1+i] && i < HI) {
               if (uniq)
                  p = 100 ;
               else
                  p += tcnt[1+i] ;
            }
            penalty[8*at+i+1] = p ;
         }
      }
   } else {
      for (int i=-1; i<=HI; i++) {
         tcnt[i+1]++ ;
         recurpenalty(togo-1, 8*at+i+1) ;
         tcnt[i+1]-- ;
      }
   }
}
void improvepen() {
   for (int i=0; i<POW87; i += 8) {
      int base = i + 1 ;
      int lo = 1000 ;
      for (int j=LO; j<=HI; j++)
         if (penalty[base+j] < lo)
            lo = penalty[base+j] ;
      if (penalty[base] < lo) {
         penalty[base] = lo ;
      }
   }
}
typedef ull row_t ;
void unpack(int y, const row_t &rt) {
   int shv = 0 ;
   for (int i=minx; i<=w && i<=maxx; i++)
      if (templat[y][i] == 0) {
         board[y][i] = LO + ((rt >> shv) & lowmask) ;
         shv += bits ;
      }
   if (shv > 64)
      error("! too many bits") ;
   if (rt >> shv) {
 cout << "RT " << rt << " shv " << shv << endl ;
      error("! some bits ignored") ;
   }
}
row_t pack(int y) {
   int shv = 0 ;
   row_t r = 0 ;
   for (int i=minx; i<=w && i<=maxx; i++) {
      if (templat[y][i] == 0) {
         if (board[y][i] == 0)
            error("! bad pack") ;
         r += ((row_t)(board[y][i] - LO)) << shv ;
         shv += bits ;
      }
   }
   if (shv > 64)
      error("! too many bits") ;
   return r ;
}
const char *infile ;
typedef pair<row_t, row_t> mkey_t ;
typedef vector<ull> rowdat ;
typedef map<mkey_t, rowdat> lev_t ;
int top ;
ll curcnts[210] ;
ll totsize ;
ll maxcnt = 1000000000000000LL ;
int maxwrite ;
void recur(int x, int y, int pen, const row_t &pr, lev_t &nextlev,
           int minpen, const rowdat &rd) {
   while (x <= w && templat[y][x] != 0)
      x++ ;
   if (x > w || x > maxx) {
      if (pen & 1)
         error("! bad pen?") ;
      pen >>= 1 ;
      if (pen > maxwrite)
         return ;
      curcnts[pen]++ ;
      totsize++ ;
      while (maxwrite > 0 && totsize > maxcnt) {
         totsize -= curcnts[maxwrite] ;
         maxwrite-- ;
      }
      row_t tr = pack(y) ;
      mkey_t key = make_pair(pr, pack(y)) ;
      auto it = nextlev.find(key) ;
      int nhi = min(maxwrite, (int)(rd.size()-1+pen-minpen)) ;
      if (it == nextlev.end()) {
         vector<ull> nv(nhi+1) ;
         for (int i=minpen; i+pen-minpen<nv.size() && i<rd.size(); i++)
            nv[i+pen-minpen] = rd[i] ;
         nextlev[key] = nv ;
      } else {
         vector<ull> &v = it->second ;
         if (v.size() <= nhi)
            v.resize(nhi+1) ;
         for (int i=minpen; i+pen-minpen<(int)v.size() && i<rd.size(); i++)
            v[i+pen-minpen] += rd[i] ;
      }
      return ;
   }
   int op[7], opind[7] ;
   opind[6] = getpenaltyind(x, y) ;
   op[6] = penalty[opind[6]] ;
   int xx, yy ;
   for (int d=0; d<6; d++) {
      xx = x + dx[d] ;
      yy = y + dy[d] ;
      if (board[yy][xx] < 0)
         continue ;
      opind[d] = getpenaltyind(xx, yy) ;
      op[d] = penalty[opind[d]] ;
   }
   int np = 0 ;
   for (int i=HI; i>=LO; i--) {
      board[y][x] = i ;
      int mnpind = opind[6] + i ;
      int mnp = penalty[mnpind] ;
      np = mnp - op[6] ;
      for (int d=0; np < 50 && pen + np <= 2 * maxwrite && d<6; d++) {
         if (board[y+dy[d]][x+dx[d]] < 0)
            continue ;
         mnpind = opind[d] + (i << indshift[d]) ;
         mnp = penalty[mnpind] ;
         np += mnp - op[d] ;
      }
      if (np < 50 && pen + np <= 2 * maxwrite)
         recur(x+1, y, pen+np, pr, nextlev, minpen, rd) ;
      board[y][x] = 0 ;
   }
}
ull totcnt[210] ;
int main(int argc, char *argv[]) {
   int lim = 100 ;
   int printlim = -1 ;
   int clock = 0 ;
   duration() ;
   srand48(time(0)) ;
   while (argc > 2 && argv[1][0] == '-') {
      argc-- ;
      argv++ ;
      switch (argv[0][1]) {
case 'h':
         HI = atol(argv[1]) ;
         argc-- ;
         argv++ ;
         break ;
case 'M':
         maxcnt = atoll(argv[1]) ;
         argc-- ;
         argv++ ;
         break ;
case 'r':
         minx = atol(argv[1]) ;
         maxx = atol(argv[2]) ;
         argc -= 2 ;
         argv += 2 ;
         break ;
case 'm':
         LO = atol(argv[1]) ;
         argc-- ;
         argv++ ;
         break ;
case 'i':
         infile = argv[1] ;
         argc-- ;
         argv++ ;
         break ;
case 'L':
         lim = atol(argv[1]) ;
         printlim = lim ;
         argc-- ;
         argv++ ;
         break ;
case 'l':
         lim = atol(argv[1]) ;
         argc-- ;
         argv++ ;
         break ;
default:
         error("Argument not understood") ;
      }
   }
   if (HI > 6)
      error("! max hi is 6") ;
   n = atol(argv[1]) ;
   bits = 1 ;
   while ((1 << bits) < (HI - LO + 1))
      bits++ ;
   lowmask = (1 << bits) - 1 ;
   if (maxx > 2 * n - 1)
      maxx = 2 * n - 1 ;
// if ((maxx - minx + 1) * bits > 64)
//    error("! too wide?") ;
   w = 2 * n - 1 ;
   h = 2 * n - 1 ;
   nonz = 3 * n * (n - 1) + 1 ;
   opt = (3 * n - 2) * (3 * n - 3) ;
   recurpenalty(7, 0) ;
   improvepen() ;
   for (int i=0; i<64; i++) {
      board[i][0] = -1 ;
      board[i][w+1] = -1 ;
      board[0][i] = -1 ;
      board[h+1][i] = -1 ;
   }
   for (int i=1; i<n; i++)
      for (int j=1; i+j<=n; j++) {
         board[h-i+1][j] = -1 ;
         board[i][w-j+1] = -1 ;
      }
   if (infile) {
      ifstream is(infile) ;
      if (!is.is_open())
         error("Could not read input file") ;
      string lin ;
      int j = 1 ;
      while (getline(is, lin)) {
         int hasspace = 0 ;
         for (char c : lin)
            if (c == ' ')
               hasspace++ ;
         if (hasspace)
            continue ;
         for (int i=0; i<lin.size(); i++)
            if (lin[i] >= '0' && lin[i] <= '9') {
               board[j][i+1] = min(lin[i]-'0', HI) ;
            } else if (lin[i] == '.') {
               board[j][i+1] = -1 ;
            } else if (lin[i] == '?') {
               board[j][i+1] = 0 ;
            } else {
               error("! bad char in input file") ;
            }
         j++ ;
      }
   }
   for (int i=0; i<64; i++)
      for (int j=0; j<64; j++)
         templat[i][j] = board[i][j] ;
   int basepen = 0 ;
   for (int j=1; j<=h; j++)
      for (int i=1; i<=w; i++)
         basepen += penalty[getpenaltyind(i, j)] ;
   cout << "Starting with a base penalty of " << basepen << endl ;
   lev_t curlev ;
   vector<ull> nv(1) ;
   nv[0] = 1 ;
   curlev[make_pair(0, 0)] = nv ;
   for (int y=1; y<=h; y++) {
      totsize = 0 ;
      maxwrite = lim ;
      for (int i=0; i<=maxwrite; i++)
         curcnts[i] = 0 ;
      cout << "At " << y << " input level size is " << curlev.size() << endl ;
      lev_t nextlev ;
      for (auto it : curlev) {
         int minpen = 0 ;
         while (it.second[minpen] == 0)
            minpen++ ;
         if (minpen > maxwrite)
            continue ;
         if (y > 2)
            unpack(y-2, it.first.first) ;
         if (y > 1)
            unpack(y-1, it.first.second) ;
         recur(minx, y, 2*minpen, it.first.second, nextlev, minpen, it.second) ;
      }
 cout << "At end of level totsize is " << totsize << " maxwrite " << maxwrite << endl ;
      swap(curlev, nextlev) ;
      for (int i=0; i<100; i++)
         totcnt[i] = 0 ;
      if (curlev.size() == 0)
         break ;
      for (auto it : curlev)
         for (int i=0; i<it.second.size(); i++)
            totcnt[i] += it.second[i] ;
      int best = 0 ;
      while (totcnt[best] == 0)
         best++ ;
      ll cnt = 0 ;
      for (int i=0; i<100; i++)
         cnt += totcnt[i] ;
      cout << "Level size " << curlev.size() << " best " << best << " tot " << cnt << endl ;
      cout << "H" ;
      for (int i=0; i<100; i++)
         if (totcnt[i])
            cout << " " << i << ":" << totcnt[i] ;
      cout << endl ;
   }
   cout << "Done in " << duration() << endl ;
}
