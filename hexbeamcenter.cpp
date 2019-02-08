#include <iostream>
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
typedef pair<int, int> pt ;
typedef pair<int, double> sortable ;
vector<pair<sortable, pt> > sortme ;
int board[64][64] ;
int verbose = 0 ;
int HI = 6 ;
int LO = 1 ;
int n, w, h ;
int uniq = 0 ;
int bits, lowmask ;
int middleperf = -1 ;
ull shiftmask ;
vector<pair<int, int> > coords ;
vector<int> firstvals ;
int dx[] = { 1, 1, 0, -1, -1, 0 } ;
int dy[] = { 1, 0, -1, -1, 0, 1 } ;
int indshift[] = { 9, 6, 3, 18, 15, 12, 0 } ;
const int POW87 = 1LL << 21 ;
unsigned char penalty[POW87] ;
ll mcnts[1001] ;
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
int ring(int x, int y) {
   x = abs(x-n) ;
   y = abs(y-n) ;
   int xy = abs(x-y) ;
   return max(x, max(y, xy)) ;
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
const int LOOKHASH = 1<<20 ;
struct lookhash {
   ull key, val ;
} lookhash[LOOKHASH] ;
ll calls = 0 ;
int peng ;
int opt, nonz ;
int rwords, wwords ;
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
ll prevprime(ll p) {
   p |= 1 ;
   p -= 2 ;
   while (1) {
      for (ll f=3; ; f++) {
         if (f * f > p)
            return p ;
         if (p % f == 0) {
            p -= 2 ;
            break ;
         }
      }
   }
}
ll MAXMEM = 8000 ;
ll whashprime, rhashprime ;
ull *ht1, *ht2 ;
short *hv1, *hv2 ;
int canwrite = 900 ;
ll wrover ;
int wshift = 0 ;
ull packw[128] ;
int look(ull rh, int nv, int at, int penalty) {
   if (penalty > canwrite || canwrite == 0)
      return 0 ;
/*
   ull w = 0 ;
   int pat = 0 ;
   int shv = 0 ;
   for (int i=0; i<at; i++) {
      w += ((ll)board[coords[i].second][coords[i].first]-LO) << shv ;
      shv += bits ;
      if (shv + bits > 64) {
         packw[pat++] = w ;
         w = 0 ;
         shv = 0 ;
      }
   }
   if (shv > 0)
      packw[pat++] = w ;
 */
   ull *r = ht1 + rh * rwords ;
   while (canwrite > 0 && penalty <= canwrite) {
      ll h = wrover ;
      for (ll k=0; k<whashprime; k++) {
         if (hv2[h] == 0 || hv2[h] > canwrite + 1) {
            mcnts[hv2[h]]-- ;
            mcnts[penalty+1]++ ;
            hv2[h] = penalty + 1 ;
            for (int i=0; i<rwords; i++)
               ht2[h*wwords+i] = r[i] ;
            if (rwords != wwords)
               ht2[h*wwords+wwords-1] = nv-LO ;
            else
               ht2[h*wwords+wwords-1] += ((ull)(nv - LO)) << wshift ;
/*
 for (int i=0; i<pat; i++) if (packw[i] != ht2[h*wwords+i]) {
    cerr << "At " << i << " packw[i] " << hex << packw[i] << " ht2 " << ht2[h*wwords+i] << endl ;
    error("! packing error") ;
 }
 */
            wrover = h + 1 ;
            if (wrover == whashprime)
               wrover = 0 ;
            return 1 ;
         }
         h++ ;
         if (h == whashprime)
            h = 0 ;
      }
      while (canwrite > 0 && mcnts[canwrite+2] == 0)
         canwrite-- ;
      cout << "Lowering canwrite to " << canwrite << endl ;
   }
   return 0 ;
}
struct unpackdat {
   int off, shift, x, y ;
} unpackdat[18] ;
int nunpack ;
ull cvroot = 0 ;
void setupunpack(int at) {
   cvroot++ ;
   nunpack = 0 ;
   int shv = 0 ;
   int y = coords[at].second ;
   int x = coords[at].first ;
   int off = 0 ;
   for (int i=0; i<at; i++) {
      if (shv + bits > 64) {
         shv = 0 ;
         off++ ;
      }
      int yy = coords[i].second ;
      int xx = coords[i].first ;
      if (abs(x-xx) <= 2 && abs(y-yy) <= 2 &&
          abs((x-y)-(xx-yy)) <= 2) {
         unpackdat[nunpack].off = off ;
         unpackdat[nunpack].shift = shv ;
         unpackdat[nunpack].x = xx ;
         unpackdat[nunpack].y = yy ;
         nunpack++ ;
      }
      shv += bits ;
   }
}
ull fastunpack(int at, ll h) {
   ull *wp = ht1+h*rwords ;
   ull cv = 0 ;
   for (int i=0; i<nunpack; i++) {
      int v = LO + ((wp[unpackdat[i].off] >> unpackdat[i].shift) & lowmask) ;
      board[unpackdat[i].y][unpackdat[i].x] = v ;
      cv = cv * 37 + v;
   }
   return cv ;
}
void unpack(int at, ll h) {
   ll wp = h*rwords ;
   ull w = ht1[wp++] ;
   int shv = 0 ;
   for (int i=0; i<at; i++) {
      if (shv + bits > 64) {
         w = ht1[wp++] ;
         shv = 0 ;
      }
      board[coords[i].second][coords[i].first] = (LO + ((w >> shv) & lowmask)) ;
      shv += bits ;
   }
}
void setupw(int nz) {
   int valsper = 64 / bits ;
   wwords = (nz + valsper - 1) / valsper ;
   if (wwords == 0)
      wwords = 1 ;
   whashprime =
    prevprime(MAXMEM * 1000000LL / (2 * (sizeof(ll) * wwords + sizeof(short)))) ;
   cout << "Whashprime is " << whashprime << endl ;
   hv2 = (short *)(ht2 + wwords * whashprime) ;
   wrover = (ll)(whashprime*drand48()) ;
}
const char *infile ;
int seed ;
int main(int argc, char *argv[]) {
   int lim = 210 ;
   int printlim = -1 ;
   int clock = 0 ;
   ll printed = 0 ;
   duration() ;
   while (argc > 2 && argv[1][0] == '-') {
      argc-- ;
      argv++ ;
      switch (argv[0][1]) {
case 'v':
         verbose++ ;
         break ;
case 'c':
         clock = 1 ;
         break ;
case 'u':
         uniq++ ;
         break ;
case 'M':
         MAXMEM = atol(argv[1]) ;
         argc-- ;
         argv++ ;
         break ;
case 'r':
         middleperf = atol(argv[1]) ;
         argc-- ;
         argv++ ;
         break ;
case 'h':
         HI = atol(argv[1]) ;
         argc-- ;
         argv++ ;
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
case 'S':
         seed = atol(argv[1]) ;
         argc-- ;
         argv++ ;
         break ;
default:
         error("Argument not understood") ;
      }
   }
   if (seed == 0)
      srand48(time(0)) ;
   else
      srand48(seed) ;
   if (HI > 6)
      error("! max hi is 6") ;
   n = atol(argv[1]) ;
   bits = 1 ;
   while ((1 << bits) < (HI - LO + 1))
      bits++ ;
   lowmask = (1 << bits) - 1 ;
   if (bits == 1) {
      shiftmask = 0xfffffffffffffffeLL ;
   } else if (bits == 2) {
      shiftmask = 0xfffffffffffffffcLL ;
   } else if (bits == 3) {
      shiftmask = 0777777777777777777770LL ;
   } else {
      error("! bad high") ;
   }
   for (int i=2; i<argc; i++)
      firstvals.push_back(atol(argv[i])) ;
   w = 2 * n - 1 ;
   h = 2 * n - 1 ;
   nonz = 3 * n * (n - 1) + 1 ;
   opt = (3 * n - 2) * (3 * n - 3) ;
   ht1 = (ull*)calloc(MAXMEM*500000LL, 1) ;
   ht2 = (ull*)calloc(MAXMEM*500000LL, 1) ;
   setupw(0) ;
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
            }
         j++ ;
      }
   }
   if (clock) {
      if (middleperf < 0)
         middleperf = 4 ;
      double rr = 20 * drand48() ;
      for (int i=1; i<=w; i++)
         for (int j=1; j<=h; j++) {
            if (board[j][i] == 0) {
               int k = abs(i-j) ;
               int r = max(k, max(abs(i-n), abs(j-n))) ;
               double ang = fmod(rr + atan2(i-n, j-n), 2*3.14159265358979) ;
               if (r < n - middleperf) {
                  // nothing
               } else {
                  r = 9999 ;
               }
               sortme.push_back(make_pair(make_pair(r, ang),
                                          make_pair(i, j))) ;
            }
         }
   } else {
      double xm = drand48() - 0.5 ;
      double ym = drand48() - 0.5 ;
      for (int i=1; i<=w; i++)
         for (int j=1; j<=h; j++) {
            if (board[j][i] == 0) {
               int r = 0 ;
               double ang = xm * i + ym * j ;
               sortme.push_back(make_pair(make_pair(r, ang),
                                          make_pair(i, j))) ;
            }
         }
   }
   sort(sortme.begin(), sortme.end()) ;
   for (int i=0; i<sortme.size(); i++)
      coords.push_back(sortme[i].second) ;
   int totpen = 0 ;
   for (int y=1; y<=h; y++)
      for (int x=1; x<=w; x++)
         totpen += penalty[getpenaltyind(y, x)] ;
   look(0, LO, 0, totpen) ;
   int bestw = 0 ;
   int bestcnt = 0 ;
   canwrite = lim ;
   for (int at=0; at<coords.size(); at++) {
      bestw = 9999 ;
      swap(hv1, hv2) ;
      swap(ht1, ht2) ;
      rhashprime = whashprime ;
      rwords = wwords ;
      setupw(at+1) ;
      setupunpack(at) ;
      for (int y=1; y<=h; y++)
         for (int x=1; x<=w; x++)
            if (board[y][x] != -1)
               board[y][x] = 0 ;
      cout << "H " << (-mcnts[0]) ;
      mcnts[0] = 0 ;
      for (int i=1; i<1001; i++)
         if (mcnts[i]) {
            cout << " " << i << ":" << mcnts[i] ;
            mcnts[i] = 0 ;
         }
      cout << endl ;
      memset(hv2, 0, whashprime*sizeof(short)) ;
      ll h = (ll)(rhashprime*drand48()) ;
      canwrite = lim ;
      int x = coords[at].first ;
      int y = coords[at].second ;
      for (ll hh=0; hh<rhashprime; h++, hh++) {
         if (h >= rhashprime)
            h = 0 ;
         if (hv1[h] == 0)
            continue ;
         if (hv1[h] > canwrite + 1)
            continue ;
         int oldpenalty = hv1[h] - 1 ;
         ull key = fastunpack(at, h) ;
         ull kh = (key + cvroot) & (LOOKHASH - 1) ;
         ull val ;
         if (at+1 <= 7 || lookhash[kh].key != key) {
            val = 0 ;
            if (at+1 <= 7)
               unpack(at, h) ;
//       cout << "Penalty is " << (hv1[h]-1) << endl ;
//       showboard() ;
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
            for (int i=HI; i>=LO; i--) {
               int np = 0 ;
               board[y][x] = i ;
               int mnpind = opind[6] + i ;
               int mnp = penalty[mnpind] ;
               np = mnp - op[6] ;
               for (int d=0; np < 50 && d<6; d++) {
                  if (board[y+dy[d]][x+dx[d]] < 0)
                     continue ;
                  mnpind = opind[d] + (i << indshift[d]) ;
                  mnp = penalty[mnpind] ;
                  np += mnp - op[d] ;
               }
               if (np > 255)
                  np = 255 ;
               val += ((ull)np) << (8 * i) ;
            }
            lookhash[kh].key = key ;
            lookhash[kh].val = val ;
         } else {
            val = lookhash[kh].val ;
         }
         for (int i=HI; i>=LO; i--) {
            int top = canwrite + 1 ;
            board[y][x] = i ;
            int good = 1 ;
            if (at+1 == 7) {
               for (int st=1; good && st<7; st++) {
                  for (int dir=-1; good && dir<=1; dir += 2) {
                     for (int ii=0; good && ii<6; ii++) {
                        int i1 = ii + 1 ;
                        int i2 = (st + dir * ii + 60) % 6 + 1 ;
                        int v1 =
                      board[sortme[i1].second.second][sortme[i1].second.first] ;
                        int v2 =
                      board[sortme[i2].second.second][sortme[i2].second.first] ;
                        if (v1 == 0 || v2 == 0)
                           error("! center not filled") ;
                        if (v2 > v1)
                           break ;
                        if (v1 > v2) {
                           good = 0 ;
                           break ;
                        }
                     }
                  }
               }
            }
            int np = 255 & (val >> (8 * i)) ;
            if (good && np < 50 && oldpenalty + np < top) {
               look(h, i, at+1, oldpenalty + np) ;
               if (oldpenalty + np < bestw ||
                  (oldpenalty + np == bestw && at+1 == coords.size()) ||
                  (oldpenalty + np <= printlim && at+1 == coords.size())) {
                  if (oldpenalty + np < bestw) {
                     bestcnt = 0 ;
                     bestw = oldpenalty + np ;
                  }
                  bestcnt++ ;
                  cout << "New best penalty " << (oldpenalty + np) << " at " << at << " out of " << nonz << endl ;
                  if (verbose || at+1 == coords.size()) {
                     unpack(at, h) ;
                     showboard() ;
                     printed++ ;
                     if (printed % 1000000 == 0)
                        printlim-- ;
                  }
                  cout << flush ;
               }
            } else {
            }
         }
         board[y][x] = 0 ;
      }
      cout << "Best penalty at " << at << " is " << bestw << endl ;
      wshift += bits ;
      if (wshift + bits > 64)
         wshift = 0 ;
   }
   cout << "H " << (-mcnts[0]) ;
   for (int i=1; i<1001; i++)
      if (mcnts[i])
         cout << " " << i << ":" << mcnts[i] ;
   cout << endl ;
   cout << "Done; hi val is " << ((3*n-3)*(3*n-2)-bestw/2) << " pen " << bestw << " cnt " << bestcnt << " in " << duration() << endl ;
}
