#include <iostream>
#include <sys/time.h>
#include <map>
#include <set>
#include <cstdlib>
#include <vector>
#include <string>
#include <fstream>
#include <algorithm>
using namespace std ;
typedef unsigned long long ull ;
typedef long long ll ;
int n, hi, w, h ;
ll maxsols = 1000000000000000000LL ;
const char *fn ;
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
int board[64][64] ;
int dx[] = { 1, 1, 0, -1, -1, 0 } ;
int dy[] = { 1, 0, -1, -1, 0, 1 } ;
int remap[12][4] = {
   {1, 0, 0, 1},
   {1, -1, 1, 0},
   {0, -1, 1, -1},
   {-1, 0, 0, -1},
   {-1, 1, -1, 0},
   {0, 1, -1, 1},
   {0, 1, 1, 0},
   {-1, 1, 0, 1},
   {-1, 0, -1, 1},
   {0, -1, -1, 0},
   {1, -1, 0, -1},
   {1, 0, 1, -1},
} ;
int getval(int x, int y, int m) {
   int x2 = remap[m][0] * (x - n) + remap[m][1] * (y - n) + n ;
   int y2 = remap[m][2] * (x - n) + remap[m][3] * (y - n) + n ;
   if (x2 < 1 || y2 < 1 || x2 > w || y2 > h || board[y2][x2] < 0) {
      return -1 ;
   } else {
      return board[y2][x2] ;
   }
}
int lowm() {
   int mask = (1 << 12) - 1 ;
   int r = -1 ;
   for (int y=1; y<=h; y++)
      for (int x=1; x<=w; x++) {
         int lowv = 256 ;
         int newm = 0 ;
         for (int m=0; m<12; m++) {
            if (((mask >> m) & 1) == 0)
               continue ;
            int v = getval(x, y, m) ;
            if (v < lowv) {
               newm = 1 << m ;
               r = m ;
               lowv = v ;
            } else if (v == lowv) {
               newm |= 1 << m ;
            }
         }
         if ((newm & (newm - 1)) == 0)
            return newm ;
         mask = newm ;
      }
   return mask ;
}
int calcpen(const vector<string> trip) {
   int w = trip[1].size() ;
   for (int j=0; j<3; j++)
      for (int i=0; i<w+2; i++)
         board[j][i] = -1 ;
   for (int j=0; j<3; j++) {
      if (trip[j].size() != 0) {
         int off = 1 ;
         if (j == 0) {
            if (trip[0].size() != w - 1)
               error("! bad row 1 size") ;
         } else if (j == 2) {
            if (trip[2].size() == w + 1) {
            } else if (trip[2].size() == w - 1) {
               off = 2 ;
            } else {
               error("! bad row 2 size") ;
            }
         }
         for (int i=0; i<trip[j].size(); i++)
            board[j][i+off] = trip[j][i] - '0' ;
      }
   }
   int r = 0 ;
   for (int i=1; i<=w; i++) {
      int c = board[1][i] ;
      int cnts[8] ;
      for (int i=0; i<8; i++)
         cnts[i] = 0 ;
      for (int d=0; d<6; d++) {
         int v = board[1+dy[d]][i+dx[d]] ;
         if (v > 0)
            cnts[v]++ ;
         if (v == board[1][i] && v != hi)
            r++ ;
      }
      int v = c ;
      for (int k=1; k<v; k++) {
         if (cnts[k] == 0) {
            cerr << "Missing support; skipping in (" << trip[0] << ") (" << trip[1] << ") (" << trip[2] << ")" << endl ;
            return -1 ;
         }
         else if (cnts[k] > 1)
            r += 2 * (cnts[k] - 1) ;
      }
   }
   return r ;
}
int rowcount = 0 ;
map<string, int> rowlookup ;
vector<string> rowlist ;
int findrow(string s) {
   auto it = rowlookup.find(s) ;
   if (it != rowlookup.end())
      return it->second ;
   rowlist.push_back(s) ;
   rowlookup[s] = rowcount ;
   return rowcount++ ;
}
int entries ;
int nodecount = 0 ;
map<pair<int, int>, int> nodelookup ;
vector<pair<int, int> > nodelist ;
vector<vector<int> > edges ;
vector<vector<int> > backedges ;
vector<vector<int> > pens ;
vector<vector<int> > backpens ;
vector<int> emptyv ;
typedef map<int, vector<ull> > lev_t ;
vector<lev_t> storedp ;
map<pair<int, int>, int> seenedges ;
int findnode(int a, int b) {
   pair<int, int> k = make_pair(a, b) ;
   auto it = nodelookup.find(k) ;
   if (it != nodelookup.end())
      return it->second ;
   nodelist.push_back(k) ;
   nodelookup[k] = nodecount ;
   edges.push_back(emptyv) ;
   backedges.push_back(emptyv) ;
   pens.push_back(emptyv) ;
   backpens.push_back(emptyv) ;
   return nodecount++ ;
}
void addedge(int n1, int n2, int pen) {
   edges[n1].push_back(n2) ;
   backedges[n2].push_back(n1) ;
   pens[n1].push_back(pen) ;
   backpens[n2].push_back(pen) ;
}
int edgecount ;
void stats(int j, const lev_t &v) {
   vector<ull> finalcnts ;
   for (auto it=v.begin(); it != v.end(); it++) {
      int n1 = it->first ;
      const vector<ull> &pv = it->second ;
      if (finalcnts.size() < pv.size())
         finalcnts.resize(pv.size()) ;
      for (int i=0; i<pv.size(); i++)
         finalcnts[i] += pv[i] ;
   }
   cout << "H " << j ;
   for (int i=0; i<finalcnts.size(); i++)
      if (finalcnts[i])
         cout << " " << i << ":" << finalcnts[i] ;
   cout << endl << flush ;
}
int maxerror = 87 ;
int checksym = 0 ;
vector<int> solnodes ;
int randomizeit = 0 ;
int recur(int loc, int remerror, int toterr, int n2) {
   if (loc < 0) {
      if (checksym) {
         for (int j=0; j<=h; j++)
            for (int i=0; i<=w; i++)
               board[j][i] = -1 ;
         for (int i=0; i+1<solnodes.size(); i++) {
            const string &s = rowlist[nodelist[solnodes[i]].first] ;
            int off = max(0, i+1-n) ;
            for (int j=0; j<s.size(); j++)
               board[i+1][j+off+1] = s[j] - '0' ;
         }
         int sym = lowm() ;
         if ((sym & 1) == 0) {
            return 1 ;
         }
      }
      cout << "Solution with " << (0.5*toterr) << endl ;
      for (int i=0; i+1<solnodes.size(); i++) {
         int off = max(0, i+1-n) ;
         for (int j=n; j<=i; j++)
            cout << "." ;
         cout << rowlist[nodelist[solnodes[i]].first] ;
         for (int j=0; j<n-1-i; j++)
            cout << "." ;
         cout << endl ;
      }
      if (--maxsols <= 0)
         exit(0) ;
      return 1 ;
   }
   lev_t &lev = storedp[loc] ;
   auto it = lev.find(n2) ;
   if (it == lev.end()) {
      return 0 ;
   }
   const vector<ull> &pv = it->second ;
   int ok = 0 ;
   for (int i=0; i <= remerror && i<pv.size(); i++)
      if (pv[i]) {
         ok = 1 ;
         break ;
      }
   if (!ok)
      return 0 ;
   int base = 0 ;
   if (randomizeit)
      base = (int)(backedges[n2].size()*drand48()) ;
   for (int jj=0; jj<backedges[n2].size(); jj++) {
      int j = (base + jj) % backedges[n2].size() ;
      int n1 = backedges[n2][j] ;
      int thispen = seenedges[make_pair(n1, n2)] ;
      int npen = remerror - thispen ;
      if (npen < 0)
         continue ;
      solnodes.push_back(n1) ;
      int t = recur(loc-1, npen, toterr + thispen, n1) ;
      solnodes.pop_back() ;
      if (randomizeit && t)
         return 1 ;
   }
   return 0 ;
}
int sols ;
char mline[10000] ;
int mgetline(FILE *f, string &s) {
   if (fgets(mline, sizeof(mline)-1, f) == 0)
      return 0 ;
   s.clear() ;
   for (int i=0; mline[i] >= ' '; i++)
      s.push_back(mline[i]) ;
   return 1 ;
}
int centerval = -1 ;
int main(int argc, char *argv[]) {
   srand48(time(0)) ;
   while (argc > 2 && argv[1][0] == '-') {
      argc-- ;
      argv++ ;
      switch (argv[0][1]) {
case 'r':
         randomizeit++ ;
         break ;
case 'c':
         checksym++ ;
         break ;
case 'v':
         centerval = atol(argv[1]) ;
         argc-- ;
         argv++ ;
         break ;
case 'l':
         maxerror = atol(argv[1]) ;
         argc-- ;
         argv++ ;
         break ;
case 'm':
         maxsols = atoll(argv[1]) ;
         argc-- ;
         argv++ ;
         break ;
case 's':
         sols++ ;
         break ;
default:
         error("! did not understand argument") ;
      }
   }
   if (argc < 3)
      error("! not enough arguments") ;
   n = atol(argv[1]) ;
   w = h = 2 * n - 1 ;
   fn = argv[2] ;
   FILE *f = fopen(fn, "r") ;
   string lin ;
   findrow("") ;
   vector<int> allpen ;
   int skipped = 0 ;
   vector<string> triple(3) ;
   while (mgetline(f, lin)) {
      entries++ ;
      int ptr = 0 ;
      for (int i=0; i<3; i++)
         triple[i].clear() ;
      for (int i=0; i<lin.size(); i++)
         if (lin[i] == '/')
            ptr++ ;
         else {
            if (lin[i] > hi + '0')
               hi = lin[i] - '0' ;
            triple[ptr].push_back(lin[i]) ;
         }
      if (triple[0].size() == 0) {
         if (triple[1].size() != n) {
            skipped++ ;
            continue ;
         }
      } else if (triple[0].size() == triple[2].size()) {
         if (triple[1].size() != 2*n-1) {
            skipped++ ;
            continue ;
         }
      } else {
         if (triple[0].size() < n || triple[2].size() >= 2 * n) {
            skipped++ ;
            continue ;
         }
      }
      int pen = calcpen(triple) ;
      if (pen < 0)
         continue ;
      if (allpen.size() <= pen)
         allpen.resize(pen+1) ;
      allpen[pen]++ ;
      vector<vector<int> > seen ;
      for (int rev=0; rev<2; rev++) {
         vector<int> rn ;
         for (int i=0; i<3; i++)
            rn.push_back(findrow(triple[i])) ;
         for (int rev2=0; rev2<2; rev2++) {
            int n1 = findnode(rn[0], rn[1]) ;
            int n2 = findnode(rn[1], rn[2]) ;
            int ok = 1 ;
            for (int k=0; k<seen.size(); k++)
               if (seen[k] == rn)
                  ok = 0 ;
            if (ok) {
               auto it = seenedges.find(make_pair(n1, n2)) ;
               if (it == seenedges.end()) {
                  seenedges[make_pair(n1, n2)] = pen ;
                  addedge(n1, n2, pen) ;
                  edgecount++ ;
                  seen.push_back(rn) ;
               }
            }
            reverse(triple.begin(), triple.end()) ;
            reverse(rn.begin(), rn.end()) ;
         }
         if (rev)
            break ;
         for (int i=0; i<3; i++)
            reverse(triple[i].begin(), triple[i].end()) ;
      }
   }
   cout << "Entries " << entries << " skipped " << skipped << " rows " << rowcount << " nodes " << nodecount << " edges " << edgecount << endl ;
   cout << "Penalties:" ;
   for (int i=0; i<allpen.size(); i++)
      if (allpen[i])
         cout << " " << i << ":" << allpen[i] ;
   cout << endl ;
   lev_t curlev ;
   vector<ull> emptyull ;
   for (int i=0; i<nodecount; i++) {
      if (nodelist[i].first == 0 && rowlist[nodelist[i].second].size() == n) {
         for (int j=0; j<edges[i].size(); j++) {
            int n2 = edges[i][j] ;
            int pen = pens[i][j] ;
            auto it = curlev.find(n2) ;
            if (it == curlev.end()) {
               curlev[n2] = emptyull ;
               it = curlev.find(n2) ;
            }
            if (it->second.size() <= pen)
               it->second.resize(pen+1) ;
            it->second[pen]++ ;
         }
      }
   }
   cout << "Start level size is " << curlev.size() << endl ;
   stats(2, curlev) ;
// 345430
// 123456
   for (int j=3; j<=2*n; j++) {
      int reqlen = min(n + j - 1, 3*n-j-1) ;
      if (j == 2 * n)
         reqlen = 0 ;
      cout << "At " << j << " required length is " << reqlen << endl ;
      lev_t nextlev ;
      for (auto it=curlev.begin(); it != curlev.end(); it++) {
         int n1 = it->first ;
         const vector<ull> &pv = it->second ;
         int hipen = pv.size()-1 ;
         int minpen = 0 ;
         while (minpen < pv.size() && pv[minpen] == 0)
            minpen++ ;
         for (int j=0; j<edges[n1].size(); j++) {
            int n2 = edges[n1][j] ;
            if (rowlist[nodelist[n2].second].size() != reqlen)
               continue ;
            if (reqlen == 2 * n - 1 && centerval >= 0 && 
                (rowlist[nodelist[n2].second][n] == '1') != (centerval == 1))
               continue ;
            int pen = pens[n1][j] ;
            auto it = nextlev.find(n2) ;
            if (it == nextlev.end()) {
               nextlev[n2] = emptyull ;
               it = nextlev.find(n2) ;
            }
            int hisize = hipen + pen ;
            if (hisize > 2 * maxerror)
               hisize = 2 * maxerror ;
            if (it->second.size() <= hisize)
               it->second.resize(hisize+1) ;
            for (int k=minpen; k<=hipen; k++) {
               if (k + pen > hisize)
                  break ;
               it->second[k+pen] += pv[k] ;
            }
         }
      }
      cout << "At level " << j << " size is " << nextlev.size() << endl ;
      stats(j, nextlev) ;
      if (nextlev.size() == 0)
         break ;
      swap(curlev, nextlev) ;
      storedp.resize(storedp.size()+1) ;
      swap(nextlev, storedp[storedp.size()-1]) ;
   }
   if (sols) {
      storedp.resize(storedp.size()+1) ;
      swap(curlev, storedp[storedp.size()-1]) ;
      lev_t &lastlev = storedp[storedp.size()-1] ;
      vector<int> todo ;
      for (auto it=lastlev.begin(); it!=lastlev.end(); it++) {
         const vector<ull> &pv = it->second ;
         int ok = 0 ;
         for (int i=0; i <= 2*maxerror && i<pv.size(); i++)
            if (pv[i]) {
               ok = 1 ;
               break ;
            }
         if (ok)
            todo.push_back(it->first) ;
      }
      int base = 0 ;
      while (1) {
         if (randomizeit)
            base = (int)(todo.size()*drand48()) ;
         for (int jj=0; jj<todo.size(); jj++) {
            int j = (base + jj) % todo.size() ;
            solnodes.push_back(todo[j]) ;
            int t = recur(storedp.size()-1, 2*maxerror, 0, todo[j]) ;
            solnodes.pop_back() ;
            if (t)
               break ;
         }
         if (!randomizeit)
            break ;
      }
   }
}
