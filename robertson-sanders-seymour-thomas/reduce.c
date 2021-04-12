/* reduce.c */
/************/

/* This is part I of two programs that serve as supplements to the paper `The
 * Four-Colour Theorem' by N. Robertson, D. P. Sanders, P. D. Seymour and R.
 * Thomas. Please refer to the manuscript `Reducibility in the Four-Color
 * Theorem' by the same authors for a description of this program */

/* Copyright 1995 by N. Robertson, D.P. Sanders, P.D. Seymour and R. Thomas  */
/* Permission to use for the purpose of scholarly research is hereby granted */

/* Version 1,  8 May 1995 */

#define VERTS   27	/* max number of vertices in a free completion + 1 */
#define DEG     13	/* max degree of a vertex in a free completion + 1 */
			/* must be at least 13 because of row 0            */
#define EDGES   62	/* max number of edges in a free completion + 1    */
#define MAXRING 14	/* max ring-size */
#include <stdio.h>
#include <stdlib.h>

typedef long tp_confmat[VERTS][DEG];
typedef long tp_angle[EDGES][5];
typedef long tp_edgeno[EDGES][EDGES];

/* function prototypes */
#ifdef PROTOTYPE_MAX
void testmatch(long, char *, long[], char *, long);
void augment(long, long[], long, long **, long[16][16][4], char *, char *, long *, long, long, long, char *, long *, long);
void checkreality(long, long **, char *, char *, long *, long, long, long, char *, long *, long);
long stillreal(long, long[], long, char *, long);
long updatelive(char *, long, long *);
void strip(tp_confmat, tp_edgeno);
long ininterval(long[], long[]);
void findangles(tp_confmat, tp_angle, tp_angle, tp_angle, long[]);
long findlive(char *, long, tp_angle, long[], long);
void checkcontract(char *, long, tp_angle, tp_angle, long[], long[]);
void printstatus(long, long, long, long);
void record(long[], long[], long, long[][5], char *, long *, long);
long inlive(long[], long[], long, char *, long);
long ReadConf(tp_confmat, FILE *, long *);
void ReadErr(int, char[]);
#else
void testmatch();
void augment();
void checkreality();
long stillreal();
long updatelive();
void strip();
long ininterval();
void findangles();
long findlive();
void checkcontract();
void printstatus();
void record();
long inlive();
long ReadConf();
void ReadErr();
#endif


main(argc, argv)
int argc;
char *argv[];
{
   long ring, nlive, ncodes, i, nchar, count, power[17], contract[EDGES + 1];
   tp_angle angle, diffangle, sameangle;
   tp_confmat graph;
   char *live, *real, *s;
   FILE *fp;
   static long simatchnumber[] = {0L, 0L, 1L, 3L, 10L, 30L, 95L, 301L, 980L, 3228L, 10797L, 36487L, 124542L, 428506L, 1485003L};

   if (argc < 2)
      s = "unavoidable.conf";
   else
      s = argv[1];
   fp = fopen(s, "r");
   if (fp == NULL) {
      (void) printf("Can't open %s\n", s);
      exit(1);
   }
   power[1] = 1;
   for (i = 2; i < 17; i++)
      power[i] = 3 * power[i - 1];	/* power[i] = 3^(i-1) for i>0 */
   ncodes = (power[MAXRING] + 1) / 2;	/* max number of codes */
   live = (char *) malloc(ncodes * sizeof(char));
   nchar = simatchnumber[MAXRING] / 8 + 2;
   real = (char *) malloc(nchar * sizeof(char));
   if (live == NULL || real == NULL) {
      i = (ncodes + nchar) * sizeof(char);
      (void) printf("Not enough memory. %ld Kbytes needed.\n", i / 1024 + 1);
      exit(44);
   }
   for (count = 0; !ReadConf(graph, fp, NULL); count++) {
      findangles(graph, angle, diffangle, sameangle, contract);
      /* "findangles" fills in the arrays "angle","diffangle","sameangle" and
       * "contract" from the input "graph". "angle" will be used to compute
       * which colourings of the ring edges extend to the configuration; the
       * others will not be used unless a contract is specified, and if so
       * they will be used in "checkcontract" below to verify that the
       * contract is correct. */
      ring = graph[0][1];	/* ring-size */
      if (ring > MAXRING) {
	 (void) printf("Ring-size bigger than %d\n", MAXRING);
	 exit(43);
      }
      ncodes = (power[ring] + 1) / 2;	/* number of codes of colorings of R */
      for (i = 0; i < ncodes; i++)
	 live[i] = 1;
      nlive = findlive(live, ncodes, angle, power, graph[0][2]);
      /* "findlive" computes {\cal C}_0 and stores in live */
      nchar = simatchnumber[ring] / 8 + 1;
      for (i = 0; i <= nchar; i++)
	 real[i] = (char) 255;
      /* "real" will be an array of characters, and each bit of each
       * character will correspond to a balanced signed matching. At this
       * stage all the bits are set = 1. */
      do
	 testmatch(ring, real, power, live, nchar);
      /* computes {\cal M}_{i+1} from {\cal M}_i, updates the bits of "real" */
      while (updatelive(live, ncodes, &nlive));
      /* computes {\cal C}_{i+1} from {\cal C}_i, updates "live" */
      checkcontract(live, nlive, diffangle, sameangle, contract, power);
      /* This verifies that the set claimed to be a contract for the
       * configuration really is. */
   }
   (void) fclose(fp);
   free(live);
   free(real);
   (void) printf("Reducibility of %ld configurations verified\n", count);
   return (0);
}


void
testmatch(ring, real, power, live, nchar)
long ring, power[], nchar;
char *live, *real;

/* This generates all balanced signed matchings, and for each one, tests
 * whether all associated colourings belong to "live". It writes the answers
 * in the bits of the characters of "real". */
{
   long a, b, n, interval[10], *weight[8], nreal;
   long matchweight[16][16][4], *mw, realterm;
   char bit;

   nreal = 0;
   /* "nreal" will be the number of balanced signed matchings such that all
    * associated colourings belong to "live"; ie the total number of nonzero
    * bits in the entries of "real" */
   bit = 1;
   realterm = 0;
   /* First, it generates the matchings not incident with the last ring edge */

   for (a = 2; a <= ring; a++)
      for (b = 1; b < a; b++) {
	 mw = matchweight[a][b];
	 mw[0] = 2 * (power[a] + power[b]);
	 mw[1] = 2 * (power[a] - power[b]);
	 mw[2] = power[a] + power[b];
	 mw[3] = power[a] - power[b];
      }
   for (a = 2; a < ring; a++)
      for (b = 1; b < a; b++) {
	 n = 0;
	 weight[1] = matchweight[a][b];
	 if (b >= 3) {
	    n = 1;
	    interval[1] = 1;
	    interval[2] = b - 1;
	 }
	 if (a >= b + 3) {
	    n++;
	    interval[2 * n - 1] = b + 1;
	    interval[2 * n] = a - 1;
	 }
	 augment(n, interval, (long) 1, weight, matchweight, live, real, &nreal, ring, (long) 0, (long) 0, &bit, &realterm, nchar);
      }

   /* now, the matchings using an edge incident with "ring" */
   for (a = 2; a <= ring; a++)
      for (b = 1; b < a; b++) {
	 mw = matchweight[a][b];
	 mw[0] = power[a] + power[b];
	 mw[1] = power[a] - power[b];
	 mw[2] = -power[a] - power[b];
	 mw[3] = -power[a] - 2 * power[b];

      }
   for (b = 1; b < ring; b++) {
      n = 0;
      weight[1] = matchweight[ring][b];
      if (b >= 3) {
	 n = 1;
	 interval[1] = 1;
	 interval[2] = b - 1;
      }
      if (ring >= b + 3) {
	 n++;
	 interval[2 * n - 1] = b + 1;
	 interval[2 * n] = ring - 1;
      }
      augment(n, interval, (long) 1, weight, matchweight, live, real, &nreal, ring, (power[ring + 1] - 1) / 2, (long) 1, &bit, &realterm, nchar);
   }
   (void) printf("               %ld\n", nreal);
   (void) fflush(stdout);
}

void
augment(n, interval, depth, weight, matchweight, live, real, pnreal, ring, basecol, on, pbit, prealterm, nchar)
long n, interval[10], depth, *weight[8], matchweight[16][16][4], *pnreal, ring,
 basecol, on, *prealterm, nchar;
char *live, *real, *pbit;

/* Finds all matchings such that every match is from one of the given
 * intervals. (The intervals should be disjoint, and ordered with smallest
 * first, and lower end given first.) For each such matching it examines all
 * signings of it, and adjusts the corresponding entries in "real" and
 * "live". */
{
   long h, i, j, r, newinterval[10], newn, lower, upper;

   checkreality(depth, weight, live, real, pnreal, ring, basecol, on, pbit, prealterm, nchar);
   depth++;
   for (r = 1; r <= n; r++) {
      lower = interval[2 * r - 1];
      upper = interval[2 * r];
      for (i = lower + 1; i <= upper; i++)
	 for (j = lower; j < i; j++) {
	    weight[depth] = matchweight[i][j];
	    for (h = 1; h < 2 * r - 1; h++)
	       newinterval[h] = interval[h];
	    newn = r - 1;
	    if (j > lower + 1) {
	       newn++;
	       newinterval[h++] = lower;
	       newinterval[h++] = j - 1;
	    }
	    if (i > j + 1) {
	       newn++;
	       newinterval[h++] = j + 1;
	       newinterval[h++] = i - 1;
	    }
	    augment(newn, newinterval, depth, weight, matchweight, live,
		    real, pnreal, ring, basecol, on, pbit, prealterm, nchar);
	 }
   }
}


void
checkreality(depth, weight, live, real, pnreal, ring, basecol, on, pbit, prealterm, nchar)
long depth, *weight[8], *pnreal, ring, basecol, on, *prealterm, nchar;
char *live, *real, *pbit;

/* For a given matching M, it runs through all signings, and checks which of
 * them have the property that all associated colourings belong to "live". It
 * writes the answers into bits of "real", starting at the point specified by
 * "bit" and "realterm". "basecol" is for convenience in computing the
 * associated colourings; it is zero for matchings not incident with "ring".
 * "on" is nonzero iff the matching is incident with "ring". */
{
   long i, k, nbits, choice[8], col, parity;
   unsigned long left;

   nbits = 1 << (depth - 1);
   /* k will run through all subsets of M minus the first match */
   for (k = 0; k < nbits; k++, *pbit <<= 1) {
      if (!*pbit) {
	 *pbit = 1;
	 ++(*prealterm);
	 if (*prealterm > nchar) {
	    (void) printf("More than %ld entries in real are needed\n", nchar + 1);
	    exit(32);
	 }
      }
      if (!(*pbit & real[*prealterm]))
	 continue;
      col = basecol;
      parity = ring & 1;
      for (i = 1, left = k; i < depth; i++, left >>= 1) {
	 if (left & 1) {	/* i.e. if a_i=1, where k=a_1+2a_2+4a_3+... */
	    parity ^= 1;
	    choice[i] = weight[i][1];
	    col += weight[i][3];
	 } else {
	    choice[i] = weight[i][0];
	    col += weight[i][2];
	 }
      }
      if (parity) {
	 choice[depth] = weight[depth][1];
	 col += weight[depth][3];
      } else {
	 choice[depth] = weight[depth][0];
	 col += weight[depth][2];
      }
      if (!stillreal(col, choice, depth, live, on)) {
	 real[*prealterm] ^= *pbit;
      } else
	 (*pnreal)++;
   }
}


long
stillreal(col, choice, depth, live, on)
long col, choice[8], depth, on;
char *live;

/* Given a signed matching, this checks if all associated colourings are in
 * "live", and, if so, records that fact on the bits of the corresponding
 * entries of "live". */
{
   long sum[64], mark, i, j, twopower, b, c;
   long twisted[64], ntwisted, untwisted[64], nuntwisted;

   ntwisted = nuntwisted = 0;
   if (col < 0) {
      if (!live[-col])
	 return ((long) 0);
      twisted[ntwisted++] = -col;
      sum[0] = col;
   } else {
      if (!live[col])
	 return ((long) 0);
      untwisted[nuntwisted++] = sum[0] = col;
   }
   for (i = 2, twopower = 1, mark = 1; i <= depth; i++, twopower <<= 1) {
      c = choice[i];
      for (j = 0; j < twopower; j++, mark++) {
	 b = sum[j] - c;
	 if (b < 0) {
	    if (!live[-b])
	       return ((long) 0);
	    twisted[ntwisted++] = -b;
	    sum[mark] = b;
	 } else {
	    if (!live[b])
	       return ((long) 0);
	    untwisted[nuntwisted++] = sum[mark] = b;
	 }
      }
   }

   /* Now we know that every coloring that theta-fits M has its code in
    * "live". We mark the corresponding entry of "live" by theta, that is,
    * set its second, third or fourth bit to 1 */

   if (on) {
      for (i = 0; i < ntwisted; i++)
	 live[twisted[i]] |= 8;
      for (i = 0; i < nuntwisted; i++)
	 live[untwisted[i]] |= 4;
   } else {
      for (i = 0; i < ntwisted; i++)
	 live[twisted[i]] |= 2;
      for (i = 0; i < nuntwisted; i++)
	 live[untwisted[i]] |= 2;
   }

   return ((long) 1);
}


long
updatelive(live, ncols, p)
long *p, ncols;
char *live;

/* runs through "live" to see which colourings still have `real' signed
 * matchings sitting on all three pairs of colour classes, and updates "live"
 * accordingly; returns 1 if nlive got smaller and stayed >0, and 0 otherwise */
{
   long i, nlive, newnlive;

   nlive = *p;
   newnlive = 0;
   if (live[0] > 1)
      live[0] = (char) 15;
   for (i = 0; i < ncols; i++) {
      if (live[i] != 15)
	 live[i] = 0;
      else {
	 newnlive++;
	 live[i] = 1;
      }
   }
   *p = newnlive;
   (void) printf("            %9ld", newnlive);
   (void) fflush(stdout);
   if ((newnlive < nlive) && (newnlive > 0))
      return ((long) 1);
   if (!newnlive)
      (void) printf("\n\n\n                  ***  D-reducible  ***\n\n");
   else
      (void) printf("\n\n\n                ***  Not D-reducible  ***\n");
   return ((long) 0);
}

void
strip(graph, edgeno)
tp_confmat graph;
tp_edgeno edgeno;

/* Numbers edges from 1 up, so that each edge has as many later edges in
 * triangles as possible; the ring edges are first.  edgeno[u][v] will be the
 * number of the edge with ends u,v if there is such an edge and 0 otherwise. */
{
   long d, h, u, v, w, x, verts, ring, term, maxint, maxes, max[VERTS];
   long inter, maxdeg, best, first, previous, *grav, done[VERTS];


   for (u = 1; u < VERTS; u++)
      for (v = 1; v < VERTS; v++)
	 edgeno[u][v] = 0;
   verts = graph[0][0];
   ring = graph[0][1];
   for (v = 1; v <= ring; v++) {
      u = (v > 1) ? v - 1 : ring;
      edgeno[u][v] = v;
      edgeno[v][u] = v;
   }
   for (v = 1; v <= verts; v++)
      done[v] = 0;
   term = 3 * (verts - 1) - ring;
   for (x = ring + 1; x <= verts; x++) {
      /* First we find all vertices from the interior that meet the "done"
       * vertices in an interval, and write them in max[1] .. max[maxes] */
      maxint = 0;
      maxes = 0;
      for (v = ring + 1; v <= verts; v++) {
	 if (done[v])
	    continue;
	 inter = ininterval(graph[v], done);
	 if (inter > maxint) {
	    maxint = inter;
	    maxes = 1;
	    max[1] = v;
	 } else if (inter == maxint)
	    max[++maxes] = v;
      }	/* for v bracket */
      /* From the terms in max we choose the one of maximum degree */
      maxdeg = 0;
      for (h = 1; h <= maxes; h++) {
	 d = graph[max[h]][0];
	 if (d > maxdeg) {
	    maxdeg = d;
	    best = max[h];
	 }
      }
      /* So now, the vertex "best" will be the next vertex to be done */

      grav = graph[best];
      d = grav[0];
      first = 1;
      previous = done[grav[d]];
      while ((previous) || (!done[grav[first]])) {
	 previous = done[grav[first++]];
	 if (first > d) {
	    first = 1;
	    break;
	 }
      }
      for (h = first; done[grav[h]]; h++) {
	 edgeno[best][grav[h]] = term;
	 edgeno[grav[h]][best] = term;
	 term--;
	 if (h == d) {
	    if (first == 1)
	       break;
	    h = 0;
	 }
      }
      done[best] = 1;
   }	/* for x bracket */
   /* This eventually lists all the internal edges of the configuration */

   /* Now we must list the edges between the interior and the ring */
   for (x = 1; x <= ring; x++) {
      maxint = 0;
      for (v = 1; v <= ring; v++) {
	 if (done[v])
	    continue;
	 u = (v > 1) ? v - 1 : ring;
	 w = (v < ring) ? v + 1 : 1;
	 inter = 3 * graph[v][0] + 4 * (done[u] + done[w]);
	 if (inter > maxint) {
	    maxint = inter;
	    best = v;
	 }
      }	/* for v bracket */
      grav = graph[best];
      u = (best > 1) ? best - 1 : ring;
      if (done[u]) {
	 for (h = grav[0] - 1; h >= 2; h--) {
	    edgeno[best][grav[h]] = term;
	    edgeno[grav[h]][best] = term;
	    term--;
	 }
      } else {
	 for (h = 2; h < grav[0]; h++) {
	    edgeno[best][grav[h]] = term;
	    edgeno[grav[h]][best] = term;
	    term--;
	 }
      }
      done[best] = 1;
   }	/* for x bracket */
}


long
ininterval(grav, done)
long grav[], done[];

/* if grav meets the done vertices in an interval of length >=1, it returns
 * the length of the interval, and otherwise returns 0 */
{
   long d, j, first, last, worried, length;

   d = grav[0];

   for (first = 1; (first < d) && (!done[grav[first]]); first++);
   if (first == d)
      return (done[grav[d]]);
   for (last = first; (last < d) && (done[grav[last + 1]]); last++);
   length = last - first + 1;
   if (last == d)
      return (length);
   if (first > 1) {
      for (j = last + 2; j <= d; j++)
	 if (done[grav[j]])
	    return ((long) 0);
      return (length);
   }
   worried = 0;
   for (j = last + 2; j <= d; j++) {
      if (done[grav[j]]) {
	 length++;
	 worried = 1;
      } else if (worried)
	 return ((long) 0);
   }
   return (length);
}

void
findangles(graph, angle, diffangle, sameangle, contract)
tp_confmat graph;
tp_angle angle,diffangle,sameangle;
long contract[];

/* writes into angle[i] all edges with number >i on a common triangle T say
 * with edge i; and if there is a contract X given, and i is not in X, writes
 * into diffangle[i] all such edges such that no edge of T is in X, and
 * writes into sameangle[i] all such edges not in X so that the third edge of
 * T is in X. Sets contract[i] to 1 if edge number i is in X and to zero
 * otherwise, checks that X is sparse, and if |X|=4 checks that X has a triad */
{

   long a, b, c, h, i, j, u, v, w, edges;
   tp_edgeno edgeno;
   long neighbour[VERTS];

   edges = 3 * graph[0][0] - 3 - graph[0][1];
   if (edges >= EDGES) {
      (void) printf("Configuration has more than %d edges\n", EDGES - 1);
      exit(20);
   }
   strip(graph, edgeno);
   for (i = 0; i < EDGES + 1; i++)
      contract[i] = 0;
   contract[0] = graph[0][4];	/* number of edges in contract */
   if (contract[0] < 0 || contract[0] > 4) {
      (void) printf("         ***  ERROR: INVALID CONTRACT  ***\n\n");
      exit(27);
   }
   for (i = 5; i <= 2 * contract[0] + 4; i++)
      if (graph[0][i] < 1 || graph[0][i] > graph[0][0]) {
	 (void) printf("         ***  ERROR: ILLEGAL CONTRACT  ***\n\n");
	 exit(29);
      }
   contract[EDGES] = graph[0][3];
   for (i = 1; i <= contract[0]; i++) {
      u = graph[0][2 * i + 3];
      v = graph[0][2 * i + 4];
      if (edgeno[u][v] < 1) {
	 (void) printf("         ***  ERROR: CONTRACT CONTAINS NON-EDGE  ***\n\n");
	 exit(29);
      }
      contract[edgeno[u][v]] = 1;
   }
   for (i = 1; i <= graph[0][1]; i++)
      if (contract[i]) {
	 (void) printf("         ***  ERROR: CONTRACT IS NOT SPARSE  ***\n\n");
	 exit(21);
      }
   for (i = 1; i <= edges; i++)
      diffangle[i][0] = sameangle[i][0] = angle[i][0] = 0;
   diffangle[0][0] = angle[0][0] = graph[0][0];
   diffangle[0][1] = angle[0][1] = graph[0][1];
   diffangle[0][2] = angle[0][2] = edges;

   for (v = 1; v <= graph[0][0]; v++) {
      for (h = 1; h <= graph[v][0]; h++) {
	 if ((v <= graph[0][1]) && (h == graph[v][0]))
	    continue;
	 i = (h < graph[v][0]) ? h + 1 : 1;
	 u = graph[v][h];
	 w = graph[v][i];
	 a = edgeno[v][w];
	 b = edgeno[u][w];
	 c = edgeno[u][v];
	 if (contract[a] && contract[b]) {
	    (void) printf("         ***  ERROR: CONTRACT IS NOT SPARSE  ***\n\n");
	    exit(22);
	 }
	 if (a > c) {
	    angle[c][++angle[c][0]] = a;
	    if ((!contract[a]) && (!contract[b]) && (!contract[c]))
	       diffangle[c][++diffangle[c][0]] = a;
	    if (contract[b])
	       sameangle[c][++sameangle[c][0]] = a;
	 }
	 if (b > c) {
	    angle[c][++angle[c][0]] = b;
	    if ((!contract[a]) && (!contract[b]) && (!contract[c]))
	       diffangle[c][++diffangle[c][0]] = b;
	    if (contract[a])
	       sameangle[c][++sameangle[c][0]] = b;
	 }
      }
   }

   /* checking that there is a triad */
   if (contract[0] < 4)
      return;
   for (v = graph[0][1] + 1; v <= graph[0][0]; v++) {
      /* v is a candidate triad */
      for (a = 0, i = 1; i <= graph[v][0]; i++) {
	 u = graph[v][i];
	 for (j = 5; j <= 12; j++)
	    if (u == graph[0][j]) {
	       a++;
	       break;
	    }
      }
      if (a < 3)
	 continue;
      if (graph[v][0] >= 6)
	 return;
      for (u = 1; u <= graph[0][0]; u++)
	 neighbour[u] = 0;
      for (i = 1; i <= graph[v][0]; i++)
	 neighbour[graph[v][i]] = 1;
      for (j = 5; j <= 12; j++) {
	 if (!neighbour[graph[0][j]])
	    return;
      }
   }
   (void) printf("         ***  ERROR: CONTRACT HAS NO TRIAD  ***\n\n");
   exit(28);
}


long
findlive(live, ncodes, angle, power, extentclaim)
long ncodes, power[], extentclaim;
tp_angle angle;
char *live;

/* computes {\cal C}_0 and stores it in live. That is, computes codes of
 * colorings of the ring that are not restrictions of tri-colorings of the
 * free extension. Returns the number of such codes */

{
   long j, c[EDGES], i, u, *am;
   long edges, ring, extent, bigno;
   long forbidden[EDGES];	/* called F in the notes */

   ring = angle[0][1];
   edges = angle[0][2];
   bigno = (power[ring + 1] - 1) / 2;	/* needed in "record" */
   c[edges] = 1;
   j = edges - 1;
   c[j] = 2;
   forbidden[j] = 5;
   for (extent = 0;;) {
      while (forbidden[j] & c[j]) {
	 c[j] <<= 1;
	 while (c[j] & 8) {
	    if (j >= edges - 1) {
	       printstatus(ring, ncodes, extent, extentclaim);
	       return (ncodes - extent);
	    }
	    c[++j] <<= 1;
	 }
      }
      if (j == ring + 1) {
	 record(c, power, ring, angle, live, &extent, bigno);
	 c[j] <<= 1;
	 while (c[j] & 8) {
	    if (j >= edges - 1) {
	       printstatus(ring, ncodes, extent, extentclaim);
	       return (ncodes - extent);
	    }
	    c[++j] <<= 1;
	 }
      } else {
	 am = angle[--j];
	 c[j] = 1;
	 for (u = 0, i = 1; i <= am[0]; i++)
	    u |= c[am[i]];
	 forbidden[j] = u;
      }
   }
}

void
checkcontract(live, nlive, diffangle, sameangle, contract, power)
tp_angle diffangle, sameangle;
long nlive, contract[EDGES + 1], power[];
char *live;

/* checks that no colouring in live is the restriction to E(R) of a
 * tri-coloring of the free extension modulo the specified contract */
{
   long j, c[EDGES], i, u, *dm, *sm;
   long ring, bigno;
   long forbidden[EDGES];	/* called F in the notes */
   long start;	/* called s in the notes */

   if (!nlive) {
      if (!contract[0]) {
	 (void) printf("\n");
	 return;
      } else {
	 (void) printf("         ***  ERROR: CONTRACT PROPOSED  ***\n\n");
	 exit(23);
      }
   }
   if (!contract[0]) {
      (void) printf("       ***  ERROR: NO CONTRACT PROPOSED  ***\n\n");
      exit(24);
   }
   if (nlive != contract[EDGES]) {
      (void) printf("       ***  ERROR: DISCREPANCY IN EXTERIOR SIZE  ***\n\n");
      exit(25);
   }
   ring = diffangle[0][1];
   bigno = (power[ring + 1] - 1) / 2;	/* needed in "inlive" */
   start = diffangle[0][2];
   while (contract[start])
      start--;
   c[start] = 1;
   j = start;
   while (contract[--j]);
   dm = diffangle[j];
   sm = sameangle[j];
   c[j] = 1;
   for (u = 4, i = 1; i <= dm[0]; i++)
      u |= c[dm[i]];
   for (i = 1; i <= sm[0]; i++)
      u |= ~c[sm[i]];
   forbidden[j] = u;

   for (;;) {
      while (forbidden[j] & c[j]) {
	 c[j] <<= 1;
	 while (c[j] & 8) {
	    while (contract[++j]);
	    if (j >= start) {
	       (void) printf("               ***  Contract confirmed  ***\n\n");
	       return;
	    }
	    c[j] <<= 1;
	 }
      }
      if (j == 1) {
	 if (inlive(c, power, ring, live, bigno)) {
	    (void) printf("       ***  ERROR: INPUT CONTRACT IS INCORRECT  ***\n\n");
	    exit(26);
	 }
	 c[j] <<= 1;
	 while (c[j] & 8) {
	    while (contract[++j]);
	    if (j >= start) {
	       (void) printf("               ***  Contract confirmed  ***\n\n");
	       return;
	    }
	    c[j] <<= 1;
	 }
	 continue;
      }
      while (contract[--j]);
      dm = diffangle[j];
      sm = sameangle[j];
      c[j] = 1;
      for (u = 0, i = 1; i <= dm[0]; i++)
	 u |= c[dm[i]];
      for (i = 1; i <= sm[0]; i++)
	 u |= ~c[sm[i]];
      forbidden[j] = u;
   }
}

void
printstatus(ring, totalcols, extent, extentclaim)
long ring, totalcols, extent, extentclaim;

{
   static long simatchnumber[] = {0L, 0L, 1L, 3L, 10L, 30L, 95L, 301L, 980L, 3228L, 10797L, 36487L, 124542L, 428506L, 1485003L};

   (void) printf("\n\n   This has ring-size %ld, so there are %ld colourings total,\n",ring, totalcols);
   (void) printf("   and %ld balanced signed matchings.\n",simatchnumber[ring]);

   (void) printf("\n   There are %ld colourings that extend to the configuration.", extent);
   if (extent != extentclaim) {
      (void) printf("\n   *** ERROR: DISCREPANCY IN NUMBER OF EXTENDING COLOURINGS ***\n");
      exit(31);
   }
   (void) printf("\n\n            remaining               remaining balanced\n");
   (void) printf("           colourings               signed matchings\n");
   (void) printf("\n              %7ld", totalcols - extent);
   (void) fflush(stdout);
}

void
record(col, power, ring, angle, live, p, bigno)
long col[], power[], ring, angle[][5], *p, bigno;
char *live;

/* Given a colouring specified by a 1,2,4-valued function "col", it computes
 * the corresponding number, checks if it is in live, and if so removes it. */

{
   long weight[5], colno, sum, i, min, max, w;

   for (i = 1; i < 5; i++)
      weight[i] = 0;
   for (i = 1; i <= ring; i++) {
      sum = 7 - col[angle[i][1]] - col[angle[i][2]];
      weight[sum] += power[i];
   }
   min = max = weight[4];
   for (i = 1; i <= 2; i++) {
      w = weight[i];
      if (w < min)
	 min = w;
      else if (w > max)
	 max = w;
   }
   colno = bigno - 2 * min - max;
   if (live[colno]) {
      (*p)++;
      live[colno] = 0;
   }
}

long
inlive(col, power, ring, live, bigno)
long col[], power[], ring, bigno;
char *live;

/* Same as "record" above, except now it returns whether the colouring is in
 * live, and does not change live. */
{
   long weight[5], colno, i, min, max, w;

   for (i = 1; i < 5; i++)
      weight[i] = 0;
   for (i = 1; i <= ring; i++)
      weight[col[i]] += power[i];
   min = max = weight[4];
   for (i = 1; i <= 2; i++) {
      w = weight[i];
      if (w < min)
	 min = w;
      else if (w > max)
	 max = w;
   }
   colno = bigno - 2 * min - max;
   return ((long) live[colno]);
}


long
ReadConf(A, F, C)
tp_confmat A;
FILE *F;
long *C;

/* Reads one graph from file F and stores in A, if C!=NULL puts coordinates
 * there. If successful returns 0, on end of file returns 1, if error exits. */
{
   char S[256], *t, name[256];
   long d, i, j, k, n, r, a, p;

   name[0] = '\0';
   t = name;
   while (*t == '\0' || *t == '\n') {
      if (fgets(name, sizeof(name), F) == NULL)
	 return ((long) 1);
      for (t = name; *t == ' ' || *t == '\t'; t++);
   }
   (void) fgets(S, sizeof(S), F);
   /* No verts, ringsize, no extendable colourings, max cons subset */
   if (sscanf(S, "%ld%ld%ld%ld", &A[0][0], &A[0][1], &A[0][2], &A[0][3]) != 4) {
      (void) printf("Error on line 2 while reading %s\n", name);
      exit(11);
   }
   n = A[0][0];
   r = A[0][1];
   if (n >= VERTS) {
      (void) printf("%s has more than %d vertices\n", name, VERTS - 1);
      exit(17);
   }
   (void) fgets(S, sizeof(S), F);	/* Contract */
   i = sscanf(S, "%ld%ld%ld%ld%ld%ld%ld%ld%ld", &A[0][4], &A[0][5], &A[0][6], &A[0][7], &A[0][8], &A[0][9], &A[0][10], &A[0][11], &A[0][12]);
   if (2 * A[0][4] + 1 != i) {
      (void) printf("Error on line 3 while reading %s\n", name);
      exit(13);
   }
   /* Reading adjacency list */
   for (i = 1; i <= n; i++) {
      (void) fgets(S, sizeof(S), F);
      if (sscanf(S, "%ld%ld", &j, &A[i][0]) != 2 || i != j) {
	 (void) printf("Error while reading vertex %ld of %s\n", i, name);
	 exit(14);
      }
      if (A[i][0] >= DEG) {
	 (void) printf("Vertex degree larger than %d in %s\n", DEG - 1, name);
	 exit(14);
      }

      for (t = S; *t < '0' || *t > '9'; t++);
      for (; *t >= '0' && *t <= '9'; t++);
      for (; *t < '0' || *t > '9'; t++);
      for (; *t >= '0' && *t <= '9'; t++);
      for (j = 1; j <= A[i][0]; j++) {
	 if (sscanf(t, "%ld", &A[i][j]) != 1) {
	    (void) printf("Error while reading neighbour %ld of %ld of %s\n", j, i, name);
	    exit(15);
	 }
	 for (; *t < '0' || *t > '9'; t++);
	 for (; *t >= '0' && *t <= '9'; t++);
      }	/* j */
   }	/* i */

   /* Reading coordinates */
   if (C != NULL)
      C[0] = n;
   for (i = 1; i <= n;) {
      (void) fgets(S, sizeof(S), F);
      if (C == NULL)
	 k = sscanf(S, "%ld%ld%ld%ld%ld%ld%ld%ld", &j, &j, &j, &j, &j, &j, &j, &j);
      else
	 k = sscanf(S, "%ld%ld%ld%ld%ld%ld%ld%ld", C + i, C + i + 1, C + i + 2, C + i + 3, C + i + 4, C + i + 5, C + i + 6, C + i + 7);
      if (k == 0) {
	 (void) printf("Error while reading coordinates of %s\n", name);
	 exit(17);
      }
      i += k;
   }	/* for i */
   (void) fgets(S, sizeof(S), F);
   for (t = S; *t == ' ' || *t == '\t'; t++);
   if (*t != '\n' && *t != '\0') {
      (void) printf("No blank line following configuration %s\n", name);
      exit(18);
   }
   /* verifying condition (1) */
   if (r < 2 || n <= r)
      ReadErr(1, name);
   /* condition (2) */
   for (i = 1; i <= r; i++)
      if (A[i][0] < 3 || A[i][0] >= n)
	 ReadErr(2, name);
   for (i = r + 1; i <= n; i++)
      if (A[i][0] < 5 || A[i][0] >= n)
	 ReadErr(2, name);
   /* condition (3) */
   for (i = 1; i <= n; i++)
      for (j = 1; j <= A[i][0]; j++)
	 if (A[i][j] < 1 || A[i][j] > n)
	    ReadErr(3, name);
   /* condition (4) */
   for (i = 1; i <= r; i++) {
      if (A[i][1] != (i == r ? 1 : i + 1))
	 ReadErr(4, name);
      if (A[i][A[i][0]] != (i == 1 ? r : i - 1))
	 ReadErr(4, name);
      for (j = 2; j < A[i][0]; j++)
	 if (A[i][j] <= r || A[i][j] > n)
	    ReadErr(4, name);
   }
   /* condition (5) */
   for (i = 1, k = 0; i <= n; i++)
      k += A[i][0];
   if (k != 6 * (n - 1) - 2 * r)
      ReadErr(5, name);
   /* condition (6) */
   for (i = r + 1; i <= n; i++) {
      k = 0;
      d = A[i][0];
      for (j = 1; j <= d; j++)
	 if (A[i][j] > r && A[i][j < d ? j + 1 : 1] <= r) {
	    k++;
	    if (A[i][j < d - 1 ? j + 2 : j + 2 - d] <= r)
	       k++;
	 }
      if (k > 2)
	 ReadErr(6, name);
   }
   /* condition (7) */
   for (i = 1; i <= n; i++)
      for (j = 1; j <= A[i][0]; j++) {
	 if (j == A[i][0]) {
	    if (i <= r)
	       continue;
	    a = A[i][1];
	 } else
	    a = A[i][j + 1];
	 k = A[i][j];
	 for (p = 1; p < A[k][0]; p++)
	    if (a == A[k][p] && i == A[k][p + 1])
	       break;
	 if (p == A[k][0] && (a != A[k][p] || i != A[k][1]))
	    ReadErr(7, name);
      }
   return ((long) 0);
}/* ReadConf */

void
ReadErr(n, name)
int n;
char name[];
{
   (void) printf("Error %d while reading configuration %s\n", n, name);
   exit(57);
}

/* End of file reduce.c */
