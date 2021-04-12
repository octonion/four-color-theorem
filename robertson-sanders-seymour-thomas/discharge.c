/* discharge.c */
/***************/

/* This is part II of two programs that serve as supplements to the paper
 * `The Four-Colour Theorem' by N. Robertson, D. P. Sanders, P. D. Seymour
 * and R. Thomas. Please refer to the manuscript `Discharging Cartwheels' by
 * the same authors (referred to as [D]) for a description of this program */

/* Copyright 1995 by N. Robertson, D.P. Sanders, P.D. Seymour and R. Thomas  */
/* Permission to use for the purpose of scholarly research is hereby granted */

/* Version 1,  24 May 1995, slightly modified 14 January 1997 */

#include <stdio.h>
#include <stdlib.h>

/* constants */
#define VERTS      27	/* max number of vertices in a free completion + 1 */
#define DEG        13	/* max degree of a vertex in a free completion + 1 */
/* must be at least 13 because of row 0            */
#define CONFS      640	/* max number of configurations	 */
#define MAXVAL     12
#define CARTVERT   5*MAXVAL+2	/* domain of l_A, u_A, where A is an axle */
#define RULEFILE   "rules"	/* file containing rules */
#define UNAVSET    "unavoidable.conf"	/* file containing unav set */
#define OUTLETFILE "outlet.et"	/* outlets will be written into this file */
#define INFTY      12	/* the "12" in the definition of limited part  */
#define MAXOUTLETS 110	/* max number of outlets */
#define MAXSTR     256	/* max length of an input string */
#define MAXSYM     50	/* max number of symmetries */
#define MAXELIST   134	/* length of edgelist[a][b] */
#define MAXASTACK  5	/* max height of Astack (see "Reduce") */
#define MAXLEV     12	/* max level of an input line + 1 */

/* print modes */
#define PRTALL  4	/* maximum information */
#define PRTPAI  3	/* to print hubcaps except reducibility */
#define PRTBAS  2	/* basics only */
#define PRTLIN  1	/* input line only */

/* macros */
#define ALLOC(result, count, type) {                                         \
        if (!(result = (type *) malloc ((count) * sizeof (type)))) {         \
                (void) fprintf (stderr, "Out of memory\n");                  \
                exit (1);                                                    \
        }                                                                    \
    }

/* type definitions */
typedef int tp_vertices[CARTVERT];
typedef int tp_adjmat[CARTVERT][CARTVERT];
typedef long tp_confmat[VERTS][DEG];	/* must be long */

typedef struct {
   tp_vertices low;
   tp_vertices upp;
} tp_axle;
typedef struct {
   int number;	/* +/-n for outlet corresponding to rule n, always !=0 */
   int nolines;	/* |M(T)| */
   int value;
   int pos[17];
   int low[17];
   int upp[17];
} tp_outlet;
typedef struct {
   int n;
   int m;
} tp_cond;	/* condition */
typedef struct {
   tp_outlet *T;
   int x;
} tp_posout;	/* positioned outlet */
typedef struct {
   int u;
   int v;
   int z;
   int xi;
} tp_query;
typedef tp_query tp_question[VERTS];
typedef int tp_edgelist[12][9][MAXELIST];


/* function prototypes */
#ifdef PROTOTYPE_MAX
void Error(char[], int);
int Getstring(char[]);
void CheckCondition(char *, tp_axle *, tp_outlet[], int *, int, int, int);
void CheckSymmetry(char *, tp_axle *, tp_outlet[], int, int);
void CheckHubcap(tp_axle *, char[], int, int);
void CheckBound(tp_axle *, tp_posout[], int[], int, int, int, int, int);
int OutletForced(tp_axle *, tp_outlet *, int);
int OutletPermitted(tp_axle *, tp_outlet *, int);
int ReflForced(tp_axle *, tp_outlet *, int);
void PrintOutlet(int, FILE *, tp_outlet *);
int Reduce(tp_axle *, int, int);
void CheckIso(tp_confmat, tp_axle *, tp_vertices, int);
void CopyAxle(tp_axle *, tp_axle *);
void PrintAxle(tp_axle *);
void Indent(int, char[]);
void Radius(tp_confmat);
int GetConf(tp_confmat *, tp_question *);
long ReadConf(tp_confmat, FILE *, long *);
void ReadErr(int, char[]);
int ReadOutlets(tp_axle *, tp_outlet[]);
int DoOutlet(tp_axle *, int, int[], int[], int[], int[], tp_outlet[], int);
void GetQuestion(tp_confmat, tp_question);
void Getadjmat(tp_axle *, tp_adjmat);
void DoFan(int, int, int, tp_adjmat);
void GetEdgelist(tp_axle *, tp_edgelist);
void AddToList(tp_edgelist, int, int, tp_vertices);
int RootedSubConf(int[], tp_adjmat, tp_question, int[], int, int, int);
int SubConf(tp_adjmat, int[], tp_question, tp_edgelist, int[]);

#else
void Error();
int Getstring();
void CheckCondition();
void CheckSymmetry();
void CheckHubcap();
void CheckBound();
int OutletForced();
int OutletPermitted();
int ReflForced();
void PrintOutlet();
int Reduce();
void CheckIso();
void CopyAxle();
void PrintAxle();
void Indent();
void Radius();
int GetConf();
long ReadConf();
void ReadErr();
int ReadOutlets();
int DoOutlet();
void GetQuestion();
void Getadjmat();
void DoFan();
void GetEdgelist();
void AddToList();
int RootedSubConf();
int SubConf();

#endif

/**************************************************************************
       main
Intializes, then reads input lines one by one and takes appropriate action
***************************************************************************/
main(ac, av)
int ac;
char *av[];
{
   int lev;	/* level of line being processed */
   int deg;	/* degree of hub; constant throughout */
   int prtline;	/* print details about line number "prtline" */
   int nosym;	/* number of symmetries, see "sym" below */
   char str[MAXSTR];	/* holds input line */
   char fname[MAXSTR];	/* name of file to be tested */
   tp_axle *axles, *A;	/* axles[l] is A_l of [D] */
   tp_outlet *sym;	/* sym[i] (i=0,..,nosym) are T_i (i=0,..,t-1) of [D] */
   int i, a, printmode, print, lineno;
   char *ch;

   printmode = prtline = 0;
   if (ac < 2) {
      (void) fprintf(stderr, "Usage: %s <filename> [<lineno> <print mode>]\n", av[0]);
      (void) fprintf(stderr, "If lineno is given and is positive will print details about that line.\n");
      (void) fprintf(stderr, "If lineno is 0 will print details about all lines. ");
      (void) fprintf(stderr, "Print modes are:\n");
      (void) fprintf(stderr, "%d  input lines only\n", PRTLIN);
      (void) fprintf(stderr, "%d  basic information\n", PRTBAS);
      (void) fprintf(stderr, "%d  hubcaps w/o reducibility\n", PRTPAI);
      (void) fprintf(stderr, "%d  hubcaps w/  reducibility\n", PRTALL);
      (void) fprintf(stderr, "WARNING: The last two generate a lot of output.\n");
      (void) fprintf(stderr, "Input command line arguments: ");
      (void) fflush(stderr);
      (void) fgets(str, sizeof(str), stdin);
      (void) strcpy(fname, "present7");
      (void) sscanf(str, "%s%d%d", fname, &prtline, &printmode);
   } else {
      if (ac >= 4) {
	 prtline = atoi(av[2]);
	 printmode = atoi(av[3]);
      }
      (void) strcpy(fname, av[1]);
   }

   (void) Getstring(fname);	/* to open presentation file */
   (void) printf("Verifying %s\n", fname);
   (void) fflush(stdout);
   if (prtline == 0)
      print = printmode;
   else
      print = 0;
   lineno = Getstring(str);	/* first line containing degree of hub */
   if (print >= PRTLIN) {
      (void) printf("%4d:%s", lineno, str);
      (void) fflush(stdout);
   }
   deg = 0;
   (void) sscanf(str, "Degree%d", &deg);
   if (deg < 5 || deg > MAXVAL)
      Error("Invalid degree", lineno);
   if (print >= PRTBAS)
      (void) printf("Allocating %d bytes for axles, %d bytes for sym\n",
	  (MAXLEV + 1) * sizeof(tp_axle), (MAXSYM + 1) * sizeof(tp_outlet));
   axles = (tp_axle *) malloc((MAXLEV + 1) * sizeof(tp_axle));
   sym = (tp_outlet *) malloc((MAXSYM + 1) * sizeof(tp_outlet));
   if (axles == NULL || sym == NULL) {
      fflush(stdout);
      (void) fprintf(stderr, "By far not enough memory\n");
      exit(26);
   }
   axles->low[0] = axles->upp[0] = deg;
   for (i = 1; i <= 5 * deg; i++) {
      axles->low[i] = 5;
      axles->upp[i] = INFTY;
   }
   CheckHubcap(axles, NULL, 0, print);	/* read rules, compute outlets */
   (void) Reduce(NULL, 0, 0);	/* read unavoidable set */

   for (lev = 0, nosym = 0; lev >= 0;) {
      if (lev >= MAXLEV) {
	 fflush(stdout);
	 (void) fprintf(stderr, "More than %d levels", MAXLEV);
	 Error("", lineno);
      }
      A = &axles[lev];
      if (lineno == prtline)
	 print = 0;
      lineno = Getstring(str);
      if (lineno == prtline)
	 print = printmode;
      if (print >= PRTLIN) {
	 (void) printf("%4d:%s", lineno, str);
	 fflush(stdout);
      }
      for (ch = str; *ch == ' '; ch++)	/* do nothing */
	 ;
      if (sscanf(ch, "L%d", &a) != 1 || a != lev) {
	 fflush(stdout);
	 (void) fprintf(stderr, "Level %d expected on line %d\n", lev, lineno);
	 exit(6);
      }
      for (; *ch != ' '; ch++)	/* do nothing */
	 ;
      for (; *ch == ' '; ch++)	/* do nothing */
	 ;
      switch (*ch) {
      case 'S':
	 CheckSymmetry(ch, A, sym, nosym, lineno);
	 break;
      case 'R':
	 if (Reduce(A, lineno, print >= PRTBAS ? 1 : 0) != 1)
	    Error("Reducibility failed", lineno);
	 break;
      case 'H':
	 CheckHubcap(A, str, lineno, print);
	 break;
      case 'C':
	 CheckCondition(ch, A, sym, &nosym, lev, lineno, print);
	 lev++;
	 continue;
      default:
	 Error("Invalid instruction", lineno);
      }	/* switch */

      /* delete symetries */
      if (print >= PRTBAS && sym[nosym - 1].nolines - 1 >= lev) {
	 (void) printf("Deleting symetries:");
	 for (i = nosym; i >= 1 && sym[i - 1].nolines - 1 >= lev; i--)
	    (void) printf(" %d", sym[i - 1].number);
	 (void) printf("\n");
	 (void) fflush(stdout);
      }
      for (; nosym >= 1 && sym[nosym - 1].nolines - 1 >= lev; nosym--)
	  /* do nothing */ ;

      lev--;
   }	/* for lev */
   /* final check */
   lineno = Getstring(str);
   ch = str;
   if (*ch++ != 'Q' || *ch++ != '.' || *ch != 'E')
      Error("`Q.E.D.' expected", lineno);
   (void) printf("%s verified.\n", fname);
   fflush(stdout);
   return (0);
}/* main */

/*************************************************************************
       Error
Prints an error message and exits.
*************************************************************************/
void
Error(message, lineno)
char message[];
int lineno;
{
   fflush(stdout);
   (void) fprintf(stderr, "%s on line %d\n", message, lineno);
   exit(lineno);
}/* Error */


/*************************************************************************
       Getstring
On first call opens file str for reading, on each subsequent call reads
a line from that file into str (at most MAXSTR characters), and returns
the number of the line read.
*************************************************************************/
int
Getstring(str)
char str[];
{
   static int lineno = 0;
   static FILE *fin = NULL;

   if (fin == NULL) {
      fin = fopen(str, "r");
      if (fin == NULL) {
	 fflush(stdout);
	 (void) fprintf(stderr, "Unable to open file %s for reading\n", str);
	 exit(3);
      }
      return (0);
   }
   ++lineno;
   if (fgets(str, MAXSTR, fin) != NULL)
      return (lineno);
   Error("Unexpected end of input file", lineno);
   exit(46);
}/* Getstring */

/*************************************************************************
       CheckCondition
Verifies condition line as described in [D]
*************************************************************************/
void
CheckCondition(S, A, sym, pnosym, lev, lineno, print)
int lev;	/* level of input line */
int lineno;	/* number of input line */
int *pnosym;	/* number of symmetries */
tp_outlet sym[];	/* symmetries (see "main") */
char *S;	/* input line */
tp_axle *A;	/* called A_lev in [D] */
int print;	/* print mode */
{
   int n, m, i, j, deg, good;
   static tp_cond cond[MAXLEV];
   tp_outlet *T;

   deg = A->low[0];
   if (sscanf(S, "%*s%d%d", &n, &m) != 2)
      Error("Syntax error", lineno);

   /* check condition and compatibility with A */
   if (n < 1 || n > 5 * deg)
      Error("Invalid vertex in condition", lineno);
   if (m < -8 || m > 9 || (m > -5 && m < 6))
      Error("Invalid condition", lineno);
   j = (n - 1) / deg;
   i = (n - 1) % deg + 1;
   if (n > 2 * deg && (A->low[i] != A->upp[i] || A->low[i] < j + 4))
      Error("Condition not compatible with A", lineno);
   CopyAxle(A + 1, A);
   if (m > 0) {	/* new lower bound */
      if (A->low[n] >= m || m > A->upp[n])
	 Error("Invalid lower bound in condition", lineno);
      A->upp[n] = m - 1;
      (A + 1)->low[n] = m;
   } else {	/* new upper bound */
      if (A->low[n] > -m || -m >= A->upp[n])
	 Error("Invalid upper bound in condition", lineno);
      A->low[n] = 1 - m;
      (A + 1)->upp[n] = -m;
   }	/* new upper bound */

   /* remember symmetry unless contains a fan vertex */
   for (i = 0, good = 1; i <= lev; i++)
      if (cond[i].n > 2 * deg || cond[i].n < 1)
	 good = 0;
   if (good) {	/* remember symmetry */
      if (*pnosym >= MAXSYM)
	 Error("Too many symmetries", lineno);
      if (print >= PRTBAS) {
	 (void) printf("Adding symmetry:");
      }
      T = &sym[(*pnosym)++];
      T->number = lineno;
      T->value = 1;
      T->nolines = lev + 1;
      for (i = 0; i <= lev; ++i) {
	 T->pos[i] = cond[i].n;
	 if (cond[i].m > 0) {
	    T->low[i] = cond[i].m;
	    T->upp[i] = INFTY;
	 } else {
	    T->low[i] = 5;
	    T->upp[i] = -cond[i].m;
	 }
	 if (print >= PRTBAS)
	    (void) printf(" (%d,%d,%d)", T->pos[i], T->low[i], T->upp[i]);
      }
      if (print >= PRTBAS) {
	 (void) printf("\n");
	 (void) fflush(stdout);
      }
   } else if (print >= PRTBAS) {
      (void) printf("Symmetry not added\n");
      (void) fflush(stdout);
   }
   cond[lev].n = n;
   cond[lev].m = m;
   cond[lev + 1].n = 0;
   cond[lev + 1].m = 0;
}/* CheckCondition */


/*************************************************************************
       CheckSymmetry
Verifies symmetry line as described in [D]
*************************************************************************/
void
CheckSymmetry(S, A, sym, nosym, lineno)
int nosym, lineno;
char *S;	/* input line */
tp_axle *A;
tp_outlet sym[];
{
   int k, epsilon, level, line, i;
   tp_outlet *T;

   if (sscanf(S, "%*s%d%d%d%d", &k, &epsilon, &level, &line) != 4)
      Error("Syntax error", lineno);
   if (k < 0 || k > A->low[0] || epsilon < 0 || epsilon > 1)
      Error("Illegal symmetry", lineno);
   for (i = 0, T = sym; i < nosym; i++, T++)
      if (T->number == line)
	 break;
   if (i >= nosym)
      Error("No symmetry as requested", lineno);
   if (T->nolines != level + 1)
      Error("Level mismatch", lineno);
   if (epsilon == 0) {
      if (OutletForced(A, T, k + 1) != 1)
	 Error("Invalid symmetry", lineno);
   } else {
      if (ReflForced(A, T, k + 1) != 1)
	 Error("Invalid reflected symmetry", lineno);
   }
}/* CheckSymmetry */


/*************************************************************************
     CheckHubcap
If str==NULL it assumes that A is the trivial axle of degree deg, where
deg=A->low[0]. It reads rules and computes the corresponding outlets. It
writes the outlets into the file specified by OUTLETFILE so they can be
verified for accuracy.
If str!=NULL it verifies hubcap line as described in [D]
**************************************************************************/
void
CheckHubcap(A, str, lineno, print)
int lineno, print;
tp_axle *A;
char str[];	/* input line */
{
   char *ch;
   int x[MAXVAL + 2], y[MAXVAL + 2], v[MAXVAL + 2];
   int covered[MAXVAL + 2], aux[MAXVAL + 2];
   int i, j, a, total, deg;
   int s[2 * MAXOUTLETS + 1];
   FILE *F = NULL;
   static tp_outlet outlet[MAXOUTLETS], *T;
   static int nouts;
   static tp_posout posout[2 * MAXOUTLETS];

   if (str == NULL) {
      nouts = ReadOutlets(A, outlet);
      for (i = 0; i < nouts; i++)
	 posout[i].T = posout[i + nouts].T = outlet + i;
      F = fopen(OUTLETFILE, "w");
      if (F != NULL) {
	 for (i = 0; i < nouts; i++)
	    PrintOutlet(i, F, outlet + i);
	 (void) fclose(F);
	 (void) printf("Outlets written into file `%s'.\n", OUTLETFILE);
	 fflush(stdout);
      }
      return;
   }
   /* This part is executed if str!=NULL */
   deg = A->low[0];
   for (ch = str; *ch == ' '; ch++);
   for (; *ch != ' '; ch++);
   for (; *ch == ' '; ch++);
   for (; *ch != ' '; ch++);
   for (; *ch == ' '; ch++);
   for (i = 1; *ch != '\0' && *ch != '\n'; i++) {
      if (i > MAXVAL)
	 Error("Too many hubcap elements", lineno);
      if (sscanf(ch, "(%d,%d,%d)", x + i, y + i, v + i) != 3)
	 Error("Syntax error", lineno);
      for (; *ch != ' ' && *ch != '\0' && *ch != '\n'; ch++);
      for (; *ch == ' '; ch++);
   }
   x[0] = i - 1;

   if (print >= PRTBAS) {
      (void) printf("Testing hubcap for:\n");
      PrintAxle(A);
      (void) printf("Forced positioned outlets:");
      for (i = 1; i <= deg; i++) {
	 a = 0;	/* a=1 if edge number printed */
	 for (T = outlet, j = 0; j < nouts; ++j, ++T)
	    if (OutletForced(A, T, i)) {
	       if (a == 0) {
		  (void) printf("\nEdge %2d: ", i);
		  a = 1;
	       }
	       (void) printf("%2d ", T->number);
	    }
      }
      (void) printf("\n");
      (void) fflush(stdout);
   }
   total = 0;
   for (i = 1; i <= deg; ++i)
      covered[i] = aux[i] = 0;
   for (i = 1; i <= x[0]; ++i) {
      if (x[i] < 1 || x[i] > deg || y[i] < 1 || y[i] > deg) {
	 fflush(stdout);
	 (void) fprintf(stderr, "Invalid hubcap member (%d,%d,%d)", x[i], y[i], v[i]);
	 Error("", lineno);
      }
      if (x[i] == y[i]) {
	 total += 2 * v[i];	/* repeated hubcap members listed once */
	 if (covered[x[i]])
	    Error("Invalid double cover", lineno);
	 covered[x[i]] = -1;
      } else {
	 total += (aux[x[i]] = v[i]);
	 if (covered[x[i]] == -1 || covered[y[i]] == -1)
	    Error("Invalid double cover", lineno);
	 covered[x[i]] = covered[x[i]] == 0 ? y[i] : -1;
	 covered[y[i]] = covered[y[i]] == 0 ? x[i] : -1;
      }
   }
   for (i = 1; i <= deg; ++i) {
      if (covered[i] == 0)
	 Error("Invalid hubcap", lineno);
      if (covered[i] == -1)
	 continue;
      if (covered[covered[i]] != i)
	 Error("Invalid hubcap", lineno);
      total += aux[i];	/* repeated hubcap members are only listed once */
   }

   if (print >= PRTBAS)
      (void) printf("Total double cover cost is %d\n", total);
   if (total > 20 * (deg - 6) + 1) {
      fflush(stdout);
      (void) fprintf(stderr, "Double cover has cost %d. ", total);
      Error("Hubcap does not satisfy (H2)", lineno);
   }
   for (i = 1; i <= x[0]; i++) {
      if (print >= PRTPAI)
	 (void) printf("\n-->Checking hubcap member (%d,%d,%d)\n", x[i], y[i], v[i]);
      for (j = 0; j < nouts; j++) {
	 posout[j].x = x[i];
	 s[j] = 0;
      }
      if (x[i] != y[i])
	 for (; j < 2 * nouts; j++) {
	    posout[j].x = y[i];
	    s[j] = 0;
	 }
      s[j] = 99;	/* to indicate end of list */
      CheckBound(A, posout, s, v[i], 0, 0, lineno, print);
   }	/* i */
   if (print >= PRTPAI) {
      (void) printf("\n");
      (void) fflush(stdout);
   }
   return;
}/* CheckHubcap */

/*************************************************************************
     CheckBound
Verifies (H1)
*************************************************************************/
void
CheckBound(A, posout, s, maxch, pos, depth, lineno, print)
int maxch, s[], pos, depth, lineno, print;
tp_posout posout[];
tp_axle *A;
{
   int deg, i, p, x, good, forcedch, allowedch;
   int *sprime;
   tp_axle *AA;
   tp_posout *PO;

   deg = A->low[0];

   /* compute forced and permitted rules, allowedch, forcedch, update s */
   forcedch = allowedch = 0;
   for (i = 0, PO = posout; s[i] < 99; i++, PO++) {
      if (s[i] > 0)
	 forcedch += PO->T->value;
      if (s[i])
	 continue;
      if (OutletForced(A, PO->T, PO->x)) {
	 s[i] = 1;
	 forcedch += PO->T->value;
      } else if (!OutletPermitted(A, PO->T, PO->x))
	 s[i] = -1;
      else if (PO->T->value > 0)
	 allowedch += PO->T->value;
   }

   if (print >= PRTPAI) {
      Indent(depth, "POs: ");
      for (i = 0, PO = posout; s[i] < 99; i++, PO++) {
	 if (s[i] < 0)
	    continue;
	 if (s[i] == 0)
	    (void) printf("?");
	 (void) printf("%d,%d ", PO->T->number, PO->x);
      }
      (void) printf("\n");
   }
   /* check if inequality holds */
   if (forcedch + allowedch <= maxch) {
      if (print >= PRTPAI)
	 Indent(depth, "Inequality holds. Case done.\n");
      return;
   }
   /* check reducibility */
   if (forcedch > maxch) {
      if (Reduce(A, lineno, print >= PRTALL ? 1 : 0) != 1)
	 Error("Incorrect hubcap upper bound", lineno);
      if (print >= PRTPAI && print < PRTALL)
	 Indent(depth, "Reducible. Case done.\n");
      return;
   }
   ALLOC(sprime, 2 * MAXOUTLETS + 1, int);
   ALLOC(AA, 1, tp_axle);
   for (PO = posout + pos; s[pos] < 99; pos++, PO++) {
      if (s[pos] || PO->T->value < 0)
	 continue;
      x = PO->x;

      /* accepting positioned outlet PO, computing AA */
      CopyAxle(AA, A);
      for (i = 0; i < PO->T->nolines; ++i) {
	 p = PO->T->pos[i];
	 p = x - 1 + (p - 1) % deg < deg ? p + x - 1 : p + x - 1 - deg;
	 if (PO->T->low[i] > AA->low[p])
	    AA->low[p] = PO->T->low[i];
	 if (PO->T->upp[i] < AA->upp[p])
	    AA->upp[p] = PO->T->upp[i];
	 if (AA->low[p] > AA->upp[p])
	    Error("Unexpected error 321", lineno);
      }	/* i */

      /* Check if a previously rejected positioned outlet is forced to apply */
      good = 1;
      for (i = 0; i < pos; i++)
	 if (s[i] == -1 && OutletForced(AA, posout[i].T, posout[i].x)) {
	    if (print >= PRTPAI) {
	       Indent(depth, "Positioned outlet ");
	       (void) printf("%d,%d can't be forced, because it forces %d,%d\n", PO->T->number, x, posout[i].T->number, posout[i].x);
	    }
	    good = 0;
	    break;
	 }
      if (good) {
	 /* recursion with PO forced */
	 for (i = 0; (sprime[i] = s[i]) < 99; ++i)	/* do nothing */
	    ;
	 sprime[pos] = 1;
	 if (print >= PRTPAI) {
	    Indent(depth, "Starting recursion with ");
	    (void) printf("%d,%d forced\n", PO->T->number, x);
	 }
	 CheckBound(AA, posout, sprime, maxch, pos + 1, depth + 1, lineno, print);
      }
      /* rejecting positioned outlet PO */
      if (print >= PRTPAI) {
	 Indent(depth, "Rejecting positioned outlet ");
	 (void) printf("%d,%d. ", PO->T->number, x);
      }
      s[pos] = -1;
      allowedch -= PO->T->value;
      if (allowedch + forcedch <= maxch) {
	 if (print >= PRTPAI)
	    (void) printf("Inequality holds.\n");
	 free(sprime);
	 free(AA);
	 return;
      } else if (print >= PRTPAI)
	 (void) printf("\n");
   }	/* pos */
   Error("Unexpected error 101", lineno);
}/* CheckBound */


/*********************************************************************
            OutletForced
If (T,x) is enforced by A, then returns the value of T, otherwise 0
*********************************************************************/
int
OutletForced(A, T, x)
int x;
tp_outlet *T;
tp_axle *A;
{
   int i, p, deg;

   deg = A->low[0];
   x--;
   for (i = 0; i < T->nolines; ++i) {
      p = T->pos[i];
      p = x + (p - 1) % deg < deg ? p + x : p + x - deg;
      if (T->low[i] > A->low[p] || T->upp[i] < A->upp[p])
	 return (0);
   }
   return (T->value);
}/* OutletForced */

/*********************************************************************
            OutletPermitted
If (T,x) is permitted by A, then returns the value of T, otherwise 0
*********************************************************************/
int
OutletPermitted(A, T, x)
int x;
tp_outlet *T;
tp_axle *A;
{
   int deg, i, p;

   deg = A->low[0];
   x--;
   for (i = 0; i < T->nolines; ++i) {
      p = T->pos[i];
      p = x + (p - 1) % deg < deg ? p + x : p + x - deg;
      if (T->low[i] > A->upp[p] || T->upp[i] < A->low[p])
	 return (0);
   }	/* i */
   return (T->value);
}/* OutletPermitted */

/************************************************************************
            ReflForced
Returns the value of T if M is fan-free and every cartwheel compatible
with A is compatible with tau^(x-1)sigma M, where M is the axle
corresponding to T
************************************************************************/
int
ReflForced(A, T, x)
int x;
tp_outlet *T;
tp_axle *A;
{
   int deg, i, p, q;

   deg = A->low[0];
   x--;
   for (i = 0; i < T->nolines; ++i) {
      p = T->pos[i];
      p = x + (p - 1) % deg < deg ? p + x : p + x - deg;
      if (p < 1 || p > 2 * deg)
	 return (0);
      else if (p <= deg)
	 q = deg - p + 1;
      else if (p < 2 * deg)
	 q = 3 * deg - p;
      else
	 q = 2 * deg;
      if (T->low[i] > A->low[q] || T->upp[i] < A->upp[q])
	 return (0);
   }
   return (T->value);
}/* ReflForced */


/*********************************************************************
            PrintOutlet
File F must be open for writing. Prints T into F.
*********************************************************************/
void
PrintOutlet(n, F, T)
int n;
FILE *F;
tp_outlet *T;
{
   int i;

   (void) fprintf(F, "%d  %d              %d\n", n, T->value, T->number);
   for (i = 0; i < T->nolines; ++i)
      (void) fprintf(F, "%2d  %2d  %2d\n", T->pos[i], T->low[i], T->upp[i]);
   (void) fprintf(F, "\n");
   fflush(F);
   return;
}/* PrintOutlet */


/*********************************************************************
            Reduce
 If A==NULL it initializes by allocating memory and reading reducible
 configurations from the file specified by UNAVSET, and computing
 "redquestions" (i.e. questions corresponding to the unavoidable set)
 If A!=NULL it tests reducibility of A as described in [D]
*********************************************************************/
Reduce(A, lineno, print)
int lineno, print;
tp_axle *A;
{
   int h, i, j, v, redring, redverts;
   static int naxles, noconf;
   static tp_confmat *conf;
   static tp_edgelist edgelist;
   static tp_adjmat adjmat;
   static tp_vertices image;
   static tp_axle **Astack, *B;
   static tp_question *redquestions;

   if (A == NULL) {
      ALLOC(Astack, MAXASTACK, tp_axle *);
      for (i = 0; i < MAXASTACK; i++)
	 ALLOC(Astack[i], 1, tp_axle);
      ALLOC(B, 1, tp_axle);
      redquestions = (tp_question *) malloc(CONFS * sizeof(tp_question));
      if (redquestions == NULL) {
	 fflush(stdout);
	 (void) fprintf(stderr, "Insufficient memory. Additional %d KBytes needed\n", (int) CONFS * sizeof(tp_question) / 1024);
	 exit(27);
      }
      conf = (tp_confmat *) malloc(CONFS * sizeof(tp_confmat));
      if (conf == NULL) {
	 (void) printf("Not enough memory to store unavoidable set. Additional %d KBytes needed.\n", (int) CONFS * sizeof(tp_confmat) / 1024);
	 (void) printf("Therefore cannot do isomorphism verification.\n");
	 fflush(stdout);
      }
      noconf = GetConf(conf, redquestions);
      return (0);
   }
   /* This part is executed when A!=NULL */
   if (print)
      (void) printf("Testing reducibility. Putting input axle on stack.\n");
   CopyAxle(Astack[0], A);
   for (naxles = 1; naxles > 0;) {
      CopyAxle(B, Astack[--naxles]);
      if (print) {
	 (void) printf("Axle from stack:");
	 PrintAxle(B);
      }
      Getadjmat(B, adjmat);
      GetEdgelist(B, edgelist);
      for (h = 0; h < noconf; ++h)
	 if (SubConf(adjmat, B->upp, redquestions[h], edgelist, image))
	    break;
      if (h == noconf) {
	 if (print)
	    (void) printf("Not reducible\n");
	 return (0);
      }
      /* Semi-reducibility test found h-th configuration, say K, appearing */
      redverts = redquestions[h][1].u;
      redring = redquestions[h][1].v;
      /* the above are no vertices and ring-size of free completion of K */
      /* could not use conf[h][0][0], because conf may be NULL           */

      if (print) {
	 (void) printf("Conf(%d,%d,%d): ", h / 70 + 1, (h % 70) / 7 + 1, h % 7 + 1);
	 for (j = 1; j <= redverts; j++) {
	    if (image[j] != -1)
	       (void) printf(" %d(%d)", image[j], j);
	 }
	 (void) printf("\n");
      }
      if (conf != NULL)
	 CheckIso(conf[h], B, image, lineno);
      /* Double-check isomorphism */

      for (i = redring + 1; i <= redverts; i++) {
	 v = image[i];
	 if (B->low[v] == B->upp[v])
	    continue;
	 if (print) {
	    (void) printf("Lowering upper bound of vertex ");
	    (void) printf("%d to %d and adding to stack\n", v, B->upp[v] - 1);
	 }
	 if (naxles >= MAXASTACK) {
	    fflush(stdout);
	    (void) fprintf(stderr, "More than %d elements in axle stack needed\n", MAXASTACK);
	    exit(42);
	 }
	 CopyAxle(Astack[naxles], B);
	 Astack[naxles]->upp[v] = B->upp[v] - 1;
	 naxles++;
      }

   }
   if (print)
      (void) printf("All possibilities for lower degrees tested\n");
   return (1);
}/* Reduce */

/*********************************************************************
            CheckIso
Verifies that image is an isomorphism between L and a well-positioned
induced subconfiguration K of the skeleton of A
*********************************************************************/
void
CheckIso(L, A, image, lineno)
tp_confmat L;
tp_axle *A;
tp_vertices image;
int lineno;

{
   int i, u, v, w, x, y, fu, deg, worried, verts, ring, d, h, a, b, c,
    e;
   static tp_vertices used;
   static tp_adjmat X, adjmat;

   deg = A->low[0];
   verts = L[0][0];	/* no verts of free completion of L */
   ring = L[0][1];	/* ring-size of L */
   Getadjmat(A, adjmat);
   for (u = 0; u <= 5 * deg; u++)
      for (v = 0; v <= 5 * deg; v++)
	 X[u][v] = 0;	/* Adjacency matrix of image */
   for (fu = 0; fu <= 5 * deg; fu++)
      used[fu] = 0;	/* to mark vertices that are in the image */

   /* first check that image is a valid 1-1 map */
   for (u = ring + 1; u <= verts; u++) {
      fu = image[u];
      if (fu < 0 || fu > 5 * deg || used[fu])
	 Error("Isomorphism error 1", lineno);
      used[fu] = 1;
      if (L[u][0] != A->upp[fu])
	 Error("Isomorphism error 2", lineno);
      if (fu > 2 * deg) {
	 i = (fu - 1) % deg + 1;
	 if (A->low[i] != A->upp[i] || A->low[i] < (fu - 1) / deg + 4)
	    Error("Isomorphism error 3", lineno);
      }
   }

   /* check that image is well-positioned */
   for (i = 1; i <= deg; i++)
      if (!used[i] && used[deg + i] && used[(i == 1) ? 2 * deg : deg + i - 1])
	 Error("Isomorphism error 4", lineno);

   /* test that image of L is a subconfiguration */
   for (u = ring + 1; u <= verts; u++) {
      d = L[u][0];
      worried = L[u][d] > ring ? 0 : 1;
      /* We are only checking edges that belong to triangles */
      /* worried is used to check that every edge belongs to a triangle */
      for (i = 1; i <= L[u][0]; i++) {
	 /* worried==1 iff L[u][i-1]<=ring */
	 v = L[u][i];
	 if (v <= ring) {
	    worried = 1;
	    continue;
	 }
	 if (image[0]) {	/* isomorphism is orientation-preserving */
	    x = image[u];
	    y = image[v];
	 } else {	/* isomorphism is orientation-reversing */
	    x = image[v];
	    y = image[u];
	 }
	 X[x][y] = 1;
	 w = L[u][i < d ? i + 1 : 1];
	 if (w <= ring) {
	    if (worried)
	       Error("Isomorphism error 5", lineno);
	    continue;
	 }
	 worried = 0;
	 if (adjmat[x][y] != image[w])
	    Error("Isomorphism error 6", lineno);
      }
   }

   /* test that the image of L is induced */
#define INDUCHECK(aa, bb, cc) if(aa && bb && cc!=1)      \
        Error("Isomorphism not induced",lineno);
   for (i = 1; i <= deg; i++) {
      INDUCHECK(used[0], used[i], X[0][i]);
      h = i == 1 ? deg : i - 1;
      INDUCHECK(used[h], used[i], X[h][i]);
      a = h + deg;
      INDUCHECK(used[h], used[a], X[h][a]);
      INDUCHECK(used[i], used[a], X[i][a]);
      if (A->low[i] != A->upp[i])
	 continue;
      b = deg + i;
      if (A->low[i] == 5) {
	 INDUCHECK(used[a], used[b], X[a][b]);
	 continue;
      }
      c = 2 * deg + i;
      INDUCHECK(used[a], used[c], X[a][c]);
      INDUCHECK(used[c], used[i], X[c][i]);
      if (A->low[i] == 6) {
	 INDUCHECK(used[c], used[b], X[c][b]);
	 continue;
      }
      d = 3 * deg + i;
      INDUCHECK(used[c], used[d], X[c][d]);
      INDUCHECK(used[d], used[i], X[d][i]);
      if (A->low[i] == 7) {
	 INDUCHECK(used[d], used[b], X[d][b]);
	 continue;
      }
      e = 4 * deg + i;
      if (A->low[i] != 8)
	 Error("Unexpected error in CheckIso", lineno);
      INDUCHECK(used[e], used[d], X[e][d]);
      INDUCHECK(used[e], used[i], X[e][i]);
      INDUCHECK(used[e], used[b], X[e][b]);
   }
}/* CheckIso */


/*********************************************************************
            CopyAxle
Copies B into A.
*********************************************************************/
void
CopyAxle(A, B)
tp_axle *A, *B;

{
   int j, deg5;

   deg5 = 5 * B->upp[0];
   for (j = 0; j <= deg5; j++) {
      A->low[j] = B->low[j];
      A->upp[j] = B->upp[j];
   }
   return;
}/* CopyAxle */

/*********************************************************************
            PrintAxle
Prints A on one line of stdout, followed by EOL
*********************************************************************/
void
PrintAxle(A)
tp_axle *A;

{
   int i, deg;

   deg = A->upp[0];
   for (i = 1; i <= 5 * deg; ++i) {
      if (A->low[i] == 5 && A->upp[i] == INFTY)
	 continue;
      (void) printf(" %d:%d", i, A->low[i]);
      if (A->low[i] != A->upp[i])
	 if (A->upp[i] == INFTY)
	    (void) printf("+");
	 else
	    (void) printf("%d", A->upp[i]);
      (void) printf(" ");
   }	/* i */
   (void) printf("\n");
   return;
}/* PrintAxle */


/*********************************************************************
            Indent
Prints string s on stdout, indented by 2n positions.
*********************************************************************/
void
Indent(n, s)
int n;
char s[];

{
   int i;

   for (i = 1; i <= n; ++i)
      (void) printf("  ");
   (void) printf("%s", s);
}/* Indent */


/*********************************************************************
	Getadjmat
Computes adjmat defined as follows. Let G=G(L), where L is the
skeleton of A. Notice that G only depends on u_B(i) for i=0,1,..,deg.
Then adjmat[u][v]=w if u,v,w form a clockwise triangle in G, and
adjmat[u][v]=-1 if w does not exist.
*********************************************************************/
void
Getadjmat(A, adjmat)
tp_axle *A;
tp_adjmat adjmat;

{
   int deg, a, b, h, i;

   deg = A->low[0];
   for (a = 0; a < CARTVERT; a++)
      for (b = 0; b < CARTVERT; b++)
	 adjmat[a][b] = -1;
   for (i = 1; i <= deg; i++) {
      h = (i == 1) ? deg : i - 1;
      adjmat[0][h] = i;
      adjmat[i][0] = h;
      adjmat[h][i] = 0;
      a = deg + h;
      adjmat[i][h] = a;
      adjmat[a][i] = h;
      adjmat[h][a] = i;
      if (A->upp[i] < 9)
	 DoFan(deg, i, A->upp[i], adjmat);
   }
}/* Getadjmat */

/*********************************************************************
	DoFan
Does one fan of adjmat
*********************************************************************/

void
DoFan(deg, i, k, adjmat)
int deg, i, k;
tp_adjmat adjmat;
{
   int a, b, c, d, e;

   a = i == 1 ? 2 * deg : deg + i - 1;
   b = deg + i;
   if (k == 5) {
      adjmat[i][a] = b;
      adjmat[a][b] = i;
      adjmat[b][i] = a;
      return;
   }
   c = 2 * deg + i;
   adjmat[i][a] = c;
   adjmat[a][c] = i;
   adjmat[c][i] = a;
   if (k == 6) {
      adjmat[i][c] = b;
      adjmat[c][b] = i;
      adjmat[b][i] = c;
      return;
   }
   d = 3 * deg + i;
   adjmat[i][c] = d;
   adjmat[c][d] = i;
   adjmat[d][i] = c;
   if (k == 7) {
      adjmat[i][d] = b;
      adjmat[d][b] = i;
      adjmat[b][i] = d;
      return;
   }
   e = 4 * deg + i;
   adjmat[i][d] = e;
   adjmat[d][e] = i;
   adjmat[e][i] = d;
   adjmat[i][e] = b;
   adjmat[e][b] = i;
   adjmat[b][i] = e;
}/* DoFan */


/***********************************************************************
            Radius
Prints an error message and exits if L does not have radius at most two.
************************************************************************/
void
Radius(L)
tp_confmat L;
{
   int i, j, u, v, verts, ring;
   static tp_vertices reached;

   verts = L[0][0];
   ring = L[0][1];
   for (u = ring + 1; u <= verts; u++) {
      /* u is a candidate for a center */
      for (v = ring + 1; v <= verts; v++)
	 reached[v] = 0;
      reached[u] = 1;
      for (i = 1; i <= L[u][0]; i++) {
	 v = L[u][i];
	 reached[v] = 1;
	 if (v > ring)
	    for (j = 1; j <= L[v][0]; j++)
	       reached[L[v][j]] = 1;
      }
      for (v = ring + 1; v <= verts; v++)
	 if (!reached[v])
	    break;
      if (v == verts + 1)
	 return;
   }
   fflush(stdout);
   (void) fprintf(stderr, "A configuration does not have radius at most two\n");
   exit(38);
}/* Radius */


/*********************************************************************
            GetConf
Reads unavoidable set from the file called UNAVSET. For the i-th member
(i=0,1,...), say L, it verifies that L has radius at most two, computes
a question for L and stores it in redquestions[i], and if conf!=NULL it
stores L in conf[i].
**********************************************************************/
int
GetConf(conf, redquestions)
tp_confmat *conf;
tp_question *redquestions;

{
   int noconf, nonull;
   tp_confmat *A;
   FILE *F;

   noconf = 0;
   if (conf == NULL) {
      ALLOC(conf, 1, tp_confmat);
      nonull = 0;
   } else
      nonull = 1;
   F = fopen(UNAVSET, "r");
   if (F == NULL) {
      fflush(stdout);
      (void) fprintf(stderr, "Unable to open file %s for reading\n", UNAVSET);
      exit(23);
   }
   (void) printf("Reading unavoidable set from file `%s'.\n", UNAVSET);
   fflush(stdout);
   for (noconf = 0; !ReadConf(*conf, F, NULL); noconf++) {
      if (noconf >= CONFS) {
	 fflush(stdout);
	 (void) fprintf(stderr, "More than %d configurations\n", CONFS);
	 exit(24);
      }
      GetQuestion(*conf, redquestions[noconf]);
      Radius(*conf);
      if (nonull)
	 conf++;
   }
   if (!nonull)
      free(conf);
   (void) printf("Total of %d configurations.\n", noconf);
   fflush(stdout);
   (void) fclose(F);
   return (noconf);
}/* GetConf */


/************************************************************************
            ReadConf
Reads one configuration matrix from file F and stores in A, if C!=NULL
puts coordinates there. If successful returns 0, on end of file returns 1,
if error exits. F must be open for reading. If K is the configuration,
and G its free completion, then A[0][0]=|V(G)|, A[0][1]=ring-size of K,
A[i][0]=d_G(i) for all i, and A[i][0]=d_G(i) =gamma_K(i) for i>ring-size,
A[i][j] (j=1,2,...,L[i][0]) are the neighbors of i in G listed in clockwise
order. See `Reducibility in the Four-Color Theorem' for more details.
*************************************************************************/
long
ReadConf(A, F, C)
tp_confmat A;
FILE *F;
long *C;

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


/**********************************************************************
	ReadErr
Prints an error message and exits
***********************************************************************/
void
ReadErr(n, name)
int n;
char name[];
{
   (void) printf("Error %d while reading configuration %s\n", n, name);
   exit(57);
}

/**********************************************************************
The remaining functions in this file do not need verification, because
the results they return are independently verified (assuming enough
memory is available)
***********************************************************************/

/************************************************************************
            ReadOutlets
Assumes that A is the trivial axle of degree deg, where deg=A->low[0].
Reads rules, computes corresponding axles of degree deg and stores
them in outlet[0],...,outlet[nouts-1]. Returns nouts (i.e. the number
of outlets constructed. The array outlet must be already allocated and
of size >=MAXOUTLET.
*************************************************************************/
int
ReadOutlets(A, outlet)
tp_axle *A;
tp_outlet outlet[];
{
   char line[512], *ch, s[64];
   int lineno, n, nouts, number, i, norules;
   int z[17], b[17];	/* input data */
   tp_outlet *T;
   FILE *F;
   static int U[] = {0, 0, 0, 1, 0, 3, 2, 1, 4, 3, 8, 3, 0, 0, 5, 6, 15};
   static int V[] = {0, 0, 1, 0, 2, 0, 1, 3, 2, 5, 2, 9, 4, 12, 0, 1, 1};

   /* See the last paragraph of [D, Section 2]. */

   F = fopen(RULEFILE, "r");
   if (F == NULL) {
      (void) fflush(stdout);
      (void) fprintf(stderr, "Unable to open file %s for reading\n", RULEFILE);
      exit(405);
   }
   (void) printf("Reading rules from file `%s'.\n", RULEFILE);
   (void) fflush(stdout);
   n = -1;	/* size of M(T) or -1 if there is no T */
   T = outlet;
   norules = 0;
   for (nouts = 0, lineno = 1; fgets(line, sizeof(line), F) != NULL; lineno++) {
      for (ch = line; *ch == ' ' || *ch == '\t'; ++ch);
      if (*ch == '#' || *ch == '\\' || *ch == '\n' || *ch == '\0')
	 continue;
      /* starting to read a new rule */
      norules++;
      if (sscanf(line, "%d%s", &number, s) != 2)
	 Error("Unable to read first line of rule", lineno);
      if (number == 0)
	 Error("Rule has number zero", lineno);
      if (*s == 'i') {
	 if (n < 0)
	    Error("Illegal rule reference", lineno);
	 /* invert previous rule */
	 if (nouts >= MAXOUTLETS - 2)
	    Error("Too many outlets", lineno);
	 if (DoOutlet(A, number, V, U, z, b, T, lineno)) {
	    nouts++;
	    T++;
	 }
	 if (DoOutlet(A, -number, V, U, z, b, T, lineno)) {
	    nouts++;
	    T++;
	 }
      } else {
	 if (sscanf(line, "%*d%d%d", &b[0], &b[1]) != 2)
	    Error("Unable to read source or sink", lineno);
	 if (fgets(line, sizeof(line), F) == NULL)
	    Error("Unexpected end of rule file", lineno);
	 ++lineno;
	 for (ch = line; *ch == ' ' || *ch == '\t'; ++ch);
	 for (n = 2; *ch != '\0' && *ch != '\n'; n++) {
	    if (n > 16)
	       Error("Too many vertices in a rule", lineno);
	    if (sscanf(ch, "%d%d", z + n, b + n) != 2)
	       Error("Syntax error in rule file", lineno);
	    if (z[n] < 0 || z[n] > 16)
	       Error("Illegal entry in rule file", lineno);
	    for (i = 0; i < 2; i++) {
	       for (; *ch >= '0' && *ch <= '9'; ch++);
	       for (; *ch == ' ' || *ch == '\t'; ch++);
	    }
	 }
	 z[0] = n;
	 /* completed reading rule */
	 if (nouts >= MAXOUTLETS - 2)
	    Error("Too many outlets", lineno);
	 if (DoOutlet(A, number, U, V, z, b, T, lineno)) {
	    nouts++;
	    T++;
	 }
	 if (DoOutlet(A, -number, U, V, z, b, T, lineno)) {
	    nouts++;
	    T++;
	 }
      }
   }
   (void) printf("Total of %d rules resulted in %d outlets of degree %d.\n", norules, nouts, A->low[0]);
   (void) fflush(stdout);
   (void) fclose(F);
   return (nouts);
}/* ReadOutlets */


/*********************************************************************
            DoOutlet
Creates one outlet T from input data. The sign of "number" determines
whether r(T)=1 or r(T)=-1. The order of arguments X, Y determines sense
(clockwise/counterclockwise).
*********************************************************************/
int
DoOutlet(A, number, X, Y, z, b, T, lineno)
tp_axle *A;
int number, X[], Y[], z[], b[], lineno;
tp_outlet *T;
{
   int i, j, k, phi[17], u, v, deg;
   static tp_adjmat adjmat;

   Getadjmat(A, adjmat);
   deg = A->low[0];
   T->nolines = z[0] - 1;
   T->number = number;
   for (i = 0; i < 17; i++)
      phi[i] = -1;
   if (number > 0) {
      phi[0] = 1;
      phi[1] = 0;
      T->value = 1;
      k = 1;
   } else {
      phi[0] = 0;
      phi[1] = 1;
      T->value = -1;
      k = 0;
   }
   T->pos[0] = 1;

   /* compute phi */
   for (i = j = 0; j < z[0]; i++, j++) {
      T->low[i] = b[j] / 10;
      T->upp[i] = b[j] % 10;
      if (T->upp[i] == 9)
	 T->upp[i] = INFTY;
      if (T->low[i] == 0)
	 T->low[i] = T->upp[i];
      /* checking (T2) */
      if (T->low[i] > T->upp[i])
	 Error("Condition (T2) from def of outlet violated", lineno);
      /* checking (T3) */
      if (T->low[i] < 5 || T->low[i] > 9 || T->upp[i] > INFTY || T->upp[i] == 9)
	 Error("Condition (T3) from def of outlet violated", lineno);
      if (j == k) {
	 if (T->low[k] > deg || T->upp[k] < deg)
	    return (0);
	 /* if above true then outlet cannot apply for this degree */
	 i--;
	 continue;
      }
      if (j >= 2) {	/* now computing T->pos[i] */
	 u = phi[X[z[j]]];
	 v = phi[Y[z[j]]];
	 if (u < 0 || u > 5 * deg || v < 0 || v > 5 * deg)
	    Error("Rule references illegal vertex", lineno);
	 T->pos[i] = phi[z[j]] = adjmat[u][v];
      }
      u = T->pos[i];
      if (u <= 0 || u > 5 * deg)
	 Error("Rule uses illegal vertex", lineno);
      if (u <= deg && T->low[i] == T->upp[i])
	 DoFan(deg, u, T->low[i], adjmat);	/* update adjmat */
   }
   /* Condition (T4) is checked in CheckIso */
   return (1);
}/* DoOutlet */


/*********************************************************************
            GetQuestion
Computes a question Q=(Q[0],Q[1],...,Q[n]) for L. Moreover, sets
Q[1].u to be the number of vertices of the free completion of L,
and Q[1].v to be the ring-size of L. Also sets Q[n+1].u=-1 to
indicate end
*********************************************************************/
void
GetQuestion(L, Q)
tp_confmat L;
tp_question Q;

{
   int nverts, max, ring, found[VERTS];
   int d, g, h, i, j, r, t, u, v, w, best, secondbest, nfound, search;

   nverts = Q[1].u = L[0][0];
   ring = Q[1].v = L[0][1];
   for (v = 0; v <= nverts; v++)
      found[v] = 0;
   for (max = 0, v = ring + 1; v <= nverts; v++) {
      if (L[v][0] > max) {
	 max = L[v][0];
	 best = v;
      }
   }
   Q[0].z = best;
   Q[0].xi = L[best][0];
   found[best] = 1;
   for (max = 0, i = 1; i <= L[best][0]; i++) {
      v = L[best][i];
      if (v <= ring)
	 continue;
      if (L[v][0] > max) {
	 max = L[v][0];
	 secondbest = v;
      }
   }
   Q[1].z = secondbest;
   Q[1].xi = L[secondbest][0];
   found[secondbest] = 1;
   nfound = 2;
   for (search = 0; search < nfound; search++) {
      v = Q[search].z;
      if (v <= ring)
	 continue;
      d = L[v][0];
      for (i = 1; !found[L[v][i]]; i++);
      for (h = (i == 1) ? d : i - 1; h != i; h = (h == 1) ? d : h - 1) {
	 u = L[v][h];
	 if (u <= ring)
	    break;
	 if (found[u])
	    continue;
	 Q[nfound].z = u;
	 Q[nfound].xi = u > ring ? L[u][0] : 0;
	 Q[nfound].u = L[v][(h == d) ? 1 : h + 1];
	 Q[nfound].v = v;
	 nfound++;
	 found[u] = 1;
      }
      if (h == i)
	 continue;
      for (j = (i == d) ? 1 : i + 1;; j = (j == d) ? 1 : j + 1) {
	 w = L[v][j];
	 if (w <= ring)
	    break;
	 if (found[w])
	    continue;
	 Q[nfound].z = w;
	 Q[nfound].xi = w > ring ? L[w][0] : 0;
	 Q[nfound].u = v;
	 Q[nfound].v = L[v][(j == 1) ? d : j - 1];
	 nfound++;
	 found[w] = 1;
      }
      r = (h >= j) ? h - j : h - j + d;
      if (r <= 2)
	 continue;
      Q[nfound].z = u;
      Q[nfound].xi = u > ring ? L[u][0] : 0;
      Q[nfound].u = L[v][(h == d) ? 1 : h + 1];
      Q[nfound].v = v;
      nfound++;
      for (g = (h == 1) ? d : h - 1; g != j; g = (g == 1) ? d : g - 1) {
	 t = L[v][g];
	 if ((t <= ring) || (found[t])) {
	    (void) printf("Error in getquestions\n");
	    exit(1);
	 }
	 Q[nfound].z = t;
	 Q[nfound].xi = t > ring ? L[t][0] : 0;
	 Q[nfound].u = Q[nfound - 1].z;
	 Q[nfound].v = v;
	 nfound++;
	 found[t] = 1;
      }
   }
   Q[nfound].u = -1;	/* indicates end */
}/* GetQuestion */

/**********************************************************************
	GetEdgeList
For (a,b) such that a >= b, b <= 8 and a <= 11 computes X=edgelist[a][b]
defined as follows: X[2*i+1],X[2*i+2] (i=0,1,...,X[0]-1) are all pairs of
adjacent vertices u,v of the skeleton of A with degrees a,b, respectively
such that either a<=8 or u=0.
***********************************************************************/
void
GetEdgelist(A, edgelist)
tp_axle *A;
tp_edgelist edgelist;


{
   int a, b, c, d, e, h, i, deg;

   deg = A->upp[0];
   for (a = 5; a <= 11; a++)
      for (b = 5; b <= 8 && b <= a; b++)
	 edgelist[a][b][0] = 0;
   for (i = 1; i <= deg; i++) {
      AddToList(edgelist, 0, i, A->upp);
      h = (i == 1) ? deg : i - 1;
      AddToList(edgelist, i, h, A->upp);
      a = deg + h;
      b = deg + i;
      AddToList(edgelist, i, a, A->upp);
      AddToList(edgelist, i, b, A->upp);
      if (A->low[i] != A->upp[i])
	 continue;
      /* in this case we are not interested in the fan edges */
      if (A->upp[i] == 5) {
	 AddToList(edgelist, a, b, A->upp);
	 continue;
      }
      c = 2 * deg + i;
      AddToList(edgelist, a, c, A->upp);
      AddToList(edgelist, i, c, A->upp);
      if (A->upp[i] == 6) {
	 AddToList(edgelist, b, c, A->upp);
	 continue;
      }
      d = 3 * deg + i;
      AddToList(edgelist, c, d, A->upp);
      AddToList(edgelist, i, d, A->upp);
      if (A->upp[i] == 7) {
	 AddToList(edgelist, b, d, A->upp);
	 continue;
      }
      if (A->upp[i] != 8) {
	 (void) fflush(stdout);
	 (void) fprintf(stderr, "Unexpected error in `GetEdgeList'\n");
	 exit(36);
      }
      e = 4 * deg + i;
      AddToList(edgelist, d, e, A->upp);
      AddToList(edgelist, i, e, A->upp);
      AddToList(edgelist, b, e, A->upp);
   }
}/* GetEdgeList */


/**********************************************************************
	AddToList
See "GetEdgeList" above.
***********************************************************************/
void
AddToList(edgelist, u, v, degree)
tp_edgelist edgelist;
int u, v;
tp_vertices degree;

/* adds the pair u,v to edgelist */
{
   int a, b, *e;

   a = degree[u];
   b = degree[v];
   if ((a >= b) && (b <= 8) && (a <= 11) && ((a <= 8) || (u == 0))) {
      e = edgelist[a][b];
      if (e[0] + 2 >= MAXELIST) {
	 (void) fflush(stdout);
	 (void) fprintf(stderr, "More than %d entries in edgelist needed\n", MAXELIST);
	 exit(39);
      }
      e[++e[0]] = u;
      e[++e[0]] = v;
   }
   if ((b >= a) && (a <= 8) && (b <= 11) && ((b <= 8) || (v == 0))) {
      e = edgelist[b][a];
      if (e[0] + 2 >= MAXELIST) {
	 (void) fflush(stdout);
	 (void) (stderr, "More than %d entries in edgelist needed\n", MAXELIST);
	 exit(41);
      }
      e[++e[0]] = v;
      e[++e[0]] = u;
   }
}

/**********************************************************************
	RootedSubConf
See "SubConf" below.
***********************************************************************/
RootedSubConf(degree, adjmat, question, image, x, y, clockwise)
int degree[], x, y, clockwise;
tp_adjmat adjmat;
tp_vertices image;
tp_question question;

{
   int deg, j, w;
   static int used[CARTVERT];
   tp_query *Q;

   deg = degree[0];
   for (j = 0; j < CARTVERT; j++) {
      used[j] = 0;
      image[j] = -1;
   }
   image[0] = clockwise;
   image[question[0].z] = x;
   image[question[1].z] = y;
   used[x] = 1;
   used[y] = 1;
   for (Q = question + 2; Q->u >= 0; Q++) {
      if (clockwise)
	 w = adjmat[image[Q->u]][image[Q->v]];
      else
	 w = adjmat[image[Q->v]][image[Q->u]];
      if (w == -1)
	 return (0);
      if (Q->xi && Q->xi != degree[w])
	 return (0);
      if (used[w])
	 return (0);
      image[Q->z] = w;
      used[w] = 1;
   }

   /* test if image is well-positioned */
   for (j = 1; j <= deg; j++)
      if (!used[j] && used[deg + j] && used[(j == 1) ? 2 * deg : deg + j - 1])
	 return (0);
   return (1);
}/* RootedSubConf */

/**********************************************************************
	SubConf
Given "adjmat", "degree" and "edgelist" derived from an axle A, and
"question" for a configuration L it tests using [D, theorem (6.3)]
if L is a well-positioned induced subconfiguration of the skeleton
of A. If not returns 0; otherwise returns 1, writes an isomorphism
into image, and sets image[0] to 1 if the isomorphism is orientation-
preserving, and 0 if it is orientation-reversing.
***********************************************************************/
SubConf(adjmat, degree, question, edgelist, image)
tp_adjmat adjmat;
tp_vertices degree;
tp_edgelist edgelist;
tp_vertices image;
tp_question question;

{
   int i, x, y, *pedge;

   pedge = edgelist[question[0].xi][question[1].xi];
   for (i = 1; i <= pedge[0]; i++) {
      x = pedge[i++];
      y = pedge[i];
      if (RootedSubConf(degree, adjmat, question, image, x, y, 1) ||
	  RootedSubConf(degree, adjmat, question, image, x, y, 0))
	 return (1);
   }
   return (0);
}/* SubConf */


/* End of file discharge.c */
