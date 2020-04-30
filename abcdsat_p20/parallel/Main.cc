
#include <errno.h>

#include <signal.h>
#include <zlib.h>


#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "utils/Options.h"
#include "core/Dimacs.h"
#include "core/SolverTypes.h"

#include "simp/SimpSolver.h"
#include "parallel/LocalThread.h"
#include "parallel/MainThread.h"

char* input_file    = NULL;

using namespace abcdSAT;

static MainThread* pmsolver;
static void SIGINT_exit(int signum) {
    printf("\n"); printf("*** INTERRUPTED ***\n");
    if (pmsolver->verbosity() > 0){
        pmsolver->printFinalStats();
        printf("\n"); printf("*** INTERRUPTED ***\n"); }
    _exit(1); 
}

void verifyModel(char* filename, vec<bool> & true_var)
{
    SimpSolver  S;
    gzFile in = gzopen(filename, "rb");
        if (in == NULL)
            printf("ERROR! Could not open file: %s\n", filename), exit(1);
           
// Parse CNF:
   printf("c final verify filename=%s \n",filename);
  
    parse_DIMACS(in, S);
    gzclose(in);
  
// Check satisfaction:
   vec<CRef>& cs = S.clauses;
  
   for (int i = 0; i < cs.size(); i++){
         Clause& c = S.ca[cs[i]];
        for (int j = 0; j < c.size(); j++){
              if (sign(c[j])==1 && true_var[var(c[j])]==false ) goto Satisfied;
              if (sign(c[j])==0 && true_var[var(c[j])]==true ) goto Satisfied;
        }
        printf("s INDETERMINATE\n");
        while(1){ i=1;}
        printf("{");
        for (int j = 0; j < c.size(); j++){
               if(sign(c[j])) printf("-");
               printf("%d:%d ", var(c[j])+1, true_var[var(c[j])]);
        }
        printf(" }\n");
        exit(0);

      Satisfied:;
    }
}

void init_rand_seed (); 

int main(int argc, char** argv)
{
   init_rand_seed ();
    double realTimeStart = realTime();
    printf("c\nc This is abcdSAT-parallel 2020 by Jingchao Chen \nc\n");
    try {
       setUsageHelp("c USAGE: %s [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n");
        
#if defined(__linux__)
        fpu_control_t oldcw, newcw;
        _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
        printf("c WARNING: for repeatability, setting FPU to use double precision\n");
#endif
        // Extra options:
        //
        IntOption    verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 1, IntRange(0, 2));
        IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", INT32_MAX, IntRange(0, INT32_MAX));
        IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", INT32_MAX, IntRange(0, INT32_MAX));
        
        input_file=argv[1];
        parseOptions(argc, argv, true);
        bool ShowModel=true;
	MainThread msolver;
        pmsolver = & msolver;
        msolver.setVerbosity(verb);
  
        double initial_time = cpuTime();
      // Use signal handlers that forcibly quit until the solver will be able to respond to interrupts
	signal(SIGINT, SIGINT_exit);
        signal(SIGXCPU,SIGINT_exit);

        // Set limit on CPU-time:
        if (cpu_lim != INT32_MAX){
            rlimit rl;
            getrlimit(RLIMIT_CPU, &rl);
            if (rl.rlim_max == RLIM_INFINITY || (rlim_t)cpu_lim < rl.rlim_max){
                rl.rlim_cur = cpu_lim;
                if (setrlimit(RLIMIT_CPU, &rl) == -1)
                    printf("c WARNING! Could not set resource limit: CPU-time.\n");
            } }

        // Set limit on virtual memory:
        if (mem_lim != INT32_MAX){
            rlim_t new_mem_lim = (rlim_t)mem_lim * 1024*1024;
            rlimit rl;
            getrlimit(RLIMIT_AS, &rl);
            if (rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max){
                rl.rlim_cur = new_mem_lim;
                if (setrlimit(RLIMIT_AS, &rl) == -1)
                    printf("c WARNING! Could not set resource limit: Virtual memory.\n");
            } }
        
        if (argc == 1) printf("c Reading from standard input... Use '--help' for help.\n");
        
        gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
        if (in == NULL)
            printf("c ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);
        
        parse_DIMACS(in, msolver);
        gzclose(in);

        FILE* res = (argc >= 3) ? fopen(argv[argc-1], "wb") : NULL;
        int org_nvars=msolver.nVars();
        if (msolver.verbosity() > 0){
            printf("c |  Number of variables:  %12d  |\n", msolver.nVars());
            printf("c |  Number of clauses:    %12d  |\n", msolver.nClauses()); }
        
        double parsed_time = cpuTime();
        if (msolver.verbosity() > 0){
            printf("c |  Parse time:   %12.2f s   |\n", parsed_time - initial_time);
        }
 
        int ret2 = msolver.simplify();    	
        double simplified_time = cpuTime();
        if (msolver.verbosity() > 0){
            printf("c |  Simplification time:  %12.2f s  |\n", simplified_time-parsed_time);
        }
        if (!ret2 || !msolver.okay()){
            if (res != NULL) fprintf(res, "UNSAT\n"), fclose(res);
            if (msolver.verbosity() > 0){
	        printf("c =========================================================================================================\n");
                printf("Solved by unit propagation\n"); 
		printf("c real time : %g s\n", realTime() - realTimeStart);
		printf("c cpu time  : %g s\n", cpuTime());
                printf("\n"); }
            printf("s UNSATISFIABLE\n");
            exit(20);
        }
        lbool ret = msolver.solve();
	
        printf("c real time : %g s\n", realTime() - realTimeStart);
	printf("c cpu time  : %g s\n", cpuTime());
        if (msolver.verbosity() > 0){
            msolver.printFinalStats();
            printf("\n"); 
        }

        if (ret==l_True){
           vec<bool>   VarValue(org_nvars, false);
           for (int i = 0; i < org_nvars; i++)
	      if (msolver.model[i] == l_True) VarValue[i]=true;
              else VarValue[i]=false;
            verifyModel(input_file, VarValue);
            printf("c OK! verified \n");
        }

	printf(ret == l_True ? "s SATISFIABLE\n" : ret == l_False ? "s UNSATISFIABLE\n" : "s INDETERMINATE\n");
	if(ShowModel && ret==l_True) {
	    printf("v ");
            for (int i = 0; i < org_nvars; i++)
	      if (msolver.model[i] != l_Undef)
		printf("%s%s%d", (i==0)?"":" ", (msolver.model[i]==l_True)?"":"-", i+1);
	    printf(" 0\n");
	}
#ifdef NDEBUG
        exit(ret == l_True ? 10 : ret == l_False ? 20 : 0);     
#else
        return (ret == l_True ? 10 : ret == l_False ? 20 : 0);
#endif
    } catch (OutOfMemoryException&){
      printf("c ===================================================================================================\n");
        printf("INDETERMINATE\n");
        exit(0);
    }
}
