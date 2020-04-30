
#ifndef MainThread_h
#define MainThread_h

#include "parallel/LocalThread.h"

namespace abcdSAT {
    
class MainThread {
 
public:
  MainThread();
  ~MainThread();
 
  void printFinalStats(); 

  int verb; 
  void setVerbosity(int i) {verb = i;}
  int verbosity()  {return verb;}
 
  void    newVar    (bool polarity = true, bool dvar = true); // Add a new variable 
  vec<Lit>  add_tmp;
  bool    addClause (const vec<Lit>& ps) { ps.copyTo(add_tmp); return addClause_(add_tmp); }
                       // Add a clause to the solver. NOTE! 'ps' may be shrunk by this method!
  bool    addClause_( vec<Lit>& ps);       
  bool    simplify     ();                        // Removes already satisfied clauses.
  int     nVars      ()      const   { return solvers[0]->nVars(); }    // The current number of variables.
 // int     originVars ()      const   { 
 //         return solvers[0]->originVars ? solvers[0]->originVars : solvers[0]->nVars(); }
  int     nClauses      ()   const   { return solvers[0]->nClauses(); }  // The current number of variables.
  lbool   solve        ();                        // Search without assumptions.
  vec<lbool> model;             // If problem is satisfiable, this vector contains the model (if any).
  inline bool okay() {
    if(!ok) return ok;
    for(int i = 0;i<solvers.size();i++) {
	if(!((SimpSolver*)solvers[i])->okay()) {
	    ok = false;
	    return false;
	}
    }
    return true;
  }

  void generateAllSolvers();
  void configureParameters(int tn);
  void adjustNumberOfCores();
  LocalThread * generateOneSolver(int threadNo);

 protected:
    friend class LocalThread;
	
    void printStats(); 
    int ok;
    int nbthreads; // Current number of threads
    unsigned int maxmemory;
    unsigned int maxnbsolvers;
   
    pthread_mutex_t m; // mutex for any high level sync between all threads )
    pthread_cond_t cfinished; // condition variable that says that a thread has finished
    pthread_cond_t Clonefinished;

    pthread_mutex_t mfinished; // mutex on which main process may wait for... 
                               //As soon as one process finishes it release the mutex
    vec <Lit> highLit;
    vec<LocalThread*> solvers; // set of plain solvers
    vec<pthread_t*> threads; // all threads of this process
};

}
#endif

