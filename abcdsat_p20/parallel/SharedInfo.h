
/* This class is responsible for protecting (by mutex) information exchange between threads.
 * It also allows each solver to send / receive clause / unary clauses.
 *
 * Only one SharedInfo is created for all the solvers
 */


#ifndef SharedInfo_h
#define SharedInfo_h
#include "core/SolverTypes.h"
#include "parallel/LocalThread.h"

namespace abcdSAT {

class LocalThread;

class SharedInfo {
    friend class MainThread;
    friend class LocalThread;
public:
	SharedInfo(int nbThreads=0);
	void setNbThreads(int _nbThreads); // Sets the number of threads (cannot by changed once the solver is running)
	void newVar();            // Adds a var (used to keep track of unary variables)
	bool jobFinished();                // True if the job is over
	bool IFinished(LocalThread *s); // returns true if you are the first solver to finish//
        void putPartFinished(LocalThread *s);
        LocalThread * getPartFinished();
        int  NumPartjobFinished();

	bool addunit(Lit unary);    // Add a unary clause to share
        void addbin(Lit p, Lit q);  // Add a binary clause to share

	Lit getUnit(int & i);                              // Get a new unary literal
        void getbin(int & i, Lit & p, Lit & q);            // Get a new binary clause
	inline LocalThread* winner(){return jobFinishedBy;} // Gets the first solver that called IFinished()

 protected:
	int nbThreads;               // Number of threads
	pthread_mutex_t mutexSharedInfo; // mutex for any high level sync between all threads (like reportf)
	pthread_mutex_t mutexSharedUnitCls; // mutex for reading/writing unit clauses on the blackboard 
        pthread_mutex_t mutexJobFinished;
        pthread_mutex_t mutexPartJobFinished;

	bool bjobFinished;
	LocalThread *jobFinishedBy;
	vec <LocalThread *> PartjobFinished;
	bool panicMode;                        // panicMode means no more increasing space needed
	lbool jobStatus;                       // global status of the job

	vec<Lit> UnitcopiedMark; //init:lit_Undef  
	vec<Lit> unitLit;  // Set of unit literals found so far
	vec<Lit> binCls;  // Set of  binary clause found so far
  };
}
#endif
