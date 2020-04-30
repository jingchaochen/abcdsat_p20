
#ifndef LocalThread_H
#define	LocalThread_H

#include "core/SolverTypes.h"
#include "core/Solver.h"
#include "simp/SimpSolver.h"
#include "parallel/SharedInfo.h"

namespace abcdSAT {
    
class LocalThread : public SimpSolver {
    friend class MainThread;
    friend class SharedInfo;
protected :
    int		thn; // internal thread number(due to incomplete types)
    SharedInfo *sharedinfo;

    pthread_cond_t *pcfinished;  // condition variable that says that a thread as finished
    pthread_cond_t *pClonefinished;  

public:
    LocalThread* copysolver;
    LocalThread(){}
    LocalThread(const LocalThread &s);
    ~LocalThread();
    
    virtual Clone* clone() const { return  new LocalThread(*this); }   

    int  threadNumber  () const {return thn;}
    void setThreadNumber (int i) {thn = i;}
    void reportProgress();
    int nextUnit;
    int nextBin;
    virtual bool panicModeIsEnabled();
    virtual bool OtherSolverFinished();
    virtual void terminate_signal (lbool status);
    virtual void cloneSolver  ();
    virtual void part_UNSAT_signal ();
    virtual bool parallelExportUnitClause (Lit unitLit);
    virtual void parallelExportBinClause(Lit p, Lit q);
    virtual Lit getUnit();
    virtual void getbin(Lit & p, Lit & q);
};

}
#endif	// LocalThread_H 

