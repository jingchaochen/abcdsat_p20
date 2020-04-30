
#include "parallel/LocalThread.h"
#include "mtl/Sort.h"

using namespace abcdSAT;

const char* _parallel = "PARALLEL";

LocalThread::LocalThread(const LocalThread &s) : SimpSolver(s){
       nextUnit=nextBin=0;
}

LocalThread::~LocalThread() {
    printf("c Solver of thread %d ended.\n", thn);
    fflush(stdout);
}

void LocalThread::reportProgress() {
    printf("c | %2d | %6d | %10d | %10d | %8d | %6.3f |\n",(int)thn,(int)starts,(int)decisions,(int)conflicts,(int)learnts.size(),progressEstimate()*100);
}


bool LocalThread::panicModeIsEnabled() {  return sharedinfo->panicMode;}

bool LocalThread::OtherSolverFinished(){  return sharedinfo->jobFinished();}

void LocalThread::terminate_signal (lbool status)
{
    bool firstToFinish = false;
    if (status != l_Undef) firstToFinish = sharedinfo->IFinished(this);
    if (firstToFinish) {
        printf("c Thread %d is 100%% pure abcdSAT! First thread to terminate (%s answer).\n", threadNumber(), status == l_True ? "SAT" : status == l_False ? "UNSAT" : "UNKOWN");
        sharedinfo->jobStatus = status;
    }
    pthread_cond_signal(pcfinished);
}

void LocalThread::cloneSolver()
{
    copysolver  = (LocalThread*)clone();
    copysolver->verbosity = 0; 
   // s->setThreadNumber(tn);
    copysolver->sharedinfo   = sharedinfo;
    copysolver->parallel_pivot = lit_Undef;
   // pthread_cond_signal(pClonefinished);
}

void LocalThread::part_UNSAT_signal ()
{
    if(!parallelExportUnitClause(~parallel_pivot)) return terminate_signal(l_False);
    sharedinfo->putPartFinished(this);
}

bool LocalThread:: parallelExportUnitClause (Lit unitLit)
{ 
      return sharedinfo->addunit(unitLit);
}

void LocalThread :: parallelExportBinClause(Lit p, Lit q)
{
      sharedinfo->addbin(p,q);
}

Lit LocalThread:: getUnit ()
{
     return sharedinfo->getUnit(nextUnit);
}

void LocalThread:: getbin(Lit & p, Lit & q)
{
    sharedinfo->getbin(nextBin, p, q);
}


