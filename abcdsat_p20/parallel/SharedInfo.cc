
#include "core/Solver.h"
#include "parallel/LocalThread.h"
#include "core/SolverTypes.h"
#include "parallel/SharedInfo.h"

using namespace abcdSAT;

extern double  random_seed;

SharedInfo::SharedInfo(int _nbThreads) :
    nbThreads(_nbThreads), 
    bjobFinished(false),
    jobFinishedBy(NULL),
    panicMode(false), // The bug in the SAT2014 competition :)
    jobStatus(l_Undef)
    {
        random_seed =9164825;
	pthread_mutex_init(&mutexSharedUnitCls,NULL); // This is the shared lock
	pthread_mutex_init(&mutexSharedInfo,NULL);  
	pthread_mutex_init(&mutexJobFinished,NULL); 
	pthread_mutex_init(&mutexPartJobFinished,NULL); 
	if (_nbThreads> 0)  {
	    setNbThreads(_nbThreads);
	    fprintf(stdout,"c Shared Info initialized: handling of clauses of %d threads\n", _nbThreads);
	}

}

void SharedInfo::setNbThreads(int _nbThreads) { nbThreads = _nbThreads;}

void SharedInfo::newVar() { UnitcopiedMark.push(lit_Undef);}

bool SharedInfo::addunit(Lit unary) 
{
  bool ret=true;
  int v=var(unary);
  pthread_mutex_lock(&mutexSharedUnitCls);
  if (UnitcopiedMark[v]==lit_Undef) {
      unitLit.push(unary);
      UnitcopiedMark[v] = unary;
  }
  else  ret= (UnitcopiedMark[v] == unary);
  pthread_mutex_unlock(&mutexSharedUnitCls);
  return ret;
}

void SharedInfo::addbin(Lit p, Lit q) 
{
  pthread_mutex_lock(&mutexSharedUnitCls);
  binCls.push(p);
  binCls.push(q);
  pthread_mutex_unlock(&mutexSharedUnitCls);
}

Lit SharedInfo::getUnit(int & i) {
  Lit ret = lit_Undef;
  pthread_mutex_lock(&mutexSharedUnitCls);
  if (i < unitLit.size()) ret = unitLit[i++];
  pthread_mutex_unlock(&mutexSharedUnitCls);
  return ret;
}

void SharedInfo::getbin(int & i, Lit & p, Lit & q) 
{
  pthread_mutex_lock(&mutexSharedUnitCls);
  if (i+1 < binCls.size()){
         p=binCls[i];
         q=binCls[i+1];
         i += 2;
  }      
  pthread_mutex_unlock(&mutexSharedUnitCls);
}

bool SharedInfo::jobFinished() {
    bool ret = false;
    pthread_mutex_lock(&mutexJobFinished);
    ret = bjobFinished;
    pthread_mutex_unlock(&mutexJobFinished);
    return ret;
}

bool SharedInfo::IFinished(LocalThread *s) {
    bool ret = false;
    pthread_mutex_lock(&mutexJobFinished);
    if (!bjobFinished) {
	ret = true;
	bjobFinished = true;
	jobFinishedBy = s;
    }
    pthread_mutex_unlock(&mutexJobFinished);
    return ret;
}

void SharedInfo::putPartFinished(LocalThread *s) {
    pthread_mutex_lock(&mutexPartJobFinished);
    PartjobFinished.push(s);
    pthread_mutex_unlock(&mutexPartJobFinished);
}

LocalThread * SharedInfo:: getPartFinished(){
    LocalThread * s;
    pthread_mutex_lock(&mutexPartJobFinished);
    s = PartjobFinished.last();
    PartjobFinished.shrink_(1);   
    pthread_mutex_unlock(&mutexPartJobFinished);
    return s;
}

int SharedInfo::NumPartjobFinished() {
    int ret;
    pthread_mutex_lock(&mutexPartJobFinished);
    ret = PartjobFinished.size();
    pthread_mutex_unlock(&mutexPartJobFinished);
    return ret;
}

