/***************************************************************************************[Solver.cc]
abcdSAT i20  by Jingchao Chen

**************************************************************************************************/

#include <math.h>
#include <algorithm>
#include <signal.h>
#include <unistd.h>

#include "mtl/Sort.h"
#include "core/Solver.h"
#include "utils/System.h"

#define ABS(x) ((x)>0?(x):(-x))
#define Swap(a,b) { int t; t=a; a=b; b=t;}

using namespace abcdSAT;

inline Lit makeLit(int lit) { return (lit > 0) ? mkLit(lit-1) : ~mkLit(-lit-1);}

//=================================================================================================
// Options:


static const char* _cat = "CORE";

static DoubleOption  opt_step_size         (_cat, "step-size",   "Initial step size",                             0.40,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_step_size_dec     (_cat, "step-size-dec","Step size decrement",                          0.000001, DoubleRange(0, false, 1, false));
static DoubleOption  opt_min_step_size     (_cat, "min-step-size","Minimal step size",                            0.06,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_var_decay         (_cat, "var-decay",   "The variable activity decay factor",            0.80,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_clause_decay      (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
static DoubleOption  opt_random_var_freq   (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption  opt_random_seed       (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption     opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption    opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);
static IntOption     opt_restart_first     (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
static DoubleOption  opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption  opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_chrono            (_cat, "chrono",  "Controls if to perform chrono backtrack", 100, IntRange(-1, INT32_MAX));
static IntOption     opt_conf_to_chrono    (_cat, "confl-to-chrono",  "Controls number of conflicts to perform chrono backtrack", 4000, IntRange(-1, INT32_MAX));

static IntOption     opt_max_lbd_dup       ("DUP-LEARNTS", "lbd-limit",  "specifies the maximum lbd of learnts to be screened for duplicates.", 12, IntRange(0, INT32_MAX));
static IntOption     opt_min_dupl_app      ("DUP-LEARNTS", "min-dup-app",  "specifies the minimum number of learnts to be included into db.", 3, IntRange(2, INT32_MAX));
static IntOption     opt_dupl_db_init_size ("DUP-LEARNTS", "dupdb-init",  "specifies the initial maximal duplicates DB size.", 500000, IntRange(1, INT32_MAX));

static IntOption     opt_VSIDS_props_limit ("DUP-LEARNTS", "VSIDS-lim",  "specifies the number of propagations after which the solver switches between LRB and VSIDS(in millions).", 30, IntRange(1, INT32_MAX));

//VSIDS_props_limit

//=================================================================================================
// Constructor/Destructor:


Solver::Solver() :

    // Parameters (user settable):
    //
    verbosity        (0)
  , step_size        (opt_step_size)
  , step_size_dec    (opt_step_size_dec)
  , min_step_size    (opt_min_step_size)
  , timer            (5000)
  , var_decay        (opt_var_decay)
  , clause_decay     (opt_clause_decay)
  , random_var_freq  (opt_random_var_freq)
  , random_seed      (opt_random_seed)
  , VSIDS            (false)
  , ccmin_mode       (opt_ccmin_mode)
  , phase_saving     (opt_phase_saving)
  , rnd_pol          (false)
  , rnd_init_act     (opt_rnd_init_act)
  , garbage_frac     (opt_garbage_frac)
  , restart_first    (opt_restart_first)
  , restart_inc      (opt_restart_inc)
 
  // Parameters (the rest):
  //
  , learntsize_factor((double)1/(double)3)
 
  // Parameters (experimental):
  //
  , learntsize_adjust_start_confl (100)
 
  // Statistics: (formerly in 'SolverStats')
  //
  , starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0), conflicts_VSIDS(0)
  , dec_vars(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)
  , chrono_backtrack(0), non_chrono_backtrack(0)
  
  , ok                 (true)
  , cla_inc            (1)
  , var_inc            (1)
  , watches_bin        (WatcherDeleted(ca))
  , watches            (WatcherDeleted(ca))
  , qhead              (0)
  , simpDB_assigns     (-1)
  , simpDB_props       (0)
  , order_heap_CHB     (VarOrderLt(activity_CHB))
  , order_heap_VSIDS   (VarOrderLt(activity_VSIDS))
  , order_heap_distance(VarOrderLt(activity_distance))

  , remove_satisfied   (true)

  , core_lbd_cut       (2)
  , global_lbd_sum     (0)
  , lbd_queue          (50)
  , next_T2_reduce     (10000)
  , next_L_reduce      (15000)
  , confl_to_chrono    (opt_conf_to_chrono)
  , chrono			   (opt_chrono)
  
  , counter            (0)

  // Resource constraints:
  //
  , conflict_budget    (-1)
  , propagation_budget (-1)
  , asynch_interrupt   (false)

  // simplfiy
  , nbSimplifyAll(0)
  , s_propagations(0)

  // simplifyAll adjust occasion
  , curSimplify(1)
  , nbconfbeforesimplify(1000)
  , incSimplify(1000)
  , my_var_decay       (0.6)
  , sched_heap         (VarSchedLt(vscore))
  {
    min_number_of_learnts_copies = opt_min_dupl_app;
    max_lbd_dup = opt_max_lbd_dup;
    dupl_db_init_size = opt_dupl_db_init_size;
    VSIDS_props_limit = opt_VSIDS_props_limit*1000000;
    DISTANCE =true;
    var_iLevel_inc = 1;

    equhead=equlink=0;
    mark = 0;
    touchMark=0;  
    dummyVar =0;
    equsum= unitsum =0;
    equMemSize=0;

    solveMode=0;
    preMode = 0;
    simpLearnMode=0;
    distance_mode=0;
}

Solver::Solver(const Solver &s) :
   verbosity(s.verbosity)
  , step_size        (s.step_size)
  , step_size_dec    (s.step_size_dec)
  , min_step_size    (s.min_step_size)
  , timer            (s.timer)
  , var_decay        (s.var_decay)
  , clause_decay     (s.clause_decay)
  , random_var_freq  (s.random_var_freq)
  , random_seed      (s.random_seed)
  , VSIDS            (s.VSIDS)
  , ccmin_mode       (s.ccmin_mode)
  , phase_saving     (s.phase_saving)
  , rnd_pol          (s.rnd_pol)
  , rnd_init_act     (s.rnd_init_act)
  , garbage_frac     (s.garbage_frac)
  , restart_first    (s.restart_first)
  , restart_inc      (s.restart_inc)
 
  , learntsize_factor(s.learntsize_factor)
  
  // Parameters (experimental):
  //
  , learntsize_adjust_start_confl (100)
  
  // Statistics: (formerly in 'SolverStats')
  //
  , starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0), conflicts_VSIDS(0)
  , dec_vars(s.dec_vars), clauses_literals(s.clauses_literals)
  , learnts_literals(s.learnts_literals), max_literals(s.max_literals), tot_literals(s.tot_literals)
  , chrono_backtrack(0), non_chrono_backtrack(0)

  , ok                 (true)
  , cla_inc(s.cla_inc)
  , var_inc(s.var_inc)
  , watches_bin        (WatcherDeleted(ca))
  , watches            (WatcherDeleted(ca))
  , qhead(s.qhead)

  , simpDB_assigns(s.simpDB_assigns)
  , simpDB_props(s.simpDB_props)

  , order_heap_CHB     (VarOrderLt(activity_CHB))
  , order_heap_VSIDS   (VarOrderLt(activity_VSIDS))
  , order_heap_distance(VarOrderLt(activity_distance))

  , remove_satisfied   (true)

  , core_lbd_cut       (s.core_lbd_cut)
  , global_lbd_sum     (0)

  , lbd_queue          (50)
  , next_T2_reduce     (10000)
  , next_L_reduce      (15000)
  , confl_to_chrono    (opt_conf_to_chrono)
  , chrono			   (opt_chrono)
  
  , counter            (0)

  // Resource constraints:
  //
  , conflict_budget    (s.conflict_budget)
  , propagation_budget (s.propagation_budget)
  , asynch_interrupt   (s.asynch_interrupt)

  // simplfiy
  , nbSimplifyAll(0)
  , s_propagations(0)

  // simplifyAll adjust occasion
  , curSimplify(1)
  , nbconfbeforesimplify(1000)
  , incSimplify(1000)
  , my_var_decay       (0.6)
  , sched_heap         (VarSchedLt(vscore))
{
    // Copy clauses.
    s.ca.copyTo(ca);
    ca.extra_clause_field = s.ca.extra_clause_field;

//=====================
    // Copy all other vectors
    s.watches.copyTo(watches);
    s.watches_bin.copyTo(watches_bin);
    s.assigns.memCopyTo(assigns);
    s.vardata.memCopyTo(vardata);
    s.activity_CHB.memCopyTo(activity_CHB);
    s.activity_VSIDS.memCopyTo(activity_VSIDS);
    s.picked.memCopyTo(picked);
    s.conflicted.memCopyTo(conflicted);
    s.almost_conflicted.memCopyTo(almost_conflicted);
#ifdef ANTI_EXPLORATION
    s.canceled.memCopyTo(canceled);
#endif
    s.seen.memCopyTo(seen);
    s.seen2.memCopyTo(seen2); //permDiff;
    s.polarity.memCopyTo(polarity);
    s.decision.memCopyTo(decision);
    s.trail.memCopyTo(trail);
    s.activity_distance.memCopyTo(activity_distance);
    s.var_iLevel.memCopyTo(var_iLevel);
    s.var_iLevel_tmp.memCopyTo(var_iLevel_tmp);
    s.pathCs.memCopyTo(pathCs);
///
    s.order_heap_CHB.copyTo(order_heap_CHB);
    s.order_heap_VSIDS.copyTo(order_heap_VSIDS);
    s.order_heap_distance.copyTo(order_heap_distance);

    s.clauses.memCopyTo(clauses);
    s.learnts.memCopyTo(learnts);

    lbd_queue.clear();

    parallel_pivot = lit_Undef;
    s.vscore.memCopyTo(vscore);

    s.extendRemLit.memCopyTo(extendRemLit);

    min_number_of_learnts_copies = opt_min_dupl_app;
    max_lbd_dup = opt_max_lbd_dup;
    dupl_db_init_size = opt_dupl_db_init_size;
    VSIDS_props_limit = opt_VSIDS_props_limit*1000000;
   // DISTANCE =true;
    DISTANCE = false;
    var_iLevel_inc = 1;

    mark = 0;
    touchMark=0;  
    dummyVar =0;

    equsum = s.equsum; 
    unitsum = s.unitsum;
    equMemSize = s.equMemSize;

    if(s.equhead){
          equhead = (int * ) calloc (s.nVars()+1, sizeof(int));
          equlink = (int * ) calloc (s.nVars()+1, sizeof(int));
          for(int i=0; i<=s.nVars(); i++) {
              equhead[i]=s.equhead[i];
              equlink[i]=s.equlink[i];
          }
    }
    else equhead=equlink=0;

    solveMode=0;
    preMode = 0;
    simpLearnMode=0;
    distance_mode=0;
    canPause=pause=false;
}

Solver::~Solver()
{
}


Var Solver::newVar(bool sign, bool dvar)
{
    int v = nVars();
    watches_bin.init(mkLit(v, false));
    watches_bin.init(mkLit(v, true ));
    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    assigns  .push(l_Undef);
    vardata  .push(mkVarData(CRef_Undef, 0));
    activity_CHB  .push(0);
    activity_VSIDS.push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);

    picked.push(0);
    conflicted.push(0);
    almost_conflicted.push(0);
#ifdef ANTI_EXPLORATION
    canceled.push(0);
#endif

    seen     .push(0);
    seen2    .push(0);
    polarity .push(sign);
    decision .push();
    trail    .capacity(v+1);
    setDecisionVar(v, dvar);

    activity_distance.push(0);
    var_iLevel.push(0);
    var_iLevel_tmp.push(0);
    pathCs.push(0);
    return v;
}

// simplify All
//
CRef Solver::simplePropagate()
{
    CRef    confl = CRef_Undef;
    int     num_props = 0;
    watches.cleanAll();
    watches_bin.cleanAll();
    while (qhead < trail.size())
    {
        Lit            p = trail[qhead++];     // 'p' is enqueued fact to propagate.
        vec<Watcher>&  ws = watches[p];
        Watcher        *i, *j, *end;
        num_props++;

        // First, Propagate binary clauses
        vec<Watcher>&  wbin = watches_bin[p];

        for (int k = 0; k<wbin.size(); k++)
        {
            Lit imp = wbin[k].blocker;

            if (value(imp) == l_False) return wbin[k].cref;

            if (value(imp) == l_Undef) simpleUncheckEnqueue(imp, wbin[k].cref);
        }
        for (i = j = (Watcher*)ws, end = i + ws.size(); i != end;)
        {
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if (value(blocker) == l_True)
            {
                *j++ = *i++; continue;
            }

            // Make sure the false literal is data[1]:
            CRef     cr = i->cref;
            Clause&  c = ca[cr];
            Lit      false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            //  i++;

            // If 0th watch is true, then clause is already satisfied.
            // However, 0th watch is not the blocker, make it blocker using a new watcher w
            // why not simply do i->blocker=first in this case?
            Lit     first = c[0];
            //  Watcher w     = Watcher(cr, first);
            if (first != blocker && value(first) == l_True)
            {
                i->blocker = first;
                *j++ = *i++; continue;
            }
            else
            {  // ----------------- DEFAULT  MODE (NOT INCREMENTAL)
                for (int k = 2; k < c.size(); k++)
                {

                    if (value(c[k]) != l_False)
                    {
                        // watcher i is abandonned using i++, because cr watches now ~c[k] instead of p
                        // the blocker is first in the watcher. However,
                        // the blocker in the corresponding watcher in ~first is not c[1]
                        Watcher w = Watcher(cr, first); i++;
                        c[1] = c[k]; c[k] = false_lit;
                        watches[~c[1]].push(w);
                        goto NextClause;
                    }
                }
            }

            // Did not find watch -- clause is unit under assignment:
            i->blocker = first;
            *j++ = *i++;
            if (value(first) == l_False)
            {
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end)
                    *j++ = *i++;
            }
            else  simpleUncheckEnqueue(first, cr);
NextClause:;
        }
        ws.shrink(i - j);
    }

    s_propagations += num_props;

    return confl;
}

void Solver::simpleUncheckEnqueue(Lit p, CRef from){
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p)); // this makes a lbool object whose value is sign(p)
    vardata[var(p)].reason = from;
    trail.push_(p);
}

void Solver::cancelUntilTrailRecord()
{
    for (int c = trail.size() - 1; c >= trailRecord; c--)
    {
        Var x = var(trail[c]);
        assigns[x] = l_Undef;

    }
    qhead = trailRecord;
    trail.shrink(trail.size() - trailRecord);

}

void Solver::litsEnqueue(int cutP, Clause& c)
{
    for (int i = cutP; i < c.size(); i++)
    {
        simpleUncheckEnqueue(~c[i]);
    }
}

bool Solver::removed(CRef cr) {
    return ca[cr].mark() == 1;
}

void Solver::simpleAnalyze(CRef confl, vec<Lit>& out_learnt, vec<CRef>& reason_clause, bool True_confl)
{
    int pathC = 0;
    Lit p = lit_Undef;
    int index = trail.size() - 1;

    do{
        if (confl != CRef_Undef){
            reason_clause.push(confl);
            Clause& c = ca[confl];
            // Special case for binary clauses
            // The first one has to be SAT
            if (p != lit_Undef && c.size() == 2 && value(c[0]) == l_False) {

                assert(value(c[1]) == l_True);
                Lit tmp = c[0];
                c[0] = c[1], c[1] = tmp;
            }
            // if True_confl==true, then choose p begin with the 1th index of c;
            for (int j = (p == lit_Undef && True_confl == false) ? 0 : 1; j < c.size(); j++){
                Lit q = c[j];
                if (!seen[var(q)]){
                    seen[var(q)] = 1;
                    pathC++;
                }
            }
        }
        else if (confl == CRef_Undef){
            out_learnt.push(~p);
        }
        // if not break, while() will come to the index of trail blow 0, and fatal error occur;
        if (pathC == 0) break;
        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        // if the reason cr from the 0-level assigned var, we must break avoid move forth further;
        // but attention that maybe seen[x]=1 and never be clear. However makes no matter;
        if (trailRecord > index + 1) break;
        p = trail[index + 1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    } while (pathC >= 0);
}

void Solver::simplifyLearnt(Clause& c)
{
    original_length_record += c.size();
    trailRecord = trail.size();// record the start pointer

    vec<Lit> falseLit;
    falseLit.clear();
    bool True_confl = false;
    int i, j;
    CRef confl;

    for (i = 0, j = 0; i < c.size(); i++){
        if (value(c[i]) == l_Undef){
            simpleUncheckEnqueue(~c[i]);
            c[j++] = c[i];
            confl = simplePropagate();
            if (confl != CRef_Undef) break;
        }
        else{
            if (value(c[i]) == l_True){
                c[j++] = c[i];
                True_confl = true;
                confl = reason(var(c[i]));
                break;
            }
            else  falseLit.push(c[i]);
        }
    }
    c.shrink(c.size() - j);
 
    if (confl != CRef_Undef || True_confl == true){
        simp_learnt_clause.clear();
        simp_reason_clause.clear();
        if (True_confl == true){
            simp_learnt_clause.push(c.last());
        }
        simpleAnalyze(confl, simp_learnt_clause, simp_reason_clause, True_confl);

        if (simp_learnt_clause.size() < c.size()){
            for (i = 0; i < simp_learnt_clause.size(); i++){
                c[i] = simp_learnt_clause[i];
            }
            c.shrink(c.size() - i);
        }
    }

    cancelUntilTrailRecord();

    simplified_length_record += c.size();

}

bool Solver::simplifyLearnt_core()
{
    int ci, cj, li, lj;
    bool sat, false_lit;
    unsigned int nblevels;
    int nbSimplifing = 0;

    for (ci = 0, cj = 0; ci < learnts.size(); ci++){
        CRef cr = learnts[ci];
        Clause& c = ca[cr];
        if(c.mark() == REMOVED ) continue;
        if (c.simplified() || c.mark() == LONG) learnts[cj++] = learnts[ci];
        else{
            nbSimplifing++;
            sat = false_lit = false;
            for (int i = 0; i < c.size(); i++){
                if (value(c[i]) == l_True){
                    sat = true;
                    break;
                }
                else if (value(c[i]) == l_False) false_lit = true;
            }
            if (sat) removeClause(cr);
            else{
                detachClause(cr, true);

                if (false_lit){
                    for (li = lj = 0; li < c.size(); li++){
                        if (value(c[li]) != l_False){
                            c[lj++] = c[li];
                        }
                    }
                    c.shrink(li - lj);
                }

                simplifyLearnt(c);

                if (c.size() == 1){
                    // when unit clause occur, enqueue and propagate
                    uncheckedEnqueue(c[0]);
                    if (propagate() != CRef_Undef){
                        ok = false;
                        return false;
                    }
                    // delete the clause memory in logic
                    c.mark(REMOVED);
                    ca.free(cr);
                }
                else{
                    attachClause(cr);
                    learnts[cj++] = learnts[ci];
                    nblevels = computeLBD(c);
                    if ((signed)nblevels < c.lbd()) c.set_lbd(nblevels);
                    if (c.lbd() <= core_lbd_cut) c.mark(SMALL);                 
                    c.setSimplified(true);
                 }
            }
        }
    }
    learnts.shrink(ci - cj);
    return true;

}

int Solver::is_duplicate(std::vector<uint32_t>&c){
   auto time_point_0 = std::chrono::high_resolution_clock::now();
    dupl_db_size++;
    int res = 0;    
    
    int sz = c.size();
    std::vector<uint32_t> tmp(c);    
    sort(tmp.begin(),tmp.end());
    
    uint64_t hash = 0;    
    
    for (int i =0; i<sz; i++) {
        hash ^= tmp[i] + 0x9e3779b9 + (hash << 6) + (hash>> 2);     
    }    
    
    int32_t head = tmp[0];
    auto it0 = ht.find(head);
    if (it0 != ht.end()){
        auto it1=ht[head].find(sz);
        if (it1 != ht[head].end()){
            auto it2 = ht[head][sz].find(hash);
            if (it2 != ht[head][sz].end()){
                it2->second++;
                res = it2->second;            
            }
            else{
                ht[head][sz][hash]=1;
            }
        }
        else{            
            ht[head][sz][hash]=1;
        }
    }else{        
        ht[head][sz][hash]=1;
    } 
    auto time_point_1 = std::chrono::high_resolution_clock::now();
    duptime += std::chrono::duration_cast<std::chrono::microseconds>(time_point_1-time_point_0);    
    return res;
}

bool Solver::simplifyAll()
{
    simplified_length_record = original_length_record = 0;
    cancelUntil(0);
    //if (!ok || propagate() != CRef_Undef)
      //  return ok = false;

    if (!simplifyLearnt_core()) return ok = false;
  //  if (!simplifyLearnt_tier2()) return ok = false;

    checkGarbage();
    return true;
}
//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//

bool Solver::addClause_(vec<Lit>& ps)
{
    assert(decisionLevel() == 0);
    if (!ok) return false;

    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);
    Lit p; int i, j;

    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
        if (value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    ps.shrink(i - j);

    if (ps.size() == 0)
        return ok = false;
    else if (ps.size() == 1){
        uncheckedEnqueue(ps[0]);
        return ok = (propagate() == CRef_Undef);
    }else{
        CRef cr = ca.alloc(ps, false);
        clauses.push(cr);
        attachClause(cr);
    }

    return true;
}


void Solver::attachClause(CRef cr) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    OccLists<Lit, vec<Watcher>, WatcherDeleted>& ws = c.size() == 2 ? watches_bin : watches;
    ws[~c[0]].push(Watcher(cr, c[1]));
    ws[~c[1]].push(Watcher(cr, c[0]));
    if (c.learnt()) learnts_literals += c.size();
    else            clauses_literals += c.size(); }


void Solver::detachClause(CRef cr, bool strict) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    OccLists<Lit, vec<Watcher>, WatcherDeleted>& ws = c.size() == 2 ? watches_bin : watches;
    
    if (strict){
        remove(ws[~c[0]], Watcher(cr, c[1]));
        remove(ws[~c[1]], Watcher(cr, c[0]));
    }else{
        // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
        ws.smudge(~c[0]);
        ws.smudge(~c[1]);
    }

    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size(); }


void Solver::removeClause(CRef cr) {
    Clause& c = ca[cr];

    detachClause(cr);
    // Don't leave pointers to free'd memory!
    if (locked(c)){
        Lit implied = c.size() != 2 ? c[0] : (value(c[0]) == l_True ? c[0] : c[1]);
        vardata[var(implied)].reason = CRef_Undef; }
    c.mark(1);
    ca.free(cr);
}


bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int bLevel) {
	
    if (decisionLevel() > bLevel){
#ifdef PRINT_OUT
		std::cout << "bt " << bLevel << "\n";
#endif				
		add_tmp.clear();
        for (int c = trail.size()-1; c >= trail_lim[bLevel]; c--)
        {
            Var      x  = var(trail[c]);

			if (level(x) <= bLevel)
			{
				add_tmp.push(trail[c]);
			}
			else
			{
				 if (!VSIDS){
					uint32_t age = conflicts - picked[x];
					if (age > 0){
						double adjusted_reward = ((double) (conflicted[x] + almost_conflicted[x])) / ((double) age);
						double old_activity = activity_CHB[x];
						activity_CHB[x] = step_size * adjusted_reward + ((1 - step_size) * old_activity);
						if (order_heap_CHB.inHeap(x)){
							if (activity_CHB[x] > old_activity)
								order_heap_CHB.decrease(x);
							else
								order_heap_CHB.increase(x);
						}
					}
#ifdef ANTI_EXPLORATION
					canceled[x] = conflicts;
#endif
				}
				
				assigns [x] = l_Undef;
#ifdef PRINT_OUT
				std::cout << "undo " << x << "\n";
#endif				
	            if (phase_saving > 1 || (phase_saving == 1) && c > trail_lim.last())
					polarity[x] = sign(trail[c]);
				insertVarOrder(x);
			}
        }
        qhead = trail_lim[bLevel];
        trail.shrink(trail.size() - trail_lim[bLevel]);
        trail_lim.shrink(trail_lim.size() - bLevel);
        for (int nLitId = add_tmp.size() - 1; nLitId >= 0; --nLitId)
		{
			trail.push_(add_tmp[nLitId]);
		}
		
		add_tmp.clear();
    } }


//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit()
{
    Var next = var_Undef;
    Heap<VarOrderLt>& order_heap = DISTANCE ? order_heap_distance : ((!VSIDS)? order_heap_CHB:order_heap_VSIDS);

    while (next == var_Undef || value(next) != l_Undef || !decision[next])
        if (order_heap.empty())
            return lit_Undef;
        else{
#ifdef ANTI_EXPLORATION
            if (!VSIDS){
                Var v = order_heap_CHB[0];
                uint32_t age = conflicts - canceled[v];
                while (age > 0){
                    double decay = pow(0.95, age);
                    activity_CHB[v] *= decay;
                    if (order_heap_CHB.inHeap(v))
                        order_heap_CHB.increase(v);
                    canceled[v] = conflicts;
                    v = order_heap_CHB[0];
                    age = conflicts - canceled[v];
                }
            }
#endif
            next = order_heap.removeMin();
        }

    return mkLit(next, polarity[next]);
}

inline Solver::ConflictData Solver::FindConflictLevel(CRef cind)
{
	ConflictData data;
	Clause& conflCls = ca[cind];
	data.nHighestLevel = level(var(conflCls[0]));
	if (data.nHighestLevel == decisionLevel() && level(var(conflCls[1])) == decisionLevel())
	{
		return data;
	}

	int highestId = 0;
    data.bOnlyOneLitFromHighest = true;
	// find the largest decision level in the clause
	for (int nLitId = 1; nLitId < conflCls.size(); ++nLitId)
	{
		int nLevel = level(var(conflCls[nLitId]));
		if (nLevel > data.nHighestLevel)
		{
			highestId = nLitId;
			data.nHighestLevel = nLevel;
			data.bOnlyOneLitFromHighest = true;
		}
		else if (nLevel == data.nHighestLevel && data.bOnlyOneLitFromHighest == true)
		{
			data.bOnlyOneLitFromHighest = false;
		}
	}

	if (highestId != 0)
	{
		std::swap(conflCls[0], conflCls[highestId]);
		if (highestId > 1)
		{
			OccLists<Lit, vec<Watcher>, WatcherDeleted>& ws = conflCls.size() == 2 ? watches_bin : watches;
			remove(ws[~conflCls[highestId]], Watcher(cind, conflCls[1]));
			ws[~conflCls[0]].push(Watcher(cind, conflCls[1]));
		}
	}

	return data;
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the 
|        rest of literals. There may be others from the same level though.
|  
|________________________________________________________________________________________________@*/
void Solver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel, int& out_lbd)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;
    int nDecisionLevel = level(var(ca[confl][0]));
    assert(nDecisionLevel == level(var(ca[confl][0])));

    do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

        // For binary clauses, we don't rearrange literals in propagate(), so check and make sure the first is an implied lit.
        if (p != lit_Undef && c.size() == 2 && value(c[0]) == l_False){
            assert(value(c[1]) == l_True);
            Lit tmp = c[0];
            c[0] = c[1], c[1] = tmp; }

        // Update LBD if improved.
        if (c.learnt() && c.mark() != SMALL){
             int lbd = computeLBD(c);
            if (lbd < c.lbd()){
                if (c.lbd() <= 30) c.removable(false); // Protect once from reduction.
                c.set_lbd(lbd);
                if (lbd <= core_lbd_cut) c.mark(SMALL);
                else if (lbd <= 6 && c.mark() == LONG) c.mark(MIDSZ); 
            }

            if (c.mark() == MIDSZ) c.touched() = conflicts;
            else if (c.mark() == LONG) claBumpActivity(c);
      
        }

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level(var(q)) > 0){
                if (VSIDS){
                    varBumpActivity(var(q), .5);
                    add_tmp.push(q);
                }else
                    conflicted[var(q)]++;
                seen[var(q)] = 1;
                if (level(var(q)) >= nDecisionLevel){
                    pathC++;
                }else
                    out_learnt.push(q);
            }
        }
        
        // Select next clause to look at:
		do {
			while (!seen[var(trail[index--])]);
			p  = trail[index+1];
		} while (level(var(p)) < nDecisionLevel);
		
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    } while (pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];
        
    }else if (ccmin_mode == 1){
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{
                Clause& c = ca[reason(var(out_learnt[i]))];
                for (int k = c.size() == 2 ? 0 : 1; k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0){
                        out_learnt[j++] = out_learnt[i];
                        break; }
            }
        }
    }else
        i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    out_lbd = computeLBD(out_learnt);
    if (out_lbd <= 6 && out_learnt.size() <= 30) // Try further minimization?
        if (binResMinimize(out_learnt))
            out_lbd = computeLBD(out_learnt); // Recompute LBD if minimized.

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }

    if (VSIDS){
        for (int i = 0; i < add_tmp.size(); i++){
            Var v = var(add_tmp[i]);
            if (level(v) >= out_btlevel - 1)
                varBumpActivity(v, 1);
        }
        add_tmp.clear();
    }else{
        seen[var(p)] = true;
        for(int i = out_learnt.size() - 1; i >= 0; i--){
            Var v = var(out_learnt[i]);
            CRef rea = reason(v);
            if (rea != CRef_Undef){
                const Clause& reaC = ca[rea];
                for (int i = 0; i < reaC.size(); i++){
                    Lit l = reaC[i];
                    if (!seen[var(l)]){
                        seen[var(l)] = true;
                        almost_conflicted[var(l)]++;
                        analyze_toclear.push(l); } } } } }

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
}


// Try further learnt clause minimization by means of binary clause resolution.
bool Solver::binResMinimize(vec<Lit>& out_learnt)
{
    // Preparation: remember which false variables we have in 'out_learnt'.
    counter++;
    for (int i = 1; i < out_learnt.size(); i++)
        seen2[var(out_learnt[i])] = counter;

    // Get the list of binary clauses containing 'out_learnt[0]'.
    const vec<Watcher>& ws = watches_bin[~out_learnt[0]];

    int to_remove = 0;
    for (int i = 0; i < ws.size(); i++){
        Lit the_other = ws[i].blocker;
        // Does 'the_other' appear negatively in 'out_learnt'?
        if (seen2[var(the_other)] == counter && value(the_other) == l_True){
            to_remove++;
            seen2[var(the_other)] = counter - 1; // Remember to remove this variable.
        }
    }

    // Shrink.
    if (to_remove > 0){
        int last = out_learnt.size() - 1;
        for (int i = 1; i < out_learnt.size() - to_remove; i++)
            if (seen2[var(out_learnt[i])] != counter)
                out_learnt[i--] = out_learnt[last--];
        out_learnt.shrink(to_remove);
    }
    return to_remove != 0;
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver::litRedundant(Lit p, uint32_t abstract_levels)
{
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0){
        assert(reason(var(analyze_stack.last())) != CRef_Undef);
        Clause& c = ca[reason(var(analyze_stack.last()))]; analyze_stack.pop();

        // Special handling for binary clauses like in 'analyze()'.
        if (c.size() == 2 && value(c[0]) == l_False){
            assert(value(c[1]) == l_True);
            Lit tmp = c[0];
            c[0] = c[1], c[1] = tmp; }

        for (int i = 1; i < c.size(); i++){
            Lit p  = c[i];
            if (!seen[var(p)] && level(var(p)) > 0){
                if (reason(var(p)) != CRef_Undef && (abstractLevel(var(p)) & abstract_levels) != 0){
                    seen[var(p)] = 1;
                    analyze_stack.push(p);
                    analyze_toclear.push(p);
                }else{
                    for (int j = top; j < analyze_toclear.size(); j++)
                        seen[var(analyze_toclear[j])] = 0;
                    analyze_toclear.shrink(analyze_toclear.size() - top);
                    return false;
                }
            }
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            if (reason(x) == CRef_Undef){
                assert(level(x) > 0);
                out_conflict.push(~trail[i]);
            }else{
                Clause& c = ca[reason(x)];
                for (int j = c.size() == 2 ? 0 : 1; j < c.size(); j++)
                    if (level(var(c[j])) > 0)
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}


void Solver::uncheckedEnqueue(Lit p, int level, CRef from)
{
    assert(value(p) == l_Undef);
    Var x = var(p);
    if (!VSIDS){
        picked[x] = conflicts;
        conflicted[x] = 0;
        almost_conflicted[x] = 0;
#ifdef ANTI_EXPLORATION
        uint32_t age = conflicts - canceled[var(p)];
        if (age > 0){
            double decay = pow(0.95, age);
            activity_CHB[var(p)] *= decay;
            if (order_heap_CHB.inHeap(var(p)))
                order_heap_CHB.increase(var(p));
        }
#endif
    }

    assigns[x] = lbool(!sign(p));
    vardata[x] = mkVarData(from, level);
    trail.push_(p);
}

/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
CRef Solver::propagate()
{
    CRef    confl     = CRef_Undef;
    int     num_props = 0;
    watches.cleanAll();
    watches_bin.cleanAll();

    while (qhead < trail.size()){
        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        int currLevel = level(var(p));
        vec<Watcher>&  ws  = watches[p];
        Watcher        *i, *j, *end;
        num_props++;

        vec<Watcher>& ws_bin = watches_bin[p];  // Propagate binary clauses first.
        for (int k = 0; k < ws_bin.size(); k++){
            Lit the_other = ws_bin[k].blocker;
            if (value(the_other) == l_False){
                confl = ws_bin[k].cref;
#ifdef LOOSE_PROP_STAT
                return confl;
#else
                goto ExitProp;
#endif
            }else if(value(the_other) == l_Undef)
            {
                uncheckedEnqueue(the_other, currLevel, ws_bin[k].cref);
#ifdef  PRINT_OUT                
                std::cout << "i " << the_other << " l " << currLevel << "\n";
#endif                
			}
        }

        for (i = j = (Watcher*)ws, end = i + ws.size();  i != end;){
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if (value(blocker) == l_True){
                *j++ = *i++; continue; 
            }

            // Make sure the false literal is data[1]:
            CRef     cr        = i->cref;
            Clause&  c         = ca[cr];
            Lit      false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit     first = c[0];
            Watcher w     = Watcher(cr, first);
            if (first != blocker && value(first) == l_True){
                *j++ = w; 
                continue; 
            }

            // Look for new watch:
            for (int k = 2; k < c.size(); k++)
                if (value(c[k]) != l_False){
                    c[1] = c[k]; c[k] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause; }

            // Did not find watch -- clause is unit under assignment:
            *j++ = w;
            if (value(first) == l_False){
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end) *j++ = *i++;
            }else
            {
				if (currLevel == decisionLevel())
				{
					uncheckedEnqueue(first, currLevel, cr);
#ifdef PRINT_OUT					
					std::cout << "i " << first << " l " << currLevel << "\n";
#endif					
				}
				else
				{
					int nMaxLevel = currLevel;
					int nMaxInd = 1;
					// pass over all the literals in the clause and find the one with the biggest level
					for (int nInd = 2; nInd < c.size(); ++nInd)
					{
						int nLevel = level(var(c[nInd]));
						if (nLevel > nMaxLevel)
						{
							nMaxLevel = nLevel;
							nMaxInd = nInd;
						}
					}

					if (nMaxInd != 1)
					{
						std::swap(c[1], c[nMaxInd]);
//						*j--; 
						j--; 
						watches[~c[1]].push(w);
					}
					
					uncheckedEnqueue(first, nMaxLevel, cr);
#ifdef PRINT_OUT					
					std::cout << "i " << first << " l " << nMaxLevel << "\n";
#endif	
				}
			}

NextClause:;
        }
        ws.shrink(i - j);
    }

//ExitProp:;
    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}


/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt { 
    ClauseAllocator& ca;
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) const { return ca[x].activity() < ca[y].activity(); }
};

struct reduceDB_lt2 { 
    ClauseAllocator& ca;
    reduceDB_lt2(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) const {
         return ca[y].lbd() < ca[x].lbd();
    //       return ca[x].activity()-ca[x].lbd() < ca[y].activity()-ca[y].lbd(); 
     }
};

void Solver::reduceDB()
{
    int     i, j;
  
    vec<CRef> learntTmp;
    for (i =j=0; i < learnts.size(); i++){
           CRef cr=learnts[i];
           if(ca[cr].mark() == LONG) learntTmp.push(cr);
           else learnts[j++]=cr;
     }

    sort(learntTmp, reduceDB_lt(ca));
    if(learntTmp.size()>100 && conflicts<600000 && nFreeVars()>20000){
           int b=learntTmp.size()/16;
           sort((CRef *)learntTmp+7*b, b+b/2, reduceDB_lt2(ca));
     }

    int limit = learntTmp.size() / 2;
    for (i =0; i < learntTmp.size(); i++){
        Clause & c = ca[learntTmp[i]];
        if (c.removable() && !locked(c) && i < limit) removeClause(learntTmp[i]);
        else{
             if (!c.removable()) limit++;
             c.removable(true);
             learnts[j++] = learntTmp[i];
        }
     }
    
    learnts.shrink(learnts.size() - j);
    checkGarbage();
}

void Solver::reduceDB_Tier2()
{
    int i, j;
    for (i = j = 0; i < learnts.size(); i++){
        Clause& c = ca[learnts[i]];
        if (c.mark() == MIDSZ)
            if (!locked(c) && c.touched() + 30000 < conflicts){
                c.mark(LONG);
                c.activity() = 0;
                claBumpActivity(c);
            }
    }
}

void Solver::removeSatisfied(vec<CRef>& cs)
{
    int i, j;
    for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];
        if (satisfied(c))
            removeClause(cs[i]);
        else
            cs[j++] = cs[i];
    }
    cs.shrink(i - j);
}

void Solver::rebuildOrderHeap()
{
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef)
            vs.push(v);

    order_heap_CHB  .build(vs);
    order_heap_VSIDS.build(vs);
    order_heap_distance.build(vs);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify()
{
    assert(decisionLevel() == 0);

    if (!ok || propagate() != CRef_Undef) return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0)) return true;

    removeSatisfied(learnts);
    if (remove_satisfied)        // Can be turned off.
        removeSatisfied(clauses);
    checkGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}

// pathCs[k] is the number of variables assigned at level k,
// it is initialized to 0 at the begining and reset to 0 after the function execution
bool Solver::collectFirstUIP(CRef confl)
{
    involved_lits.clear();
    int max_level=1;
    Clause& c=ca[confl]; 
    int minLevel=decisionLevel();
    for(int i=0; i<c.size(); i++) {
        Var v=var(c[i]);
        if (level(v)>0) {
            seen[v]=1;
            var_iLevel_tmp[v]=1;
            pathCs[level(v)]++;
            if (minLevel>level(v)) minLevel=level(v);
        }
    }

    int limit=trail_lim[minLevel-1];
    for(int i=trail.size()-1; i>=limit; i--) {
        Lit p=trail[i]; Var v=var(p);
        if (seen[v]) {
            int currentDecLevel=level(v);
            seen[v]=0;
            if (--pathCs[currentDecLevel]!=0) {
                Clause& rc=ca[reason(v)];
                int reasonVarLevel=var_iLevel_tmp[v]+1;
                if(reasonVarLevel>max_level) max_level=reasonVarLevel;
                if (rc.size()==2 && value(rc[0])==l_False) {
                    // Special case for binary clauses
                    // The first one has to be SAT
                    assert(value(rc[1]) != l_False);
                    Lit tmp = rc[0];
                    rc[0] =  rc[1], rc[1] = tmp;
                }
                for (int j = 1; j < rc.size(); j++){
                    Lit q = rc[j]; Var v1=var(q);
                    if (level(v1) > 0) {
                        if (minLevel>level(v1)) {
                            minLevel=level(v1); limit=trail_lim[minLevel-1]; 	assert(minLevel>0);
                        }
                        if (seen[v1]) {
                            if (var_iLevel_tmp[v1]<reasonVarLevel)
                                var_iLevel_tmp[v1]=reasonVarLevel;
                        }
                        else {
                            var_iLevel_tmp[v1]=reasonVarLevel;
                            seen[v1] = 1;
                            pathCs[level(v1)]++;
                        }
                    }
                }
            }
            involved_lits.push(p);
        }
    }
    double inc=var_iLevel_inc;
    vec<int> level_incs; level_incs.clear();
    for(int i=0;i<max_level;i++){
        level_incs.push(inc);
        inc = inc/my_var_decay;
    }

    for(int i=0;i<involved_lits.size();i++){
        Var v =var(involved_lits[i]);
        activity_distance[v]+=var_iLevel_tmp[v]*level_incs[var_iLevel_tmp[v]-1];

        if(activity_distance[v]>1e100){
            for(int vv=0;vv<nVars();vv++)
                activity_distance[vv] *= 1e-100;
            var_iLevel_inc*=1e-100;
            for(int j=0; j<max_level; j++) level_incs[j]*=1e-100;
        }
        if (order_heap_distance.inHeap(v)) order_heap_distance.decrease(v);
    }
    var_iLevel_inc=level_incs[level_incs.size()-1];
    return true;
}

/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts. 
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int& nof_conflicts)
{
    assert(ok);
    int         backtrack_level;
    int         lbd;
    vec<Lit>    learnt_clause;
    bool        cached = false;
    starts++;

    // simplify
    //
    if(simpLearnMode){
       if ((signed)conflicts >= curSimplify * nbconfbeforesimplify){
           nbSimplifyAll++;
           if (!simplifyAll())  return l_False;
           curSimplify = (conflicts / nbconfbeforesimplify) + 1;
           nbconfbeforesimplify += incSimplify;
       }
    }
    int chrono_lim=10000;
    if(VSIDS && nof_conflicts>1000000) nof_conflicts=1000000;
    for (;;){
        CRef confl = propagate();

        if (confl != CRef_Undef){
            // CONFLICT
            if (VSIDS){
                if (--timer == 0 && var_decay < 0.95) timer = 5000, var_decay += 0.01;
            }else
                if (step_size > min_step_size) step_size -= step_size_dec;

            conflicts++; nof_conflicts--;
            if(nof_conflicts<-100000){
                cancelUntil(0);
                return l_Undef; 
            }
            //if (conflicts == 100000 && learnts_core.size() < 100) core_lbd_cut = 5;
            ConflictData data = FindConflictLevel(confl);
            if (data.nHighestLevel == 0) return l_False;
            if (data.bOnlyOneLitFromHighest)
            {
                chrono_lim--;
				cancelUntil(data.nHighestLevel - 1);
				continue;
			}
           
            learnt_clause.clear();

            if(distance_mode){
                 if(conflicts>50000) DISTANCE=0;
                 else DISTANCE=1;
            }
            else DISTANCE=0;

            if(VSIDS && DISTANCE) collectFirstUIP(confl);

            analyze(confl, learnt_clause, backtrack_level, lbd);
            // check chrono backtrack condition
            if (chrono_lim>0 && (confl_to_chrono < 0 || confl_to_chrono <= (int)conflicts) && chrono > -1 && (decisionLevel() - backtrack_level) >= chrono)
            {
		         chrono_lim--;
				++chrono_backtrack;
				cancelUntil(data.nHighestLevel -1);
			}
			else // default behavior
			{
				++non_chrono_backtrack;
				cancelUntil(backtrack_level);
			}

            lbd--;
            lbd_sum += lbd;
            if (VSIDS){
                cached = false;
                conflicts_VSIDS++;
                lbd_queue.push(lbd);
                global_lbd_sum += (lbd > 50 ? 50 : lbd); }

            if (learnt_clause.size() == 1){
                uncheckedEnqueue(learnt_clause[0]);
            }else{
                CRef cr = ca.alloc(learnt_clause, true);
                ca[cr].set_lbd(lbd);
                //duplicate learnts 
                int  id = 0;
                if (lbd <= (signed)max_lbd_dup){                        
                    std::vector<uint32_t> tmp;
                    for (int i = 0; i < learnt_clause.size(); i++)
                        tmp.push_back(learnt_clause[i].x);
                    id = is_duplicate(tmp);             
                    if ((unsigned)id == min_number_of_learnts_copies +1){
                        duplicates_added_conflicts++;                        
                    }                    
                    if ((unsigned)id == min_number_of_learnts_copies){
                        duplicates_added_tier2++;
                    }                                        
                }
                //duplicate learnts
                learnts.push(cr);
                if ((lbd <= core_lbd_cut) || (id == (signed)min_number_of_learnts_copies+1)) ca[cr].mark(SMALL);
                else if ((lbd <= 6)||(id == (signed )min_number_of_learnts_copies)){
                    ca[cr].mark(MIDSZ);
                    ca[cr].touched() = conflicts;
                }else{
                    ca[cr].mark(LONG);
                    claBumpActivity(ca[cr]); 
                }
             
                attachClause(cr);

                uncheckedEnqueue(learnt_clause[0], backtrack_level, cr);
            }

            if (VSIDS) varDecayActivity();
            claDecayActivity();
        }else{
            // NO CONFLICT
            bool restart = false;
            if (!VSIDS)
                restart = nof_conflicts <= 0;
            else if (!cached){
                restart = lbd_queue.full() && (lbd_queue.avg() * 0.8 > global_lbd_sum / conflicts_VSIDS);
                cached = true;
            }
            if (restart /*|| !withinBudget()*/){
                lbd_queue.clear();
                cached = false;
                // Reached bound on number of conflicts:
                cancelUntil(0);
                return l_Undef; }

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && !simplify())
                return l_False;

            if (conflicts >= next_T2_reduce){
                next_T2_reduce = conflicts + 10000;
                reduceDB_Tier2(); }
            if (conflicts >= next_L_reduce){
                next_L_reduce = conflicts + 15000;
                reduceDB(); }

            Lit next = lit_Undef;
            {
                // New variable decision:
                decisions++;
                next = pickBranchLit();

                if (next == lit_Undef)
                    // Model found:
                    return l_True;
            }

            // Increase decision level and enqueue 'next'
            newDecisionLevel();
            uncheckedEnqueue(next, decisionLevel());
        }
    }
}

/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...
 */

static double luby(double y, int x){

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

    while (size-1 != x){
        size = (size-1)>>1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}

static bool switch_mode = false;

uint32_t Solver::reduceduplicates(){
    uint32_t removed_duplicates = 0;
    std::vector<std::vector<uint64_t>> tmp;
    for (auto & outer_mp: ht){//variables
        for (auto &inner_mp:outer_mp.second){//sizes
            for (auto &in_in_mp: inner_mp.second){
                if (in_in_mp.second >= 2){
                //min_number_of_learnts_copies
                    tmp.push_back({(uint64_t)outer_mp.first,inner_mp.first, in_in_mp.first,in_in_mp.second});
                }
            }                    
         }
    }          
    removed_duplicates = dupl_db_size-tmp.size();  
    ht.clear();
    for (auto i=0;i< (signed)tmp.size();i++){
        ht[tmp[i][0]][tmp[i][1]][tmp[i][2]]=tmp[i][3];
    }
    return removed_duplicates;
}

// NOTE: assumptions passed in member-variable 'assumptions'.

lbool Solver::sim_solve()
{
    model.clear();
    conflict.clear();
    if (!ok) return l_False;
    if(distance_mode==0) DISTANCE=0;
    printf("c sim distance_mode:%d pivot_lit=%d \n",distance_mode,toIntLit(parallel_pivot));
    
    lbd_sum=0;

    double curTime = cpuTime();
  
    if( parallel_pivot != lit_Undef){
           if( value(parallel_pivot) == l_False) { ok=false; return l_False;}
           if( value(parallel_pivot) != l_True) {
                 uncheckedEnqueue(parallel_pivot);
                 CRef confl = propagate();
                 if (confl != CRef_Undef) { ok=false; return l_False;}
                 if(!simplify()) {ok=false; return l_False;}
           }
           else parallel_pivot=lit_Undef;
    }
  
    max_learnts               = nClauses() * learntsize_factor;
    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
    lbool   status            = l_Undef;

    add_tmp.clear();

    VSIDS = true;
    int init = 10000;
    while (status == l_Undef && init > 0 /*&& withinBudget()*/)
        status = search(init);
    VSIDS = false;

    duplicates_added_conflicts = 0;
    duplicates_added_minimization=0;
    duplicates_added_tier2 =0;    

    dupl_db_size=0;
    size_t dupl_db_size_limit = dupl_db_init_size;

    // Search:
    int curr_restarts = 0;
    uint64_t curr_props = 0;
    uint32_t removed_duplicates =0;
   
    int old_usize =0;
    uint64_t next_get=10000;
   
    while (status == l_Undef){
        if(canPause){
              if(isPause()){
                  cancelUntil(0);
                  cloneSolver();
                  setPause(false);
              }
        }
        if( parallel_pivot == lit_Undef){
              int m=FixedVars();
              for (int i = old_usize; i < m; i++) {
                   ok=parallelExportUnitClause(trail[i]);
                   if (!ok) return l_False;
              }
              old_usize = m;
        }
        if(conflicts>next_get){
            next_get = conflicts+10000;
            while(1){
                Lit uLit=getUnit();
                if( uLit == lit_Undef) break;
                if( value (uLit) == l_False){ ok=false; return l_False;}
                if( value (uLit) == l_True) continue;
                uncheckedEnqueue(uLit);
                CRef confl = propagate();
                if (confl != CRef_Undef) { ok=false; return l_False;}
            }
            while(1){
                 Lit p,q=lit_Undef;
                 getbin(p,q);
                 if( q == lit_Undef) break;
                 putbin(p, q);
            }
       }
 
        if (dupl_db_size >= dupl_db_size_limit){    
            if(distance_mode){
//Duplicate version
                 removed_duplicates = reduceduplicates();
                 dupl_db_size_limit*=1.1;
                 dupl_db_size -= removed_duplicates;
            }
        }   
        if (propagations - curr_props >  VSIDS_props_limit){
            curr_props = propagations;
            switch_mode = true;
            VSIDS_props_limit = VSIDS_props_limit + VSIDS_props_limit/10;
        }
    
        if (VSIDS){
            int weighted = INT32_MAX;
            status = search(weighted);
        }else{
            int nof_conflicts = luby(restart_inc, curr_restarts) * restart_first;
            curr_restarts++;
            status = search(nof_conflicts);
        }

        if (status != l_Undef) break;
        if (switch_mode){ 
            switch_mode = false;
            VSIDS = !VSIDS;
            
           // if (VSIDS)   printf("c simp Switched to VSIDS.\n");
           // else         printf("c simp Switched to LRB.\n");
           
            picked.clear();
            conflicted.clear();
            almost_conflicted.clear();
#ifdef ANTI_EXPLORATION
            canceled.clear();
#endif
        }
        
        if(OtherSolverFinished()) break;
    }

    if (status == l_True){
        ExtendCopyModel();
    }
    else if (status == l_False && conflict.size() == 0)  ok = false;
    cancelUntil(0);
    double finalTime = cpuTime();
    totalTime = finalTime-curTime;
    return status;
}


lbool Solver::pre_sim_solve()
{
    model.clear();
    conflict.clear();
    if (!ok) return l_False;
    if(distance_mode==0) DISTANCE=0;
    printf("c pre_sim distance_mode:%d pivot =%d \n",distance_mode,toIntLit(parallel_pivot));
   
    if( parallel_pivot != lit_Undef){
           if( value(parallel_pivot) == l_False) { ok=false; return l_False;}
           if( value(parallel_pivot) != l_True) {
                 uncheckedEnqueue(parallel_pivot);
                 CRef confl = propagate();
                 if (confl != CRef_Undef) { ok=false; return l_False;}
                 if(!simplify()) {ok=false; return l_False;}
           }
           else parallel_pivot=lit_Undef;
    }
    lbd_sum=0;

    double curTime = cpuTime();
    lbool   status = l_Undef;
    if(preMode){
        status = s_lift ();
        if(status == l_Undef) status = unhide ();
        if(status == l_Undef) status = distill(); 
        if(status == l_Undef) status = tarjan_SCC();
        if(status == l_Undef) status = transitive_reduction();
       if(status == l_Undef) status = s_eliminate ();
    }

    rebuildOrderHeap();
   
    max_learnts               = nClauses() * learntsize_factor;
    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
  
    add_tmp.clear();

 //   VSIDS = true;
  
    duplicates_added_conflicts = 0;
    duplicates_added_minimization=0;
    duplicates_added_tier2 =0;    

    dupl_db_size=0;
  
    // Search:
    int curr_restarts = 0;
    uint64_t curr_props = 0;
   
    int old_usize =0;
    uint64_t next_get=10000;
   
    while (status == l_Undef){
        if( parallel_pivot == lit_Undef){
              int m=FixedVars();
              for (int i = old_usize; i < m; i++) {
                   ok=parallelExportUnitClause(trail[i]);
                   if (!ok) return l_False;
              }
              old_usize = m;
        }
        if(conflicts>next_get){
            next_get = conflicts+10000;
            while(1){
                Lit uLit=getUnit();
                if( uLit == lit_Undef) break;
                if( value (uLit) == l_False){ ok=false; return l_False;}
                if( value (uLit) == l_True) continue;
                uncheckedEnqueue(uLit);
                CRef confl = propagate();
                if (confl != CRef_Undef) { ok=false; return l_False;}
            }
            while(1){
                 Lit p,q=lit_Undef;
                 getbin(p,q);
                 if( q == lit_Undef) break;
                 putbin(p, q);
            }
       }
 
        if (propagations - curr_props >  VSIDS_props_limit){
            curr_props = propagations;
            switch_mode = true;
            VSIDS_props_limit = VSIDS_props_limit + VSIDS_props_limit/10;
        }
    
        if (VSIDS){
            int weighted = INT32_MAX;
            status = search(weighted);
        }else{
            int nof_conflicts = luby(restart_inc, curr_restarts) * restart_first;
            curr_restarts++;
            status = search(nof_conflicts);
        }

        if (status != l_Undef) break;
/*
        if (switch_mode){ 
            switch_mode = false;
            VSIDS = !VSIDS;
            
            if (VSIDS)   printf("c pre Switched to VSIDS.\n");
            else         printf("c pre Switched to LRB.\n");
           
            picked.clear();
            conflicted.clear();
            almost_conflicted.clear();
#ifdef ANTI_EXPLORATION
            canceled.clear();
#endif
        }
  */      
        if(OtherSolverFinished()) break;
    }

    if (status == l_True){
        ExtendCopyModel();
    }
    else if (status == l_False && conflict.size() == 0)  ok = false;
    cancelUntil(0);
    double finalTime = cpuTime();
    totalTime = finalTime-curTime;
    return status;
}

// abcdSAT =================================================================

#include "core/Solver_Mix.h"

lbool Solver :: mix_solve()
{    
    model.clear();
    conflict.clear();
    if (!ok) return l_False;
 
    printf("c mix distance_mode:%d pivot=%d \n",distance_mode,toIntLit(parallel_pivot));
    
    if( parallel_pivot != lit_Undef){
           if( value(parallel_pivot) == l_False) { ok=false; return l_False;}
           if( value(parallel_pivot) != l_True) {
                 uncheckedEnqueue(parallel_pivot);
                 CRef confl = propagate();
                 if (confl != CRef_Undef) { ok=false; return l_False;}
                 if(!simplify()) {ok=false; return l_False;}
           }
           else parallel_pivot=lit_Undef;
    }
  
    int i,j;

    Solver_Mix * m_solver=new Solver_Mix();
   
    m_solver->var_decay = var_decay;

    for (i=1; i <= nVars(); i++) m_solver->newVar();
  
    vec<Lit> lits;
    for (i =0; i < clauses.size(); i++){
           Clause & c = ca[clauses[i]];
 	       int sz=c.size();
	       lits.clear();
           for (j = 0; j < sz; j++) {
		        Lit p=c[j];
          	    if (value(p) == l_True) goto nextc;
		        if (value(p) == l_False) continue;
	            lits.push(p);
	       }
           if(!m_solver->addClause_(lits)){
                delete m_solver;
                return l_False;
           }
         nextc:  ;
    }
    lbool   status = l_Undef;
        
    int old_usize =0;
    uint64_t next_get=10000;
    // Search:
    int curr_restarts = 0;
    uint64_t curr_props = 0;
    m_solver->VSIDS = true;
    while (status == l_Undef){
        if( parallel_pivot == lit_Undef){
              int m=m_solver->FixedVars();
              for (int i = old_usize; i < m; i++) {
                   ok=parallelExportUnitClause(m_solver->trail[i]);
                   if (!ok) return l_False;
              }
              old_usize = m;
        }
        if(m_solver->conflicts>next_get){
            next_get = m_solver->conflicts+10000;
            while(1){
                Lit uLit=getUnit();
                if( uLit == lit_Undef) break;
                if( m_solver->value (uLit) == l_False){ ok=false; return l_False;}
                if( m_solver->value (uLit) == l_True) continue;
                m_solver->uncheckedEnqueue(uLit);
                CRef confl = m_solver->propagate();
                if (confl != CRef_Undef) { ok=false; return l_False;}
            }
            while(1){
                 Lit p,q=lit_Undef;
                 getbin(p,q);
                 if( q == lit_Undef) break;
                 m_solver->putbin(p, q);
            }
        }
        propagations = m_solver->propagations;
        if (propagations - curr_props >  VSIDS_props_limit){
            curr_props = propagations;
            switch_mode = true;
            VSIDS_props_limit = VSIDS_props_limit + VSIDS_props_limit/10;
        }     
        if (m_solver->VSIDS){
                int weighted = INT32_MAX;
                status = m_solver->search(weighted);
        }else{
                int nof_conflicts = luby(restart_inc, curr_restarts) * restart_first;
                curr_restarts++;
                status = m_solver->search(nof_conflicts);
        }
        conflicts = m_solver->conflicts;
        starts  = m_solver->starts;
   
        if (switch_mode){ 
                switch_mode = false;
                m_solver->VSIDS = !m_solver->VSIDS;

              //  if (m_solver->VSIDS) printf("c Mix Switched to VSIDS.\n");
              //  else                 printf("c Mix Switched to LRB.\n");
              //  fflush(stdout);

                 m_solver->picked.clear();
                 m_solver->conflicted.clear();
                 m_solver->almost_conflicted.clear();
#ifdef ANTI_EXPLORATION
                 m_solver->canceled.clear();
#endif
        }
    }
    
    if(status == l_True || status == l_Undef) {
           for (i=1; i <= nVars(); i++){
                  if(assigns[i-1] != l_Undef) continue;
                  if(status == l_True) assigns[i-1]= m_solver->assigns[i-1];
            }
    }
    if (status == l_True)  ExtendCopyModel();
   // double finalTime = cpuTime();
   // totalTime = finalTime-curTime;
  
    delete m_solver;
    return status;
}

//=================================================================================================
// Writing CNF to DIMACS:
// 
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var>& map, Var& max)
{
    if (map.size() <= x || map[x] == -1){
        map.growTo(x+1, -1);
        map[x] = max++;
    }
    return map[x];
}


void Solver::toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max)
{
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max)+1);
    fprintf(f, "0\n");
}


void Solver::toDimacs(const char *file, const vec<Lit>& assumps)
{
    FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}


void Solver::toDimacs(FILE* f, const vec<Lit>& assumps)
{
    // Handle case when solver is in contradictory state:
    if (!ok){
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return; }

    vec<Var> map; Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]]))
            cnt++;

    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])){
            Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False)
                    mapVar(var(c[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumptions.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumptions.size(); i++){
        assert(value(assumptions[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumptions[i]) ? "-" : "", mapVar(var(assumptions[i]), map, max)+1);
    }

    for (int i = 0; i < clauses.size(); i++)
        toDimacs(f, ca[clauses[i]], map, max);

    if (verbosity > 0)
        printf("c Wrote %d clauses with %d variables.\n", cnt, max);
}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator& to)
{
    // All watchers:
    //
    // for (int i = 0; i < watches.size(); i++)
    watches.cleanAll();
    watches_bin.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);
            // printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
            vec<Watcher>& ws = watches[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
            vec<Watcher>& ws_bin = watches_bin[p];
            for (int j = 0; j < ws_bin.size(); j++)
                ca.reloc(ws_bin[j].cref, to);
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
        Var v = var(trail[i]);

        if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
            ca.reloc(vardata[v].reason, to);
    }

    // All learnt:
    //
   for (int i = 0; i < learnts.size(); i++)
        ca.reloc(learnts[i], to);
  
    // All original:
    //
    int i, j;
    for (i = j = 0; i < clauses.size(); i++)
        if (ca[clauses[i]].mark() != 1){
            ca.reloc(clauses[i], to);
            clauses[j++] = clauses[i]; }
    clauses.shrink(i - j);
}


void Solver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted());

    relocAll(to);
    if (verbosity >= 2)
        printf("c |  Garbage collection:   %12d bytes => %12d bytes             |\n",
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}

void Solver :: verify()
{
    for (int i = 0; i < clauses.size(); i++){
        Clause& c = ca[clauses[i]];
        if (!satisfied(c)){
            printf("c {");
            for (int j = 0; j < c.size(); j++){
               if(sign(c[j])) printf("-");
               printf("%d", var(c[j])+1);
               if(value(c[j]) == l_True) printf(":1 ");
               else printf(":0 ");
            }
            printf(" }\n");
            exit(0);
        }
    }   
    if (verbosity > 0) printf("c internal verified \n");
}

void  Solver :: s_extend ()
{
  printf("c elimination extend.sz=%d \n",extendRemLit.size());
  Lit lit;
  if (equhead){
       equlinkmem();
       for(int i=0; i<extendRemLit.size(); i++){
          lit = extendRemLit[i];
          if (lit==lit_Undef) continue;
          int cv=var(lit)+1;
          if(equhead[cv] && equhead[cv]!=cv){
                int elit =  equhead[cv];
                Lit eqLit = makeLit(elit);
                if(sign(lit)) extendRemLit[i]= ~eqLit;
                else  extendRemLit[i]= eqLit;
                if (value (eqLit) == l_Undef ) assigns[var(eqLit)] = lbool(!sign(eqLit));
          }
      }
  }

  Lit next = lit_Undef;
  while (extendRemLit.size()) {
     int satisfied = 0;
     do {
          lit = next;
          next = extendRemLit.pop_();
          if (lit==lit_Undef || satisfied) continue;
          if ( value (lit) == l_True ) satisfied = 1;
     } while (next != lit_Undef);
     if (satisfied) continue;
     int cv=var(lit);
     assigns[cv] = lbool(!sign(lit));
  }
}

void Solver:: solveEqu(int *equRepr, int equVars, vec<lbool> & Amodel)
{   
   if(equRepr==0) return;
   if (verbosity > 0) printf("c solve Equ Vn=%d \n",equVars);
   for (int i=1; i <= equVars; i++){
         if(equRepr[i]==0 || equRepr[i]==i) continue;
         int v=equRepr[i];
         v=ABS(v)-1;
         Amodel[i-1] = l_False;
         if (Amodel[v] == l_Undef) Amodel[v] = l_True;
         if (Amodel[v] == l_True){
                   if(equRepr[i] > 0) Amodel[i-1] = l_True;
         }
         else      if(equRepr[i] < 0) Amodel[i-1] = l_True;
    }
}
//abcdSAT ========================================================
inline void Solver :: simpAddClause(const vec<Lit>& lits)
{
     CRef cr = ca.alloc(lits, false);
     clauses.push(cr);
     attachClause(cr);
}

CRef Solver::unitPropagation(Lit p)
{
     uncheckedEnqueue(p);
     CRef confl = simplePropagate();
     return confl;
}

bool Solver :: is_conflict(vec<Lit> & lits)
{  
   simpleCancelUntil(0);
   int i;
   for (i=0; i<lits.size(); i++){
        Lit p = ~lits[i];
        if ( value(p) == l_True) continue;
        if ( value(p) == l_False) break;
        newDecisionLevel();
        uncheckedEnqueue(p);
        CRef confl = simplePropagate();
        if (confl != CRef_Undef) break;
   }
   simpleCancelUntil(0);
   if(i<lits.size()) return true;
   return false;
}

bool Solver :: is_conflict(Lit p, Lit q)
{
      vec<Lit> ps;
      ps.push(p);
      ps.push(q);
      return is_conflict(ps);
}

// a bin clasue exists?
bool Solver::hasBin(Lit p, Lit q)
{
    vec<Watcher>&  wbin  = watches_bin[~p];
    for(int k = 0;k<wbin.size();k++) {
	  Lit imp = wbin[k].blocker;
	  if( imp == q) return true;
    }
    return false;
}	  
/*
inline void Solver::setmark(vec<int> & liftlit)
{   liftlit.clear();
    for (int c = trail.size()-1; c >= trail_lim[0]; c--) {
            int lit=toInt(trail[c]);
            mark[lit]=1;
            liftlit.push(lit);
    }
    simpleCancelUntil(0);
}
*/
/*
inline void Solver::clearmark(vec<int> & liftlit)
{
     for (int i =0; i < liftlit.size(); i++) mark[liftlit[i]]=0;
}
*/
/*
lbool Solver:: addequ(Lit p, Lit q)
{ 
    int pul=toInt(p);
    int qul=toInt(q);
 
    if(pul == qul)  return l_Undef;
    if(pul == (qul^1)) return l_False;

    touchVar.push(var(p));
    touchVar.push(var(q));
    return add_equ_link(pul,qul);
}
*/
void Solver:: equlinkmem()
{
    if (equMemSize >= nVars()+1) return;
    int oldsize=equMemSize;
    equMemSize = nVars()+1;
    if(equhead == 0){
          equhead = (int * ) calloc (equMemSize, sizeof(int));
          equlink = (int * ) calloc (equMemSize, sizeof(int));
          return;
    }
    equhead = (int * )realloc ((void *)equhead, sizeof(int)*equMemSize);
    equlink = (int * )realloc ((void *)equlink, sizeof(int)*equMemSize);
    for(int i=oldsize; i<equMemSize; i++) equhead[i]=equlink[i]=0;
} 

lbool Solver:: add_equ_link(int pul, int qul)
{
    equlinkmem();
    if( pul < qul){
       int t=pul;  pul=qul;  qul=t;
    }
    int pl=toIntLit(toLit(pul));
    int ql=toIntLit(toLit(qul));

    if(pl<0){ pl=-pl; ql=-ql; }
    int qv=ABS(ql);
    if(equhead[pl] == equhead[qv]){
        if(equhead[pl] == 0){
           equhead[pl]=ql; equhead[qv]=qv;
           equlink[qv]=pl;
           equsum++;
           return l_Undef;
        }
        if(ql < 0) return l_False;
        return l_Undef;
    }
    if(equhead[pl] == -equhead[qv]){
        if(ql < 0) return l_Undef;
        return l_False;
    }
    equsum++;
    if(equhead[pl] == 0 && equhead[qv]){
        if(ql < 0) equhead[pl]=-equhead[qv];
        else equhead[pl]=equhead[qv];
        int h=ABS(equhead[pl]);
        int t = equlink[h];
        equlink[h]=pl;
        equlink[pl]=t;
        return l_Undef;
    }
    if(equhead[pl] && equhead[qv]==0){
        if(ql < 0) equhead[qv]=-equhead[pl];
        else equhead[qv]=equhead[pl];
        int h=ABS(equhead[qv]);
        int t = equlink[h];
        equlink[h]=qv;
        equlink[qv]=t;
        return l_Undef;
    }
//merge
    int x=equhead[pl];
    int y=equhead[qv];
    if(ql < 0) y=-y;
    int next=ABS(y);
    while(1){
         if(equhead[next]==y) equhead[next]=x;
         else  equhead[next]=-x;
         if(equlink[next]==0) break;
         next=equlink[next];
    }    
    int xh=ABS(x);
    int t=equlink[xh];
    equlink[xh]=ABS(y);
    equlink[next]=t;
    return l_Undef;
}

void Solver:: buildEquClause()
{   vec<Lit> lits;
    if(equhead==0) return;
 
    if(dummyVar == 0)  dummyVar = (char * ) calloc (nVars()+1, sizeof(char));
    equlinkmem();
    for (int i=1; i <= nVars(); i++){
         if(equhead[i]==0 || equhead[i]==i || dummyVar[i]) continue;
         Lit p=mkLit(i-1);
         int lit=equhead[i];
         dummyVar[i]=1;
         Lit q = (lit>0) ? mkLit(lit-1) : ~mkLit(-lit-1);
         if( !hasBin(p, ~q) ) {
                lits.clear();
                lits.push(p);
                lits.push(~q);
                simpAddClause(lits);
         }
         if(!hasBin(~p, q) ) {
                lits.clear();
                lits.push(~p);
                lits.push(q);
                simpAddClause(lits);
         }
    }
}


lbool Solver::removeEqVar(vec<CRef>& cls, bool learntflag)
{
    vec<Lit> newCls;
    int i, j,k,n;

    lbool ret=l_Undef;
    equlinkmem();
    
    for (i = j = 0; i < cls.size(); i++){
        Clause& c = ca[cls[i]];
        if(c.mark()) continue;
        if(ret!=l_Undef){
            cls[j++] = cls[i];
            continue;
        }
        newCls.clear();
        int T=0;
        int del=0;
        for (k = 0; k < c.size(); k++){
             Lit p=c[k];
             if (value(p) == l_True) {
                    del=T=1; 
                    break;
             }
             if (value(p) == l_False){
                     del=1; 
                     continue;
             }
             int v = var(p)+1;
             Lit q;
             if(equhead[v]==0 || equhead[v]==v) q=p;
             else{ int lit;
                 if(sign(p)) lit = -equhead[v];
                 else        lit = equhead[v];
                 q = (lit>0) ? mkLit(lit-1) : ~mkLit(-lit-1);
                 del=1;
            }
             if(del){
                for(n=newCls.size()-1; n>=0; n--){
                   if( q  == newCls[n]) break;
                   if( ~q == newCls[n]) {T=1; break;}
                }
             }
             else n=-1;
             if(T) break;
             if(n<0) newCls.push(q);
        }
        if(del==0){
            cls[j++] = cls[i];
            continue;
        }
        if(T){
           removeClause(cls[i]);
           continue;
        }
        if(touchMark && newCls.size()<3){
            for (k = 0; k < newCls.size(); k++) touchMark[var(newCls[k])]=1;
        }
        if(newCls.size()==0){
              cls[j++] = cls[i];
              ret=l_False;
              continue;
       }
       if(newCls.size()==1){
              removeClause(cls[i]);
              if( unitPropagation(newCls[0]) != CRef_Undef ) ret=l_False;
              unitsum++;
              continue;
       }
       removeClause(cls[i]);
       CRef cr = ca.alloc(newCls, learntflag);
       attachClause(cr);
       cls[j++] = cr;
    }
    cls.shrink(i - j);
    checkGarbage();
    return ret; 
}
/*
bool Solver:: addbinclause(Lit p, Lit q)
{
      if(hasBin(p,q)) return true;
      vec<Lit> ps;
      ps.clear();
      ps.push(p);
      ps.push(q);
      if(is_conflict(ps)){
           CRef cr = ca.alloc(ps, false);
           clauses.push(cr);
           attachClause(cr);
           return true;
      }
      return false;
}
*/

void Solver:: addbinclause2(Lit p, Lit q, CRef & cr, int learntflag)
{
      vec<Lit> ps;
      ps.push(p);
      ps.push(q);
      cr = ca.alloc(ps, learntflag);
      attachClause(cr);
}

bool Solver:: out_binclause(Lit p, Lit q)
{
      if(hasBin(p,q)) return true;
      vec<Lit> ps;
      ps.clear();
      ps.push(p);
      ps.push(q);
      if(is_conflict(ps)) return true;
      return false;
}

lbool Solver::replaceEqVar()
{  
     watches.cleanAll();
     watches_bin.cleanAll();
     if(equhead==0) return l_Undef;
    
     lbool ret=removeEqVar(clauses, false);
     if(ret == l_False) return l_False;
     ret=removeEqVar(learnts, true);
     watches.cleanAll();
     watches_bin.cleanAll();
     return ret;
}
/*
lbool Solver::probeaux()
{    
     int old_equsum = equsum;
     for (int i = 0; i<clauses.size() && i<400000; i++){
           Clause & c = ca[clauses[i]];
 	   int sz=c.size();
           if(sz!=3) continue;
	   int tcnt=0;
           for (int j = 0; j < sz; j++) {
                tcnt += touchMark[var(c[j])];
                if(value(c[j]) != l_Undef) goto next;
           }
           if(tcnt < 2) continue;
           if(simpleprobehbr (c) == l_False) return l_False;
next:      ;
     }
//lift
    vec<int> liftlit;
    vec<int> unit;
    int liftcnt;
    if(probeSum) liftcnt = nVars()/2;
    else liftcnt=10000;
    equlinkmem();
    for(int vv=0; vv<nVars() && liftcnt > 0; vv++){
	     if(touchMark[vv]==0) continue;
             if(assigns[vv] != l_Undef) continue;
             if(equhead)
                if(equhead[vv+1] && ABS(equhead[vv+1]) <= vv) continue;

            Lit p = mkLit(vv);
            int pos=watches_bin[p].size();
            int neg=watches_bin[~p].size();

            if(pos==0 || neg==0) continue;
            liftcnt--;
            if(pos < neg) p=~p;
            CRef confl=trypropagate(p);
            if (confl != CRef_Undef){
                    simpleCancelUntil(0);
                    if(value(p) != l_Undef) continue; 
                    confl=unitPropagation(~p);
                    if (confl != CRef_Undef) return l_False;
                    unitsum++;
                    continue;
            }
            setmark(liftlit);
            confl=trypropagate(~p);
            if (confl != CRef_Undef){
                    simpleCancelUntil(0);
                    clearmark(liftlit);
                    if(value(p) != l_Undef) continue;
                    unitPropagation(p);
                    unitsum++;
                    continue;
            }
            unit.clear();
            vec<Lit> eqLit;
            eqLit.clear();
            for (int c = trail.size()-1; c > trail_lim[0]; c--) {//not contain p
                 int lit=toInt(trail[c]);
                 if(mark[lit]) unit.push(lit);
                 else{
                      if(mark[lit^1]) {//equ p=~lit
                          Lit q = ~trail[c];//~toLit(lit); 
                          eqLit.push(q);
                          unit.push(lit);
                       }
                 }
             }
            clearmark(liftlit);
            simpleCancelUntil(0);
//p=q
             for (int i =0; i< eqLit.size(); i++) {
                     Lit q=eqLit[i];
                     lbool ret=addequ(p,q);
                     if(ret == l_False) return l_False;
            }
//unit  
            for (int i =0; i < unit.size(); i++){
                  int lit=unit[i];
              	  Lit uLit=toLit(lit);
	          if(value(uLit) != l_Undef) continue;
                  if(!addbinclause(p,  uLit)) continue;
                  if(!addbinclause(~p, uLit)) continue;
                  confl=unitPropagation(uLit);
                  if (confl != CRef_Undef) return l_False;
                  unitsum++;
            }
   }
  
   for (int i =0; i < nVars(); i++) {
         touchMark[i]=0;
         if(equhead){
             int exv=i+1;
             if(equhead[exv]==0 || equhead[exv]==exv) continue;
         }
         decision[i]=1;
   }
  
   for (int i =0; i < touchVar.size(); i++) touchMark[touchVar[i]]=1;
   if(old_equsum != equsum) return replaceEqVar();
   return l_Undef;
}

lbool Solver::probe()
{    if(verbosity>0) printf("c probe \n");
    
     lbool ret=l_Undef;
     count = (int* ) calloc (2*nVars()+1, sizeof(int));
     litsum = (int* ) calloc (2*nVars()+1, sizeof(int));
     mark = (char * ) calloc (2*nVars()+1, sizeof(char));
     touchMark = (char *) malloc(sizeof(char) * (nVars()+1));

     for (int i =0; i < nVars(); i++)  touchMark[i]=1;
     int nC=nClauses();
     nC += (nC/2);
     int m=0;
     if(hbrsum > 1000 && conflicts>5000000 || (conflicts>300000)) goto noprobe;
     while(hbrsum<nC){
          m++;
          touchVar.clear();
          int oldhbr=hbrsum;
          int oldequ=equsum;
          int olduni=unitsum;
          ret=probeaux();
          if(ret == l_False) break;
          if(probeSum>3 || conflicts>100000 && m>25000) break;        
          if(oldhbr==hbrsum && oldequ==equsum && olduni==unitsum) break;
      }
noprobe:
     if(verbosity>0) printf("c hyper bin resol#=%d equ#=%d uni#=%d \n",  hbrsum,equsum,unitsum);
    
     touchVar.clear();
     free(count);
     free(litsum);
     free(mark);
     free(touchMark);
     touchMark=0;
     probeSum++;
     return ret;
}
*/

extern int nVarsB;
extern int sumLit;

//----------------------------------------------------------------
// find equivalent literals by 
//Tarjan's strongly connected components algorithm, dfsi: depth first search index
lbool Solver :: tarjan_SCC () 
{
  int * dfsimap, * min_dfsimap, lit;
  int dfsi, mindfsi, repr,olit;
  lbool ret=l_Undef;
  int nvar=nVars();

  dfsimap      = (int* ) calloc (2*nvar+1, sizeof(int));
  min_dfsimap  = (int* ) calloc (2*nvar+1, sizeof(int));
  dfsimap     += nvar;
  min_dfsimap += nvar;
  watches_bin.cleanAll();

  vec<int>  stk,component;
  stk.clear();  component.clear();
  dfsi = 0;
  int eqvNum=0;
  for (int idx = 1; idx <= nvar; idx++) {
     if(assigns[idx-1] != l_Undef) continue;
     for (int sign = -1; sign <= 1; sign += 2) {
        lit = sign * idx;
        if (dfsimap[lit]) continue;
        stk.push(lit);
        while (stk.size()>0) {
	    lit = stk.pop_();
            if (lit) {
	        if (dfsimap[lit]) continue;
	        dfsimap[lit] = min_dfsimap[lit] = ++dfsi;
	        component.push(lit);
	        stk.push(lit);
                stk.push(0);
		Lit Lt = makeLit(lit);
                vec<Watcher>&  bin  = watches_bin[Lt];
                for(int k = 0;k<bin.size();k++) {
	             Lit other = bin[k].blocker;
                     int olit = toIntLit(other);
                     if(dfsimap[olit]) continue;
	             stk.push(olit);
	        }  
            } 
            else {
	        lit = stk.pop_();
                mindfsi = dfsimap[lit];
		Lit Lt = makeLit(lit);
                vec<Watcher>&  bin  = watches_bin[Lt];
                for(int k = 0;k<bin.size();k++) {
	             Lit other = bin[k].blocker;
                     int olit = toIntLit(other);
                     if (min_dfsimap[olit] < mindfsi) mindfsi = min_dfsimap[olit];
	        }   
                if (mindfsi == dfsimap[lit]) {
                      repr = lit;
                      for (int k = component.size()-1; (olit =component[k]) != lit; k--) {
	                  if (ABS(olit) < ABS(repr)) repr = olit;
	              }
	              Lit p=makeLit(repr);
                      while ((olit = component.pop_()) != lit) {
	                   min_dfsimap[olit] = INT_MAX;
	                   if (olit == repr) continue;
	                   if (olit == -repr) {//empty clause 
                                 ret =l_False; 
	                          goto DONE;
                            }
                            Lit q=makeLit(olit);
                            ret = check_add_equ (p, q);
                            if(ret == l_False){
                                  goto DONE;
                            }
                            eqvNum++;
                      }
                      min_dfsimap[lit] = INT_MAX;
     	       } 
               else min_dfsimap[lit] = mindfsi;
	  }
        }
      }
  }
DONE:
  dfsimap     -= nvar;
  min_dfsimap -= nvar;
  free(dfsimap);
  free(min_dfsimap);
  if(ret == l_False) return ret;
 // printf("c tarjan SCC eqvNum=%d equsum=%d \n",eqvNum,equsum);
  if(eqvNum>0){
      touchMark=0;   
      return replaceEqVar();
  }
  return l_Undef;
}

typedef struct RNG { unsigned z, w; } RNG;
RNG rng;
unsigned s_rand () 
{
  unsigned res;
  rng.z = 36969 * (rng.z & 65535) + (rng.z >> 16);
  rng.w = 18000 * (rng.w & 65535) + (rng.w >> 16);
  res = (rng.z << 16) + rng.w;
  return res;
}

void init_rand_seed () 
{
  rng.w = 0;
  rng.z = ~rng.w;
  rng.w <<= 1;
  rng.z <<= 1;
  rng.w += 1;
  rng.z += 1;
  rng.w *= 2019164533u, rng.z *= 1000632769u;
}

unsigned s_gcd (unsigned a, unsigned b) {
  unsigned tmp;
//  if (a < b) SWAP2 (a, b);
  if (a < b) Swap (a, b);
  while (b) tmp = b, b = a % b, a = tmp;
  return a;
}

lbool Solver :: distill() 
{
  unsigned int pos, i, bin, delta, ncls;
  ncls = clauses.size(); 
  vec<CRef>& cs = clauses;
  for (i = bin=0; i < ncls; i++){
        Clause& c = ca[cs[i]];
        if(c.size()>2) continue;
        if(bin != i ){
             CRef tmp = cs[bin];
             cs[bin]  = cs[i];
             cs[i]    = tmp;
        }
        bin++;
  }
  
  unsigned int mod=ncls-bin;
  if (!mod)  return l_Undef;
  pos   = s_rand () % mod;
  delta = s_rand () % mod;
  if (!delta) delta++;
  while (s_gcd (delta, mod) > 1)   if (++delta == mod) delta = 1;
 
  for (i = bin; i < ncls; i++){
        unsigned int k=bin+pos;
        CRef tmp= cs[i];
        cs[i]   = cs[k];
        cs[k]   = tmp;
        pos = (pos+delta) % mod;
  }
  lbool ret=distillaux(clauses, 0);
  return ret;
}

void Solver::distill_analyze(vec<Lit> & out_clause, Lit p)
{
    vec<Var> scan,visit;
    out_clause.push(p); 
    scan.push(var(p)); 
    seen[var(p)]=1;
    visit.push(var(p));
    while(scan.size()>0){
  	Var qv=scan.pop_();
        CRef  confl = reason(qv);
        if( confl != CRef_Undef ){
               Clause & c = ca[confl];
               for (int i =0; i < c.size(); i++){
                    p = c[i];
                    Var pv= var(p);    
                    if (seen[pv]) continue;
                    seen[pv]=1;
                    visit.push(pv);
                    if( reason(pv) != CRef_Undef) scan.push(pv);
                    else  out_clause.push(p);
                } 
         }
    }
   // for (int c = trail_lim[0]; c<trail.size(); c++)  seen[var(trail[c])] = 0;
    for (int v = 0; v<visit.size(); v++)  seen[visit[v]] = 0;
}

lbool Solver::distillaux(vec<CRef>& cls,int start)
{
    vec<Lit> newCls;
    int i,j,k,m=0;
    lbool ret=l_Undef;
    simpleCancelUntil(0);
    if(start+30000 < cls.size()) start=cls.size()-30000;
    for (i = j = start; i < cls.size(); i++){
        if(ret!=l_Undef){
            cls[j++] = cls[i];
            continue;
        }
        Clause& c = ca[cls[i]];
        newCls.clear();
        int T=0;
        int csize=c.size();
        for (k = 0; k < csize; k++){
             Lit p=c[k];
             if (value(p) == l_True) { T=1; break;}
             if (value(p) == l_False)  continue;
             newCls.push(p);
        }
        if(T){
           removeClause(cls[i]);
           continue;
        }

        if(newCls.size()==csize && csize>2){

             for (int k=0; k<csize; k++){
                  Lit p = newCls[k];
                  if ( value(p) == l_False ) {
                         newCls[k]=newCls[csize-1];
                         newCls.shrink_(1);
                         break;
                  }
                  if (value(p) == l_True) {
                        if(k>=csize-1){
                           if(m<20000){
                              m++;
                              newCls.clear();
                              distill_analyze(newCls, p);
                          }
                        }
                        else  newCls.shrink_(csize-k-1);
                        break;
                  } 
                  newDecisionLevel();
                  simpleUncheckEnqueue(~p);
                  CRef confl = simplePropagate();
                  if (confl != CRef_Undef) {
                      newCls.shrink_(csize-k-1);
                      break;
                 }
            }
            simpleCancelUntil(0);
        }

       if(newCls.size()>=csize){
               cls[j++] = cls[i];
               continue;
       }
       if(newCls.size()==0){
              cls[j++] = cls[i];
              ret=l_False;
              continue;
       }
       if(newCls.size()==1){
              cls[j++] = cls[i];
              if( unitPropagation(newCls[0]) != CRef_Undef ) ret=l_False;
              unitsum++;
              continue;
       }
       removeClause(cls[i]);
       CRef cr = ca.alloc(newCls, false);
       attachClause(cr);
       cls[j++] = cr;
    }

    cls.shrink(i - j);
    checkGarbage();
    return ret; 
}

int  Solver :: trdbin (Lit start, Lit target, int learntflag) 
{
  int res=0;  
  int ign=1;
  vec<Lit> scan;
  scan.push(start); 
  seen[var(start)]=2+sign(start);
  for(int i=0; i<scan.size(); i++){
       Lit lit = scan[i];
       if(assigns[var(lit)] != l_Undef) continue;
       vec<Watcher>&  bin  = watches_bin[lit];
       for(int k = 0;k<bin.size();k++) {
            Lit other = bin[k].blocker;
            CRef cr=bin[k].cref;
            Clause& c = ca[cr];
            if(c.mark()) continue;
            if(c.learnt() && learntflag==0) continue;
            if (other == start) continue;
            if (other == target) {
                 if (lit == start && ign) { ign = 0; continue; }
                 res = 1;
	         goto DONE;
            }
            int mark=2+sign(other);
            Var ov=var(other);
            if(seen[ov]==0){
                    seen[ov] = mark;
                    scan.push(other);
                    continue;
            } 
            if(seen[ov] != mark){
               if (value(start) != l_Undef) continue;
               newDecisionLevel();
               simpleUncheckEnqueue(start);
               CRef confl = simplePropagate();
               simpleCancelUntil(0);
        
               confl = unitPropagation(~start);
               if (confl != CRef_Undef) { res = -1; goto DONE;}
            } 
       }
  }        
DONE:
  for(int i=0; i<scan.size(); i++)  seen[var(scan[i])]=0;
  return res;
}

void Solver ::cleanClauses(vec<CRef>& cls)
{
    int i,j;
    for (i = j = 0; i < cls.size(); i++)
        if (ca[cls[i]].mark() == 0) cls[j++] = cls[i];
    cls.shrink(i - j);
}

void Solver :: cleanNonDecision()
{   int i,j;
    for (i = j = 0; i < learnts.size(); i++){
        CRef cr=learnts[i];
        Clause & c = ca[cr];
        if (c.mark()) continue;
        for (int k = 0; k < c.size(); k++){
             if (value(c[k]) == l_True || !decision[var(c[k])]) {
                    removeClause(cr);
                    goto NEXT;
             }
        }
        learnts[j++] = cr;
    NEXT: ;
    }   
    learnts.shrink(i -j);
}

lbool Solver :: trdlit (Lit start, int & remflag) 
{ 
  vec<Watcher>&  bin  = watches_bin[start];
  for(int k = 0;k<bin.size(); k++) {
         Lit target = bin[k].blocker;
         if (var (start) > var (target)) continue;
         CRef cr=bin[k].cref;
         Clause & c = ca[cr];
         if(c.mark()) continue;
         int ret = trdbin (start, target, c.learnt());
         if(ret < 0 ) return l_False;
         if(ret > 0 ) {
              removeClause(cr);
              remflag=1;
              break;
         }
  }
  return l_Undef;
}

//delete taut binary clause
lbool Solver :: transitive_reduction () 
{ int i;
//  printf("c transitive_reduction cls#=%d learnt=%d %d \n",clauses.size(),learnts.size(),clauses.size()+learnts.size());
  unsigned int pos,delta,v,mod=nVars();
  if (mod<20)  return l_Undef;
  pos     = s_rand () % mod;
  delta = s_rand () % mod;
  if (!delta) delta++;
  while (s_gcd (delta, mod) > 1)   if (++delta == mod) delta = 1;
  int remflag=0;
  lbool ret=l_Undef;
  simpleCancelUntil(0);
  i=nVars();
  if(i>5000) i=5000;
  for(; i>0; i--) {
        v= pos/2;
        if(assigns[v] == l_Undef){
             Lit lit = (pos & 1) ? mkLit(v) : ~mkLit(v);
             ret=trdlit (lit, remflag);
             if(ret != l_Undef) break;
        }
        pos = (pos+delta) % mod;
  }
  if(remflag) {
          cleanClauses(clauses);
          cleanClauses(learnts);
  }
 // printf("c transitive_reduction_end cls#=%d \n",clauses.size());
  return ret;
}

typedef struct DFPR  { int discovered, finished, parent, root;} DFPR;
typedef struct DFOPF { int observed, pushed, flag;} DFOPF;
DFOPF * dfopf;
DFPR * dfpr=0;

typedef struct DFL {
  int discovered, finished;
  int lit, sign;
} DFL;

typedef enum Wrag {
  PREFIX = 0,
  BEFORE = 1,
  AFTER = 2,
  POSTFIX = 3,
} Wrag;

typedef struct Work {
  Wrag wrag : 2;
  int lit : 30;
  int other : 30;
  unsigned red : 1;
  unsigned removed : 1;
  CRef cr;
} Work;

int Solver :: unhdhasbins (Lit lit, int irronly)
{
   vec<Watcher>&  bin  = watches_bin[~lit];
   for(int k = 0;k<bin.size();k++) {
         Lit other = bin[k].blocker;
         CRef cr=bin[k].cref;
         Clause& c = ca[cr];
         if(c.learnt() && irronly) continue;
         if( value(other) != l_Undef) continue;
         if (!dfpr[toInt(other)].discovered) return 1;
   }
   return 0;
}

inline void s_pushwork (vec<Work> & work, Wrag wrag, int lit, int other, int red,CRef cr=CRef_Undef) 
{
  Work w;
  w.wrag = wrag;
  w.other = other;
  w.red = red ? 1 : 0;
  w.removed = 0;
  w.lit = lit;
  w.cr  = cr;
  work.push(w);
}

int Solver :: s_stamp (Lit root, vec <int> &  units, int stamp, int irronly) 
{
  vec<Work> work;
  int observed, discovered, pos;
  unsigned start, end, mod, i, j;
  int startstamp=0;
  int uroot=toInt(root);
  if (dfpr[uroot].discovered) return stamp;
  s_pushwork (work, PREFIX, uroot, uroot, 0);

  vec <int> sccs;
  while (work.size()) {
      Work w = work.pop_();
      if (w.removed) continue;
      if (w.wrag == PREFIX) {
           if (dfpr[w.lit].discovered) {
	        dfopf[w.lit].observed = stamp;
                continue;
           }
           dfpr[w.lit].discovered = ++stamp;
           dfopf[w.lit].observed = stamp;
           if (!startstamp) {
        	startstamp = stamp;
         	dfpr[w.lit].root = w.lit;
           }
           s_pushwork (work, POSTFIX, w.lit, w.lit, 0);
           dfopf[w.lit].pushed = start = work.size();
           dfopf[w.lit].flag = 1;
           sccs.push(w.lit);
           Lit p=toLit(w.lit);
           vec<Watcher>&  bin  = watches_bin[p];
           for(int k = 0;k<bin.size();k++) {
                  Lit other = bin[k].blocker;
                  CRef cr=bin[k].cref;
                  Clause& c = ca[cr];
                  if(c.mark()) continue;
                  if(c.learnt() && irronly) continue;
                  if( value(other) != l_Undef) continue;
                  int uo=toInt(other);
                  if(mark[uo]) continue;
                  mark[uo]=1;
         	  s_pushwork (work, BEFORE, w.lit, uo, c.learnt(),cr);
           }
                
	   for(int k = start;k<work.size();k++) mark[work[k].other]=0;
           end = work.size();
	   mod = end - start;
           for (i = start; i < end - 1;  i++) {
	       j = s_rand () % mod--;
	       if (!j) continue;
	       j = i + j;
               Work tmp=work[i]; work[i] = work[j]; work[j] = tmp;
           }
     } else if (w.wrag == BEFORE) {// before recursive call,stamping edge %d %d before recursion", lit, other);
          s_pushwork (work, AFTER, w.lit, w.other, w.red);
          int Nother = w.other ^ 1; 
          if ( (irronly || w.red) && dfopf[w.other].observed > dfpr[w.lit].discovered) {
               //transitive edge %d %d during stamping", lit, other
               Clause & c = ca[w.cr];
               if(c.mark()==0) removeClause(w.cr);
               if ((pos = dfopf[Nother].pushed) >= 0) {           
                         int Nlit=w.lit^1;
                         while (pos  < work.size()) {
	                     if (work[pos].lit != Nother) break;
	                     if (work[pos].other == Nlit) {//removing edge %d %d from DFS stack", -other, -lit);
	                            work[pos].removed = 1;
	                      }
	                      pos++;
	                  }
	        }
                work.pop();
               	continue;
	   }
           observed = dfopf[Nother].observed;
           if ( startstamp <= observed) {//stamping failing edge %d %d, lit, other
	        int failed;
                for (failed = w.lit;  dfpr[failed].discovered > observed; failed = dfpr[failed].parent);
	        units.push(failed^1);
                if (dfpr[Nother].discovered && !dfpr[Nother].finished) {
                     work.pop();
                     continue;
	        }
           }
           if (!dfpr[w.other].discovered) {
	       dfpr[w.other].parent = w.lit;//stamping %d parent %d", other, lit
               dfpr[w.other].root   = uroot;//stamping %d root %d", other, root
	       s_pushwork (work, PREFIX, w.other, w.other, 0);
           }
    } else if (w.wrag == AFTER) {	// after recursive call. stamping edge %d %d after recursion, lit, other
         if (!dfpr[w.other].finished  && dfpr[w.other].discovered < dfpr[w.lit].discovered) {
                  //stamping back edge %d %d", lit, other
	         dfpr[w.lit].discovered = dfpr[w.other].discovered;
                      //stamping %d reduced discovered to %d",lit, dfpr[ulit].discovered);
	         dfopf[w.lit].flag = 0; // stamping %d as being part of a non-trivial SCC", lit
         }
         dfopf[w.other].observed = stamp;//stamping %d observed %d", other, stamp
    } else {//stamping postfix %d", lit
          if (dfopf[w.lit].flag) {
        	stamp++;
                discovered = dfpr[w.lit].discovered;
                int other;
	        do {
	             other = sccs.pop_();
	             dfopf[other].pushed = -1;
	             dfopf[other].flag = 0;
	             dfpr[other].discovered = discovered;
	             dfpr[other].finished = stamp;
                } while (other != w.lit);
         }
      }
  }
  return stamp;
}
//remove duplicated binary clause 
void Solver :: rmBinDup () 
{
  watches_bin.cleanAll();
  int redrem, irrem;
  redrem = irrem = 0;
  vec<int> scan;
  vec<CRef> delbin;
  for (int idx = 0; idx < nVars(); idx++) {
     for (int sign = -1; sign <= 1; sign += 2) {
         Lit lit = (sign > 0) ? mkLit(idx) : ~mkLit(idx);
         scan.clear();
         for (int round = 0; round < 2; round++) {
	     vec<Watcher>&  bin  = watches_bin[lit];
             delbin.clear();
             for(int k = 0;k<bin.size();k++) {
                  Lit other = bin[k].blocker;
                  CRef cr=bin[k].cref;
                  Clause & c = ca[cr];
                  if(c.mark()) continue;
                  if(c.learnt()    && round == 0) continue;
                  if(c.learnt()==0 && round )     continue;
                  if( value(other) != l_Undef) continue;
                  int uo=toInt(other);
                  if(mark[uo]) delbin.push(cr);
                  else { mark[uo]=1;
                         scan.push(uo);
         	  }
            }
            for(int k = 0;k<delbin.size();k++) removeClause(delbin[k]);
            if(round) redrem += delbin.size();
            else      irrem  += delbin.size();
         }
	 for(int k = 0;k<scan.size();k++) mark[scan[k]]=0;
      }
   }
   if(redrem) cleanClauses(learnts);
   if(irrem)  cleanClauses(clauses);
   watches_bin.cleanAll();
}

inline void find_relative_prime(unsigned & pos, unsigned & delta, unsigned mod)
{
      pos   = s_rand () % mod;
      delta = s_rand () % mod;
      if (!delta) delta++;
      while (s_gcd (delta, mod) > 1)   if (++delta == mod) delta = 1;
}

lbool Solver :: s_stampall (int irronly) 
{
  unsigned pos, delta, mod;
  int stamp, rootsonly;
  lbool ret = l_Undef;

  vec<int>  units;
 
  rmBinDup ();
  int nvar = nVars();
  dfpr  = (DFPR * ) calloc (2*nvar+1, sizeof(DFPR));
  dfopf = (DFOPF *) calloc (2*nvar+1, sizeof(DFOPF));

  for (DFOPF * q = dfopf; q < dfopf + 2*nvar+1; q++) q->pushed = -1;
  stamp = 0;
  for (rootsonly = 1; rootsonly >= 0; rootsonly--) {
      mod = 2*nvar;

     find_relative_prime(pos, delta, mod);
      //unhiding %s round start %u delta %u mod %u,(rootsonly ? "roots-only": "non-root"), pos, delta, mod);
      for (unsigned int i=0; i<mod; i++, pos = (pos+delta) % mod ) {
           Lit root = toLit(pos);
           if( value(root) != l_Undef) continue;
           if (dfpr[pos].discovered) continue;
           if (rootsonly && unhdhasbins (root, irronly)) continue;
           if (!unhdhasbins (~root, irronly)) continue;
           stamp = s_stamp (root, units, stamp, irronly);
           while (units.size()) {
	         int uo = units.pop_();
                 Lit lit = toLit (uo);
                 if( value(lit) != l_Undef) continue;
                 if(!checkUnit (uo, 'S')) continue;
                 CRef confl = unitPropagation(lit);
                 if (confl != CRef_Undef) { ret = l_False; goto DONE;}
 	   }
       }
  }
DONE:
  if (ret != l_Undef) { free(dfpr); dfpr = 0;}
  free(dfopf);
  return ret;
}

lbool Solver :: unhide () 
{ int irr_only=0;
  lbool ret = l_Undef;
  printf("c unhide \n");
  dfpr = 0;
  if (nVars() <20) return l_Undef;
  simpleCancelUntil(0);
  mark = (char * ) calloc (2*nVars()+1, sizeof(char));
  for(int round=0; round<2; round++) 
  {  
      ret = s_stampall (irr_only);
      if (ret != l_Undef) break;
      if (!dfpr) break;
      watches_bin.cleanAll();

      check_all_impl();

      ret=s_unhidefailed ();
      if (ret != l_Undef) break;

      ret=s_unhidebintrn (clauses, irr_only, 0);
      if (ret != l_Undef) break;
      ret=s_unhidebintrn (learnts, irr_only, 1);
      if (ret != l_Undef) break;

      ret= s_unhidelrg (clauses, irr_only, 0);
      if (ret != l_Undef) break;
      cleanClauses(clauses);

      ret= s_unhidelrg (learnts, irr_only, 1);
      cleanClauses(learnts);
      if (ret != l_Undef) break;
     
      irr_only = !irr_only;
      free (dfpr);
      dfpr=0;
  }
  rmBinDup ();
  free(mark);
  if (dfpr) free (dfpr);
  return ret;
}

static int s_unhimpl (int u, int v) {
//  int u = s_ulit (a), v = s_ulit (b),
  int c, d, f, g;
  c = dfpr[u].discovered; if (!c) return 0;
  d = dfpr[v].discovered; if (!d) return 0;
  f = dfpr[u].finished, g = dfpr[v].finished;
  return c < d && g < f;
}

int s_unhimplies2 (int a, int b) {
  return s_unhimpl (a, b) || s_unhimpl (b^1, a^1);
}

int s_unhimplincl (int u, int v) 
{
  int c, d, f, g;
  c = dfpr[u].discovered; if (!c) return 0;
  d = dfpr[v].discovered; if (!d) return 0;
  f = dfpr[u].finished, 
  g = dfpr[v].finished;
  return c <= d && g <= f;
}

int s_unhimplies2incl (int a, int b) {
  return s_unhimplincl (a, b) || s_unhimplincl (b^1, a^1);
}

lbool Solver :: s_unhidefailed () 
{
  int unit;
  for (int idx = 0; idx < nVars(); idx++) {
     for (int sign = -1; sign <= 1; sign += 2) {
         Lit lit = (sign > 0) ? mkLit(idx) : ~mkLit(idx);
         if( value(lit) != l_Undef) continue;
         unit=toInt(lit);
         if(!dfpr[unit^1].discovered) continue;
         if (s_unhimplincl (unit^1, unit)==0) {// unhiding %d implies %d", -lit, lit
                if (s_unhimplincl (unit, unit^1)==0) continue;//unhiding %d implies %d", lit, -lit
                lit = ~lit;
         }
         if(checkUnit (toInt(lit), 'F')){
               CRef confl = unitPropagation(lit);
               if (confl != CRef_Undef) return l_False;
        }
    }
  } 
  return l_Undef;
}

//unhiding least common ancestor of %d and %d is %d", a, b, p
int Solver :: s_unhlca (int a, int b) 
{
  int p;
  if (a == b) return a;
  if (dfpr[a].discovered <= dfpr[b].discovered) p = a;
  else { p = b; b=a; a=p; }
  for (;;) {
    if (dfpr[b].finished <= dfpr[p].finished) break;
    p = dfpr[p].parent;
    if (!p) break;
  }
  return p;
}

int s_unhroot (int ulit) { return dfpr[ulit].root;}

int Solver :: checkUnit (int uLit, char printflag)
{    (void)printflag;
     Lit unit=toLit(uLit^1);
     if(value(unit) == l_False) return 1;
     if(value(unit) == l_Undef) {
            newDecisionLevel();
            simpleUncheckEnqueue(unit);
            CRef confl = simplePropagate();
            simpleCancelUntil(0);
            if (confl != CRef_Undef) return 1;
     }
     //printf("c checkUnit %c  fail lit=%d \n",printflag, toIntLit(~unit));
     return 0;
}

void Solver :: checkBin (int uL1, int uL2,char printflag)
{    (void)printflag;
     Lit lit;
     for(int i=0; i<2; i++){
              if(i) lit=toLit(uL2^1);
              else lit=toLit(uL1^1);
              if(value(lit) == l_False) goto done;
              if(value(lit) == l_Undef) {
                   newDecisionLevel();
                   simpleUncheckEnqueue(lit);
                   CRef confl = simplePropagate();
                   if (confl != CRef_Undef) goto done;
              }
     }
       //  printf("c <Bin_%c <%d %d> fail \n",printflag,uL1,uL2);
done:
     simpleCancelUntil(0);
}

void Solver :: checklarg(vec <Lit> & cs, char type)
{     (void)type;
      int i;
      for(i=0; i<cs.size(); i++){
              if(value(cs[i]) == l_True)  break;
              if(value(cs[i]) == l_False) continue;
              newDecisionLevel();
              simpleUncheckEnqueue(~cs[i]);
              CRef confl = simplePropagate();
              if (confl != CRef_Undef) break;
      }
      //if(i>=cs.size()) printf("c large %c fail \n",type);
      simpleCancelUntil(0);
}

void Solver :: check_all_impl()
{ 
   int m=0;
   for (int i = 0; i < 2*nVars() && i<10000; i++) {
       for (int j = 0; j < 2*nVars() && i<10000; j++) {
             if(i==j) continue;
             if (s_unhimplincl (i, j)) {// i implies j
                   checkBin (i^1, j, 'L');
                   m++;
             }
        }
   }
  // printf("c check all %d impl \n",m);
}           
 
lbool Solver :: s_unhidebintrn (vec<CRef>& cls,int irronly,int learntflag)
{
  lbool ret=l_Undef;
  int i,j;
  vec<Lit> newCls,NewBin;
  int root,lca,ul,unit,other2;
	
  for (i = j = 0; i < cls.size(); i++){
        Clause & c = ca[cls[i]];
        if (c.mark()) continue;
        if(c.size()>3 || ret==l_False) goto next;
        ul=toInt(c[0]);
        unit=toInt(c[1]);
        if(c.size() == 2){
             if( value(c[0]) != l_Undef || value(c[1]) != l_Undef) goto next;
             if(!dfpr[ul].discovered) goto next;
             if (s_unhimplies2 (ul, unit)) {
                      if(!checkUnit (unit, 'A')) goto next;
RUNIT:               
                      removeClause(cls[i]);
UNIT:
                      CRef confl = unitPropagation(toLit(unit));
                      if (confl != CRef_Undef) ret=l_False;
                      continue;
	     }
             if (s_unhimplies2 (unit,ul)) {
                      unit=ul;
                      if(!checkUnit (unit, 'B')) goto next;
                      goto RUNIT;
             }
             if ((root = s_unhroot (ul^1)) && value(toLit(root)) == l_Undef && root == s_unhroot (unit^1)) { 
                      //negated literals in binary clause %d %d implied by %d",lit, other, root
                      int lca = s_unhlca (ul^1, unit^1);
                      if(lca==0) goto next;
	              unit = lca^1;
	              if(!checkUnit (unit, 'C')) goto next;
                      cls[j++] = cls[i];
                      goto UNIT;
             }
	     if (irronly==0 && learntflag==0)   goto next;
      	     if (dfpr[unit].parent == (ul^1))   goto next;
             if (dfpr[ul  ].parent == (unit^1)) goto next;
	     if (!s_unhimplies2 (ul^1, unit))   goto next;
             removeClause(cls[i]);
             continue;
        }
        if( value(c[2]) != l_Undef) goto next;
        other2=toInt(c[2]);

        if (s_unhimplies2incl (unit, ul) && s_unhimplies2incl (other2, ul)) {
	    //unit => ul  other2 => ul
            unit = ul;
            if(!checkUnit (unit, 'D')) goto next;
 	    goto RUNIT;
	}

        if ((root = s_unhroot (ul^1)) && value(toLit(root)) == l_Undef && root == s_unhroot (unit^1) && 
           root == s_unhroot (other2^1)) { 
        // root => ul^1 & unit^1  & other2^1;
	    lca = s_unhlca (ul^1, unit^1);
	    lca = s_unhlca (lca, other2^1);
	    if(lca==0) goto next;
            unit = lca^1;
            if(!checkUnit (unit, 'E')) goto next;
	    cls[j++] = cls[i];
            goto UNIT;
	 }
	 if ((learntflag || irronly) &&  (s_unhimplies2incl (ul^1, unit) || s_unhimplies2incl (ul^1, other2))) {
	   // (ul V unit) or (ul V others) => tautological
	    removeClause(cls[i]);
            continue;
         } 
	 if (s_unhimplies2incl (other2, ul)) {
             checkBin (ul, unit,'A');
TRNSTR://unhiding removal of literal %d with implication %d %d from ternary clause %d %d %d,
             removeClause(cls[i]);
             addbinclause2(toLit(ul), toLit(unit), cls[j], learntflag);
             j++;
            continue;
         }
         if (s_unhimplies2incl (unit, ul)) {
 	    unit=other2;
            checkBin (ul, unit,'B');
	    goto TRNSTR;
	 }
         if ((root = s_unhroot (ul^1)) &&  value(toLit(root)) == l_Undef) {
	      if (root == s_unhroot (other2^1)) {
	          lca = s_unhlca (ul^1, other2^1);
	      } else if (root == s_unhroot (unit^1)) {
	          lca = s_unhlca (ul^1, unit^1);
	          Swap(unit,other2);
	      } else if (s_unhimplies2incl (root, other2^1)) lca = root;
	        else if (s_unhimplies2incl (root, unit^1)) {
	                lca = root;
	                Swap(unit, other2);
	              } else goto next;
	    if (lca==0) goto next;
	    if ((lca/2) == (ul/2))     goto next;
	    if ((lca/2) == (unit/2))   goto next;
	    if ((lca/2) == (other2/2)) goto next;
	    if (s_unhimplies2incl (lca, unit)) goto next;
	   // (-lca V -ul) and (-lca V -other) => -lca V unit
              ul=lca^1;
              checkBin (ul, unit,'C');//bug
              if(NewBin.size()<1000){
                   Lit p=toLit(ul);
                   Lit q=toLit(unit);
                   if(!hasBin(p, q)){
                          NewBin.push(p);
                          NewBin.push(q);
                  }
              }
        }
next:
         cls[j++] = cls[i];
    }
    cls.shrink(i - j);
    while(NewBin.size()){
            newCls.clear();
            newCls.push(NewBin.pop_());
            newCls.push(NewBin.pop_());
            CRef cr = ca.alloc(newCls, learntflag);
            attachClause(cr);
            cls.push(cr);
    }
    return ret;
}

void * s_realloc (void * ptr, size_t old, size_t newsz) 
{
  void * res;
  if (ptr==0) res= malloc (newsz);
  else {
       if (!newsz) { free (ptr); return 0; }
       res = realloc (ptr, newsz);
  }
  if (newsz > old) memset ((char *)res + old, 0, newsz - old);
  return res;
}

void Adp_SymPSort(void *a, int n, int es, int (*cmp)(const void *,const void *));
int cmpdfl (const void * a, const void * b)
{  DFL * c =(DFL *)a;
    DFL * d =(DFL *)b;
    return c->discovered - d->discovered;
}

void sort(DFL * dfl,int n)
{
   Adp_SymPSort((void *)dfl, n, sizeof(DFL), cmpdfl);
}

lbool Solver :: s_unhidelrg (vec<CRef>& cls,int irronly,int learntflag)
{  int posdfl, negdfl, ndfl, szdfl = 0;
   int lca,nsize;
   int i,j,k,q,unit,satisfied,tautological,root,root1,root2,lca1,lca2;
   vec<Lit> newCls,bin;
   lbool ret=l_Undef;
   CRef confl,cr;
   DFL *eodfl,*d,*e, * dfl = 0;
   for (i = j = 0; i < cls.size(); i++){
        Clause & c = ca[cls[i]];
        if (c.mark()) continue;
        if(c.size() <=3 || ret==l_False) goto nextcls;
        posdfl = negdfl = satisfied = tautological = ndfl = 0;
        newCls.clear();
        for(k=0; k<c.size(); k++){
             Lit p=c[k];
             if (value(p) == l_True) {
                    satisfied = 1;
                    break;
             }
             if (value(p) == l_False) continue;
             newCls.push(p);
             if (dfpr[toInt(p)].discovered) posdfl++;	// count pos in BIG
             if (dfpr[toInt(p^1)].discovered) negdfl++;	// count neg in BIG
        }
        if (satisfied){
remSAT:
             removeClause(cls[i]);
             continue;
        }
        ndfl = posdfl + negdfl;	// number of literals in BIG
        nsize=newCls.size();
//FAILED: find root implying all negated literals
        if (nsize != negdfl) goto HTE;	// not enough complement lits in BIG
        lca = toInt(newCls[0])^1;
        root = s_unhroot (lca);
        if (!root) goto HTE; //????
        if (value(toLit(root)) != l_Undef) goto HTE;
        for(k=1; k<nsize && s_unhroot (toInt(newCls[k])^1) == root; k++);
        if (k < nsize) goto HTE; // at least two roots
        // lca => -x1, lca => -x2,,, lca => -xn  ==> -lca 
        for(k=1; k<nsize; k++) lca = s_unhlca (toInt(newCls[k])^1, lca);
        unit = lca^1;
        confl = unitPropagation(toLit(unit));
        if (confl != CRef_Undef) ret=l_False;
        goto nextcls;
HTE:    //hide tautology elim
        if (learntflag == 0 && !irronly) goto STRNEG; // skip tautology checking if redundant clauses used and
					   //  irredundant clauses
        if (posdfl < 2 || negdfl < 2) goto STRNEG;
        if (ndfl > szdfl){
             dfl = (DFL *)s_realloc (dfl, szdfl*sizeof(DFL), ndfl*sizeof(DFL));
             szdfl = ndfl;
        }
        ndfl = 0;

    // copy all literals and their complements to 'dfl'
        for(k=0; k<nsize; k++){
            for (int sign = 1; sign >=0; sign--) {
	      int ulit = toInt(newCls[k])^sign;
              if (!dfpr[ulit].discovered) continue;	// not in BIG so skip
	      dfl[ndfl].discovered = dfpr[ulit].discovered;
	      dfl[ndfl].finished = dfpr[ulit].finished;
	      dfl[ndfl].sign = sign;
	      dfl[ndfl].lit  = ulit;
	      ndfl++;
           }
        }
        sort(dfl, ndfl);
        eodfl = dfl + ndfl;
        for (d = dfl; d < eodfl - 1; d++)
             if (d->sign > 0) break;			// get first negative pos
        while (d < eodfl - 1) {
          for (e = d + 1; e < eodfl && e->finished < d->finished; e++) {
	          if (e->sign > 0) continue;		// next positive pos
	              //  d.lit => elit   ==>  tautological;
                 checkBin (d->lit^1, e->lit, 't');
                 goto remSAT;
               /*
                 removeClause(cls[i]);
                 bin.clear();
                 bin.push(toLit(d->lit^1));
                 bin.push(toLit(e->lit));
                 cr = ca.alloc(bin, learntflag);
                 attachClause(cr);
                 cls[i]=cr;
               //  cls[j++]=cr;
                 goto nextcls;
               */
          }
          for (d = e; d < eodfl && d->sign == 0; d++);
       }
STRNEG: //negative
      //????   if (!s_str (spf)) goto HBR;
       if (negdfl < 2) goto STRPOS;
       if (negdfl > szdfl) { 
           dfl = (DFL*)s_realloc (dfl, szdfl*sizeof(DFL), negdfl*sizeof(DFL));
           szdfl = negdfl; 
      }

      ndfl = 0;
    // copy complement literals to 'dfl'
      for(k=0; k<nsize; k++){
            int ulit = toInt(newCls[k])^1;
            if (!dfpr[ulit].discovered) continue;
	    dfl[ndfl].discovered = dfpr[ulit].discovered;
	    dfl[ndfl].finished = dfpr[ulit].finished;
	    dfl[ndfl].lit = ulit^1;
	    ndfl++;
      }
      if (ndfl < 2) goto STRPOS;
      sort(dfl, ndfl);
      eodfl = dfl + ndfl;
      for (d = dfl; d < eodfl - 1; d = e) {
           for (e = d + 1; e < eodfl && d->finished >= e->finished; e++) {
	//  -d->lit => -e->lit;
	      e->lit = -1;
           }
    }
    q = 0;
    for (int p = q; p < nsize; p++) {
      int ulit = toInt(newCls[p])^1;
      if (dfpr[ulit].discovered) continue;
      newCls[q++]=newCls[p];
    }
    // copy from 'dfl' unremoved BIG literals back to clause
    for (d = dfl; d < eodfl; d++) {
      int lit = d->lit;
      if (lit<0) continue;
      newCls[q++]=toLit(lit);
    }
    newCls.shrink(nsize-q);
    nsize=q;

STRPOS:
    if (posdfl < 2) goto HBR;
    if (posdfl > szdfl) { 
          dfl = (DFL*)s_realloc (dfl, szdfl*sizeof(DFL), posdfl*sizeof(DFL));
          szdfl = posdfl; 
    }
    ndfl = 0;
    // copy original literals to 'dfl' but sort reverse wrt 'discovered'
    for(k=0; k<nsize; k++){
           int ulit = toInt(newCls[k]);
           if (!dfpr[ulit].discovered) continue;
	   dfl[ndfl].discovered = -dfpr[ulit].discovered;
	   dfl[ndfl].finished = -dfpr[ulit].finished;
	   dfl[ndfl].lit = ulit;
	   ndfl++;
    }
    if (ndfl < 2) goto NEXT;
    sort(dfl, ndfl);
    eodfl = dfl + ndfl;
    for (d = dfl; d < eodfl - 1; d = e) {
      for (e = d + 1; e < eodfl && d->finished >= e->finished; e++) {
	// e->lit => d->lit;
	e->lit = -1;
      }
    }
    q = 0;
    for (int p = q; p < nsize; p++) {
      int ulit = toInt(newCls[p]);
      if (dfpr[ulit].discovered) continue;
      newCls[q++]=newCls[p];
    }
    for (d = dfl; d < eodfl; d++) {
      int lit = d->lit;
      if (lit<0) continue;
      newCls[q++]=toLit(lit);;
    }
    newCls.shrink(nsize-q);
    nsize=q;
HBR:
   // hyper binary resolution x => -x1, x => -x2,...,x => -xn and y => -y1, y => -y2,...,y => -ym
   // -x1 V -x2 V...V -xn V y1 V y2 V...V ym => -x V -y 
    //if (!spf->opts.unhdhbr.val) goto NEXT;
    if (nsize < 3) goto NEXT;
    root1 = root2 = lca1 = lca2 = 0;
    for (int p = 0; p < nsize; p++) {
         int lit=toInt(newCls[p]);
         root = s_unhroot (lit^1);
         if (!root){
                root = lit^1;//var=1
                if (!root) goto NEXT;
         }
         if (!root1) { root1 = root; continue; }
         if (root1 == root) continue;
         if (!root2) { root2 = root; continue; }
         if (root2 == root) continue;
         if (s_unhimplies2incl (root1, lit^1)) { lca1 = root1; continue; }
         if (s_unhimplies2incl (root2, lit^1)) { lca2 = root2; continue; }
         goto NEXT;			// else more than two roots ...
    }
    if (!root2) goto NEXT;
    if (root1 == (root2^1)) goto NEXT;
    if (s_unhimplies2incl (root1, root2^1)) goto NEXT;
    //root hyper binary resolution %d %d of %s clause,-root1, -root2, type);
    if (!lca1 && !lca2) {
       for (int p = 0; p < nsize; p++) {
          int lit=toInt(newCls[p]);
          root = s_unhroot (lit^1);
	  if (root) {
	      if (root == root1) lca1 = lca1 ? s_unhlca (lca1, lit^1) : (lit^1);
	      if (root == root2) lca2 = lca2 ? s_unhlca (lca2, lit^1) : (lit^1);
	  } else {
	      if (lca1) lca2 = lit^1; 
              else lca1 = lit^1;
	  }
       }
    } 
    else {
      if (!lca1) lca1 = root1;
      if (!lca2) lca2 = root2;
    }
    if (lca1 == lca2^1 || lca1==0 || lca2==0) goto NEXT;
    if (s_unhimplies2incl (lca1, lca2^1)) goto NEXT;
    //lca hyper binary resolution lca1 => -x1, lca1 => -x2,...,lca1 => -xn and lca2 => -y1, lca2 => -y2,...,lca2 => -ym
    checkBin (lca1^1, lca2^1, 'a');
    addbinclause2(toLit(lca1^1), toLit(lca2^1), cr, learntflag);
    cls.push(cr);
    goto nextcls;
NEXT:
    if (nsize<c.size() && nsize>0) {
         // checklarg(newCls,'C');//bug
          removeClause(cls[i]);
          if(nsize>1){
              CRef cr = ca.alloc(newCls, learntflag);
              attachClause(cr);
              cls[j++] = cr;
              continue;
          }
          if(nsize==1){
               CRef confl = unitPropagation(newCls[0]);
               if (confl != CRef_Undef) ret=l_False;
          }
          continue;
      }
nextcls:
      cls[j++] = cls[i];
  }
  cls.shrink(i - j);
  if (dfl) free(dfl);
  return ret;
}
//---------------------------------------
// probing analysis returns 1st UIP
Lit Solver::s_prbana(CRef confl, Lit res)
{
    vec<Var> scan;
    int tpos=trail.size();
    int open=0;
    while(tpos>0){
          Clause & c = ca[confl];
          for (int i =0; i < c.size(); i++){
                 Var pv= var(c[i]);    
                 if (seen[pv]) continue;
                 if(level(pv) > 0 ) {
                        seen[pv]=1;
                        scan.push(pv);
                        open++;
                 }
          }
          while(tpos>0){
                tpos--;
                if(seen[var(trail[tpos])]) break;
          }
          open--;
          if(open==0) {           
                res = trail[tpos];
                break;
          }     
          confl = reason(var(trail[tpos]));
    }
    for (int i = 0; i<scan.size(); i++)  seen[scan[i]] = 0;
    return res;
}

int Solver :: s_randomprobe (vec<int> & outer) 
{
  unsigned mod = outer.size();
  if (mod==0) return -1;
  unsigned pos = s_rand () % mod;
  int res = outer[pos];
  if (assigns[res] != l_Undef) return -1;
  return res;
}

int Solver :: s_innerprobe (int start, vec<int> & probes) 
{
  vec<int> tmp;
  for (int i = start; i < trail.size(); i++) {
         Lit lit = trail[i];
         vec<Watcher>&  trn  = watches[lit];
         for(int j = 0; j<trn.size(); j++) {
                 CRef cr=trn[j].cref;
                 Clause & c = ca[cr];
                 if(c.size() != 3) continue;
                 int m=0;
                 for(int k=0; k<3; k++)
                       if(value(c[k]) != l_Undef) m++;
                 if(m>1) continue;
                 for(int k=0; k<3; k++){
                       if(value(c[k]) == l_Undef){
                             int v = var(c[k]);
                             if(seen[v]) continue;
                             tmp.push(v);
                             seen[v]=1;
                      }
                 }
         } 
  }//found %d inner probes in ternary clauses", s_cntstk (tmp));
  int res = s_randomprobe (tmp);
  for (int i = 0; i < tmp.size(); i++) seen[tmp[i]]=0;
  if (res<0) res = s_randomprobe (probes);
  return res;
}

void Solver :: s_addliftbincls (Lit p, Lit q)
{ 
    if(hasBin(p,q)) return;
    vec<Lit> ps;
    ps.push(p);
    ps.push(q);
    if(!is_conflict(ps)) return;
    CRef cr = ca.alloc(ps, false);
    clauses.push(cr);
    attachClause(cr);
}

lbool Solver :: check_add_equ (Lit p, Lit q)
{
    if( p == q) return l_Undef;
    if( p == ~q ) return l_False;
    if(!out_binclause(p,  ~q)) return l_Undef;
    if(!out_binclause(~p, q)) return l_Undef;

    return add_equ_link(toInt(p), toInt(q));
}

lbool Solver :: addeqvlist (vec <int> & equal)
{
     Lit p=toLit(equal[0]);
     for (int i = 1; i < equal.size(); i++) {
             Lit q=toLit(equal[i]);
             lbool ret = check_add_equ (p, q);
             if(ret == l_False){
                    return l_False;
             }
     }
     return l_Undef;
}       
//double depth unit probe
lbool Solver :: s_liftaux () 
{
  int i,outer,inner;
  unsigned pos, delta, mod;
  vec<int> probes, represented[2], equal[2];
  vec<Lit> saved; 
 
  for (int idx = 0; idx < nVars(); idx++) {
      if (assigns [idx] != l_Undef) continue;
      probes.push(idx);
  }
  mod = probes.size();
  if (mod<20) return l_Undef;
  find_relative_prime(pos, delta, mod);

  lbool ret=l_Undef;
  CRef confl;
  Lit inlit;
  int loop=mod-10;
  if(loop>10000) loop=10000;
  
  while ( --loop > 0 ) {
       outer = probes[pos];
       pos = (pos + delta) % mod;
       if (assigns[outer] != l_Undef ) continue;
        //1st outer branch %d during lifting, outer
       represented[0].clear();
       represented[1].clear();
       equal[0].clear();
       equal[1].clear();
       int oldtrailsize = trail.size();
       Lit outlit=mkLit(outer);
       newDecisionLevel();
       simpleUncheckEnqueue(outlit);
       confl = simplePropagate();
       if (confl != CRef_Undef) {
FIRST_OUTER_BRANCH_FAILED:
           Lit dom = s_prbana(confl, outlit);
            //1st outer branch failed literal %d during lifting, outer
            simpleCancelUntil(0);
            confl = unitPropagation(~dom);
            if (confl == CRef_Undef) continue;
            ret=l_False;
            break;
       }
       inner = s_innerprobe (oldtrailsize, probes);
       if (inner<0) {
FIRST_OUTER_BRANCH_WIHOUT_INNER_PROBE:
          //no inner probe for 1st outer probe %d", outer
           for (i = oldtrailsize; i < trail.size(); i++) represented[0].push(toInt(trail[i]));
           goto END_OF_FIRST_OUTER_BRANCH;
       }   //1st inner branch %d in outer 1st branch %d", inner, outer
       inlit =mkLit(inner);
       newDecisionLevel();
       simpleUncheckEnqueue(inlit);
       confl = simplePropagate();
       if (confl != CRef_Undef) {//1st inner branch failed literal %d on 1st outer branch %d,inner, outer
               simpleCancelUntil(0);
               s_addliftbincls (~outlit, ~inlit);
               newDecisionLevel();
               simpleUncheckEnqueue(outlit);
               confl = simplePropagate();
               if (confl == CRef_Undef ) goto FIRST_OUTER_BRANCH_WIHOUT_INNER_PROBE;
               goto FIRST_OUTER_BRANCH_FAILED; //conflict after propagating negation of 1st inner branch
        }
        saved.clear();
        for (i = oldtrailsize; i < trail.size(); i++) saved.push(trail[i]);
        simpleCancelUntil(1);
        newDecisionLevel();
        simpleUncheckEnqueue(~inlit);
        confl = simplePropagate();  //2nd inner branch %d in 1st outer branch %d", -inner, outer
        if (confl != CRef_Undef) {// 2nd inner branch failed literal %d on 1st outer branch %d,-inner, outer
               simpleCancelUntil(0);
               s_addliftbincls (~outlit, inlit);
               newDecisionLevel();
               simpleUncheckEnqueue(outlit);
               confl = simplePropagate();
               if (confl == CRef_Undef) goto FIRST_OUTER_BRANCH_WIHOUT_INNER_PROBE;
               goto FIRST_OUTER_BRANCH_FAILED;  // conflict after propagating negation of 2nd inner branch
        } 
        equal[0].push(toInt(inlit));
        while (saved.size()) {
               Lit lit = saved.pop_();
               if(value(lit) == l_True) represented[0].push(toInt(lit));
               else if(value(lit) == l_False && lit != inlit) equal[0].push(toInt(lit));
       }
END_OF_FIRST_OUTER_BRANCH:
       simpleCancelUntil(0); // 2nd outer branch %d during lifting, -outer
       newDecisionLevel();
       simpleUncheckEnqueue(~outlit);
       CRef confl = simplePropagate();
       if (confl != CRef_Undef) {
SECOND_OUTER_BRANCH_FAILED:
             Lit dom = s_prbana(confl, ~outlit);   //2nd branch outer failed literal %d during lifting, -outer
             simpleCancelUntil(0);
             confl = unitPropagation(~dom);
             if (confl == CRef_Undef) continue;
             ret=l_False;
             break;
      }

      if (inner < 0 || value(inlit) != l_Undef ) 
              inner = s_innerprobe (oldtrailsize, probes);
      if (inner < 0) {
SECOND_OUTER_BRANCH_WIHOUT_INNER_PROBE:
              //no inner probe for 2nd outer branch %d", -outer
             for (i = oldtrailsize; i < trail.size(); i++) represented[1].push(toInt(trail[i]));
             goto END_OF_SECOND_BRANCH;
      }
  //1st inner branch %d in outer 2nd branch %d", inner, -outer
      inlit =mkLit(inner);
      newDecisionLevel();
      simpleUncheckEnqueue(inlit);
      confl = simplePropagate();
      if (confl != CRef_Undef) {//1st inner branch failed literal %d on 2nd outer branch %d", inner, -outer
             simpleCancelUntil(0);
             s_addliftbincls (outlit, ~inlit);
             newDecisionLevel();
             simpleUncheckEnqueue(~outlit);
             confl = simplePropagate();
             if (confl == CRef_Undef) goto SECOND_OUTER_BRANCH_WIHOUT_INNER_PROBE;
                     // conflict after propagating negation of 1st inner branch
             goto SECOND_OUTER_BRANCH_FAILED;
       }
       saved.clear();
       for (i = oldtrailsize; i < trail.size(); i++) saved.push(trail[i]);
       simpleCancelUntil(1);
              // 2nd inner branch %d in 2nd outer branch %d", -inner, -outer
       newDecisionLevel();
       simpleUncheckEnqueue(~inlit);
       confl = simplePropagate(); 
       if (confl != CRef_Undef) {// 2nd inner branch failed literal %d on 2nd outer branch %d", -inner, -outer
              simpleCancelUntil(0);
              s_addliftbincls (outlit, inlit);
              newDecisionLevel();
              simpleUncheckEnqueue(~outlit);
              confl = simplePropagate();
              if (confl == CRef_Undef ) goto SECOND_OUTER_BRANCH_WIHOUT_INNER_PROBE;
                  //conflict after propagating negation of 2nd inner branch
              goto SECOND_OUTER_BRANCH_FAILED;
       }
       equal[1].push(toInt(inlit));
       while (saved.size()) {
               Lit lit = saved.pop_();
               if(value(lit) == l_True) represented[1].push(toInt(lit));
               else if(value(lit) == l_False && lit != inlit) equal[1].push(toInt(lit));
       }
END_OF_SECOND_BRANCH:
       simpleCancelUntil(0);
       for (i = 0; i < represented[0].size(); i++) mark[represented[0][i]]=1;
       mark[2*outer]=mark[2*outer+1]=0;
       for (i = 0; i < represented[1].size(); i++) {
               int ulit=represented[1][i]; 
               if(mark[ulit]){//??? bug
                    if(assigns[ulit/2] != l_Undef) continue;

                    Lit q=toLit(ulit);
                    if(checkUnit (ulit, 'p')){//2017.1.17 bug?
                  unitq:
                         confl = unitPropagation(q);
                         if (confl == CRef_Undef) continue;
                         ret=l_False;
                         break;
                    }
                    else {
                        if(!out_binclause(outlit, q)) continue;
                        if(!out_binclause(~outlit, q)) continue;
                        goto unitq;
                    }
               }
               if(mark[ulit^1]){
                      Lit q=toLit(ulit^1);
                      ret = check_add_equ (outlit,q);// outlit => q
                      if(ret == l_False){
                            break;
                      }
               }
      }
      for (i = 0; i < represented[0].size(); i++) mark[represented[0][i]]=0;
      if(ret == l_False) break;
// p => A=B, ~p => A=B   ==>  A=B       
      for (i = 0; i < equal[0].size(); i++) mark[equal[0][i]]=1;
      int eqn=0;
      for (i = 0; i < equal[1].size(); i++) if(mark[equal[1][i]]) eqn++;
      if(eqn < 2){
         eqn=0;
         for (i = 0; i < equal[1].size(); i++){
                  int notl=equal[1][i]^1;
                  equal[1][i]=notl;
                  if(mark[notl]) eqn++;
         }
      }
      for (i = 0; i < equal[0].size(); i++) mark[equal[0][i]]=0;
      if(eqn >= 2){
            ret=addeqvlist(equal[0]);
            if(ret == l_False) break;
            ret=addeqvlist(equal[1]);
            if(ret == l_False) break;
      }
  }
  return ret;
}

lbool Solver :: s_lift ()
{ 
  if (nVars()>500000) return l_Undef;
  simpleCancelUntil(0);
  mark = (char * ) calloc (2*nVars()+1, sizeof(char));
  int oldeqn = equsum;
  lbool ret= s_liftaux ();
  free(mark);

  if(verbosity > 0) printf("c lift old eqn=%d cur eqn=%d \n",  oldeqn,equsum);
     
  if(oldeqn != equsum && ret ==l_Undef) return replaceEqVar();
  return ret;
}

// simple lift or probe unit
lbool Solver :: s_probe ()
{ 
   Lit dom={-2}, rootlit;
   unsigned pos, delta;
   vec <int> probes;
   vec <Lit> lift, saved;
   int nprobes,oldtrailsize;

   for (int idx = 0; idx < nVars(); idx++) {
      if (assigns [idx] != l_Undef) continue;
      probes.push(idx);
   }
   nprobes = probes.size();
   if (nprobes < 20) return l_Undef;
   find_relative_prime(pos, delta, nprobes);
 
   int units=0;
   simpleCancelUntil(0);
   lbool ret=l_Undef;
   int loop=nprobes-10;
   if(loop>10000) loop=10000;

   while ( --loop > 0 ) {
        int root = probes[pos];
        pos = (pos+delta) % nprobes;
        if (assigns [root] != l_Undef) continue;
        lift.clear();
        saved.clear();
    //-------------------------level==0
       oldtrailsize = trail.size();
       rootlit=mkLit(root);
       newDecisionLevel();
       simpleUncheckEnqueue(rootlit);
       CRef confl = simplePropagate();
       if (confl == CRef_Undef) {
          for (int i = oldtrailsize; i < trail.size(); i++) saved.push(trail[i]);
       } 
       else {
             dom = s_prbana(confl, rootlit);
       }
       simpleCancelUntil(0);
       if (confl != CRef_Undef) {// failed literal %d on probing, dom, root
               lift.push(~dom);
               goto LUNIT;
       }// next probe %d negative phase, -root
    //---------------------------------------
       newDecisionLevel();
       simpleUncheckEnqueue(~rootlit);
       confl = simplePropagate();
       if (confl == CRef_Undef) {
          for (int i = 0; i <saved.size(); i++) 
                if(value(saved[i]) == l_True ) lift.push(saved[i]);
       } 
       else  dom = s_prbana(confl, ~rootlit);
       simpleCancelUntil(0);
   //------------------------------------------------
      if (confl != CRef_Undef) {// failed literal %d on probing %d, dom, -root
             lift.push(~dom);
      }
LUNIT:
      for (int i = 0; i < lift.size(); i++){
             if(value(lift[i]) != l_Undef) continue;
             if(checkUnit (toInt(lift[i]), 's')){
                   units++;
                   confl = unitPropagation(lift[i]);
                   if (confl == CRef_Undef) continue;
                   ret=l_False;
                   goto DONE;
             }
      }
  }
DONE:
  return ret;
}

inline void Solver :: update_score(int ulit)
{
      int v=ulit/2;
      int pos=fullwatch[ulit].size();
      int neg=fullwatch[ulit^1].size();
      if(sched_heap.inHeap(v)){
            int old=vscore[v];
            if( !pos  || !neg ) vscore[v] = 0;
            else if(pos < 10000 && neg < 10000) vscore[v] = pos*neg;
                 else vscore[v]=10000000;
            if(old > vscore[v]) sched_heap.decrease(v);
            if(old < vscore[v]) sched_heap.increase(v);
      }
      else{
        if(decision[v] && (pos+neg) < 16){
             if(vscore[v] > pos*neg && pos+neg>6){
                   vscore[v] = pos*neg;
                   sched_heap.insert(v);
             }
        } 
     }
}        

void Solver::removefullclause(CRef cr) 
{
  Clause& c = ca[cr];
  for(int i=0; i<c.size(); i++){
        int ulit=toInt(c[i]);
        remove(fullwatch[ulit], cr);
        if(vscore.size()>=nVars()) update_score(ulit);
  }
  removeClause(cr);
}

void Solver :: s_addfullcls (vec<Lit> & ps, int learntflag)
{ 
    CRef cr = ca.alloc(ps, learntflag);
    if(!learntflag) clauses.push(cr);
    else            learnts.push(cr);
    for(int i=0; i<ps.size(); i++) {
             int ulit=toInt(ps[i]);
             fullwatch[ulit].push(cr);
             if(vscore.size()>=nVars()) update_score(ulit);
    }
    attachClause(cr);
}

void Solver :: buildfullwatch ()
{
    for (int i =0; i < 2*nVars(); i++) fullwatch[i].clear();
    for (int i =0; i < clauses.size(); i++){
        CRef cr =clauses[i];
        Clause& c = ca[cr];
        if (c.mark()==1) continue;
        for(int j=0; j<c.size(); j++) fullwatch[toInt(c[j])].push(cr);
    }
}       

int Solver :: s_chkoccs4elmlit (int ulit) 
{
   vec <CRef> &  cs  = fullwatch[ulit];
   int sz=cs.size();
   for (int i = 0; i<sz; i++) {
         CRef cr=cs[i];
         Clause& c = ca[cr];
         int size = 0;
         for(int j=c.size()-1; j>=0; j--){
             if(fullwatch[toInt(c[j])].size() > 800) return 0;
             if (++size > 600) return 0;
         }
   }
   return 1;
}

int Solver :: s_chkoccs4elm (int v) 
{
   if(fullwatch[2*v].size()   > 800) return 0;
   if(fullwatch[2*v+1].size() > 800) return 0;
   if (!s_chkoccs4elmlit (2*v)) return 0;
   return s_chkoccs4elmlit (2*v+1);
}

vec <int> elm_m2i, clv;
 
static const uint64_t s_basevar2funtab[6] = {
  0xaaaaaaaaaaaaaaaaull, 0xccccccccccccccccull, 0xf0f0f0f0f0f0f0f0ull,
  0xff00ff00ff00ff00ull, 0xffff0000ffff0000ull, 0xffffffff00000000ull,
};

// mapped external variable to marked variable
int Solver :: s_s2m (int ulit) 
{  int v=ulit/2;
   int res = markNo[v];
   if (!res) {
       elm_m2i.push(v); 
       res = elm_m2i.size();
       if (res > 11) return 0;
       markNo[v] = res;
  }
  return 2*res + (ulit%2);
}

// mapped external variable to marked variable
int Solver :: s_i2m (int ulit) 
{  int v=ulit/2;
   int res = markNo[v];
   if (!res) {
        elm_m2i.push(v);
        res = elm_m2i.size();
        markNo[v] = res;
  }
  return 2*res - 2 + (ulit%2);
}

// map marked variable to external variable
int Solver :: s_m2i (int mlit) {
  int res, midx = mlit/2;
  res = elm_m2i[midx-1];
  return 2*res + (mlit%2);
}

void s_var2funaux (int v, Fun res, int negate) {
  uint64_t tmp;
  int i, j, p;
  if (v < 6) {
    tmp = s_basevar2funtab[v];
    if (negate) tmp = ~tmp;
    for (i = 0; i < FUNQUADS; i++) res[i] = tmp;
  } else {
    tmp = negate ? ~0ull : 0ull;
    p = 1 << (v - 6);
    j = 0;
    for (i = 0; i < FUNQUADS; i++) {
      res[i] = tmp;
      if (++j < p) continue;
      tmp = ~tmp;
      j = 0;
    }
  }
}

static Cnf s_pos2cnf (int pos)  { return pos; }
static Cnf s_size2cnf (int s)   { return ((Cnf)s) << 32; }
static int s_cnf2pos (Cnf cnf)  { return cnf & 0xfffffll; }
static int s_cnf2size (Cnf cnf) { return cnf >> 32; }
static Cnf s_cnf (int pos, int size) {
  return s_pos2cnf (pos) | s_size2cnf (size);
}

void s_negvar2fun (int v, Fun res) {  s_var2funaux (v, res, 1);}
void s_var2fun (int v, Fun res)    {  s_var2funaux (v, res, 0);}

void s_s2fun (int marklit, Fun res) 
{
  int sidx = marklit/2 - 2;
  if ( marklit & 1 ){
        s_negvar2fun (sidx, res);
  }
  else {
       s_var2fun (sidx, res);
  }
}

static void s_orfun (Fun a, const Fun b) {
  for (int i = 0; i < FUNQUADS; i++) a[i] |= b[i];
}

static void s_andfun (Fun a, const Fun b) {
  for (int i = 0; i < FUNQUADS; i++)    a[i] &= b[i];
}

static void s_or3fun (Fun a, const Fun b, const Fun c) {
  for (int i = 0; i < FUNQUADS; i++)  a[i] = b[i] | c[i];
}

static void s_and3negfun (Fun a, const Fun b, const Fun c) {
  for (int i = 0; i < FUNQUADS; i++)    a[i] = b[i] & ~c[i];
}

static void s_and3fun (Fun a, const Fun b, const Fun c) {
  for (int i = 0; i < FUNQUADS; i++)    a[i] = b[i] & c[i];
}

static void s_andornegfun (Fun a, const Fun b, const Fun c) {
  for (int i = 0; i < FUNQUADS; i++)    a[i] &= b[i] | ~c[i];
}

static void s_funcpy (Fun dst, const Fun src) {
  for (int i = 0; i < FUNQUADS; i++) dst[i] = src[i];
}

static void s_ornegfun (Fun a, const Fun b) {
  for (int i = 0; i < FUNQUADS; i++) a[i] |= ~b[i];
}

static void s_slfun (Fun a, int shift) {
  uint64_t rest, tmp;
  int i, j, q, b, l;
  b = shift & 63;
  q = shift >> 6;
  j = FUNQUADS - 1;
  i = j - q;
  l = 64 - b;
  while (j >= 0) {
    if (i >= 0) {
      tmp = a[i] << b;
      rest = (b && i > 0) ? (a[i-1] >> l) : 0ll;
      a[j] = rest | tmp;
    } else a[j] = 0ll;
    i--, j--;
  }
}

static void s_srfun (Fun a, int shift) {
  uint64_t rest, tmp;
  int i, j, q, b, l;
  b = shift & 63;
  q = shift >> 6;
  j = 0;
  i = j + q;
  l = 64 - b;
  while (j < FUNQUADS) {
    if (i < FUNQUADS) {
      tmp = a[i] >> b;
      rest = (b && i+1 < FUNQUADS) ? (a[i+1] << l) : 0ull;
      a[j] = rest | tmp;
    } else a[j] = 0ull;
    i++, j++;
  }
}

static void s_falsefun (Fun res) {
  for (int i = 0; i < FUNQUADS; i++)   res[i] = 0ll;
}

static void s_truefun (Fun res) {
  for (int i = 0; i < FUNQUADS; i++)
    res[i] = (unsigned long long)(~0ll);
}

static int s_isfalsefun (const Fun f) {
  for (int i = 0; i < FUNQUADS; i++)    if (f[i] != 0ll) return 0;
  return 1;
}

static int s_istruefun (const Fun f) {
  for (int i = 0; i < FUNQUADS; i++) if (f[i] != (unsigned long long)(~0ll)) return 0;
  return 1;
}

static void s_negcofactorfun (const Fun f, int v, Fun res) {
  Fun mask, masked;
  s_var2fun (v, mask);            //mask <- v
  s_and3negfun (masked, f, mask); //masked = f & ~mask;
  s_funcpy (res, masked);         //res <-masked
  s_slfun (masked, (1 << v));     // masked << v
  s_orfun (res, masked);          // res = res | masked
}

static void s_poscofactorfun (const Fun f, int v, Fun res) {
  Fun mask, masked;
  s_var2fun (v, mask);     //mask <- v
  s_and3fun (masked, f, mask); // //masked = a[i] = f & v
  s_funcpy (res, masked);      
  s_srfun (masked, (1 << v)); //// masked >> v
  s_orfun (res, masked);   // res = res | masked
}

static int s_eqfun (const Fun a, const Fun b) {
  for (int i = 0; i < FUNQUADS; i++)    if (a[i] != b[i]) return 0;
  return 1;
}

static int s_smalltopvar (const Fun f, int min) {
  Fun p, n;
  int v;
  for (v = min; v < FUNVAR; v++) {
    s_poscofactorfun (f, v, p);
    s_negcofactorfun (f, v, n);
    if (!s_eqfun (p, n)) return v;
  }
  return v;
}

static void s_or3negfun (Fun a, const Fun b, const Fun c) {
  for (int i = 0; i < FUNQUADS; i++)  a[i] = b[i] | ~c[i];
}

static void s_smallevalcls (unsigned cls, Fun res) {
  Fun tmp;
  int v;
  s_falsefun (res);
  for (v = 0; v < FUNVAR; v++) {
    if (cls & (1 << (2*v + 1))) {
      s_var2fun (v, tmp);
      s_ornegfun (res, tmp);
    } else if (cls & (1 << (2*v))) {
      s_var2fun (v, tmp);
      s_orfun (res, tmp);
    }
  }
}

static void s_smallevalcnf (Cnf cnf, Fun res) {
  Fun tmp;
  int i, n, p, cls;
  p = s_cnf2pos (cnf);
  n = s_cnf2size (cnf);
  s_truefun (res);
  for (i = 0; i < n; i++) {
    cls = clv[p + i];
    s_smallevalcls (cls, tmp);
    s_andfun (res, tmp);//res = res & cls
  }
}

int Solver :: s_initsmallve (int ulit, Fun res) 
{
  Fun cls, tmp;
  //initializing small variable eliminiation for %d", lit);
  s_s2m (ulit);
  s_truefun (res);
  Lit pivot=toLit(ulit);
  int count = fullwatch[ulit].size();

  vec<CRef>&  crs  = fullwatch[ulit];
  int clsCnt=0;
  for(int i = 0; i < count; i++){
        CRef cr=crs[i];
        Clause& c = ca[cr];
        s_falsefun (cls);// cls <- 000000
        for(int j = 0; j < c.size(); j++){
              if( value(c[j]) != l_Undef ){
                    if( value(c[j]) == l_True ) goto NEXT;
              }
              if( c[j] == pivot ) continue;
              int mlit = s_s2m (toInt(c[j]));
              if (!mlit) {
                     return 0;
	      }
              s_s2fun (mlit, tmp); //convert to fun 
	      s_orfun (cls, tmp);  // cls = cls | tmp 
        }
        clsCnt=1;
        s_andfun (res, cls); //res = res & cls
  NEXT:  ;
  }
  return clsCnt;
}

static Cnf s_smalladdlit2cnf (Cnf cnf, int lit) {
  int p, m, q, n, i, cls;
  Cnf res;
  p = s_cnf2pos (cnf);
  m = s_cnf2size (cnf);
  q = clv.size();
  for (i = 0; i < m; i++) {
    cls = clv[p + i];
    cls |= lit;
    clv.push(cls);
  }
  n = clv.size() - q;
  res = s_cnf (q, n);
  return res;
}

#define FALSECNF	(1ll<<32)
#define TRUECNF		0ll

static Cnf s_smallipos (const Fun U, const Fun L, int min) {
  Fun U0, U1, L0, L1, Unew, ftmp;
  Cnf c0, c1, cstar, ctmp, res;
  int x, y, z;
  if (s_istruefun (U)) return TRUECNF;  //U=11111
  if (s_isfalsefun (L)) return FALSECNF;//U=00000
  y = s_smalltopvar (U, min);
  z = s_smalltopvar (L, min);
  x = (y < z) ? y : z;

  s_negcofactorfun (U, x, U0); // U0 = U & ~x 
  s_poscofactorfun (U, x, U1); // U1 = U & x
  
  s_negcofactorfun (L, x, L0); // L0 = L & ~x
  s_poscofactorfun (L, x, L1); // L1 = L & x

  s_or3negfun (ftmp, U0, L1); // ftmp = U0 | ~L1 => ftmp = (U & ~x) | ~(L & x)  
  c0 = s_smallipos (ftmp, L0, min+1);    // L0= L & ~x

  s_or3negfun (ftmp, U1, L0); // ftmp = U1 | ~L0 => ftmp = (U & x) | ~(L & ~x)
  c1 = s_smallipos (ftmp, L1, min+1);

  s_smallevalcnf (c0, ftmp);     // ftmp <- c0
  s_or3negfun (Unew, U0, ftmp); // Unew = U0 | ~c0;
 
  s_smallevalcnf (c1, ftmp);
  s_andornegfun (Unew, U1, ftmp); // Unew = Unew & (U1 | ~c1);

  s_or3fun (ftmp, L0, L1);//ftmp = L0 | L1
  cstar = s_smallipos (Unew, ftmp, min+1);

  ctmp = s_smalladdlit2cnf (c1, (1 << (2*x + 1)));
  res = s_cnf2pos (ctmp);

  ctmp = s_smalladdlit2cnf (c0, (1 << (2*x)));
  if (res == TRUECNF) res = s_cnf2pos (ctmp);

  ctmp = s_smalladdlit2cnf (cstar, 0);
  if (res == TRUECNF) res = s_cnf2pos (ctmp);

  res |= s_size2cnf (clv.size() - res);
  return res;
}

int Solver :: s_smallisunitcls (int cls) {
  int fidx, fsign, flit, ulit;
  ulit = -1;
  for (fidx = 0; fidx < FUNVAR; fidx++)
    for (fsign = 0; fsign <= 1; fsign++) {
      flit = 1<<(2*fidx + fsign);
      if (!(cls & flit)) continue;
      if (ulit>=0) return -1;
      int mlit = (fidx + 2) * 2 + fsign;
      ulit = s_m2i (mlit);
  }
  return ulit;
}

int Solver :: s_smallcnfunits (Cnf cnf) 
{
  int p, m, i, cls, ulit;
  p = s_cnf2pos (cnf);
  m = s_cnf2size (cnf);
  int units = 0;
  for (i = 0; i < m; i++) {
      cls = clv[p + i];
      ulit = s_smallisunitcls (cls);
      if (ulit < 0) continue;
      units++;
  }
  return units;
}

lbool Solver :: s_smallve (Cnf cnf, int pivotv, bool newaddflag) 
{
  int cls, v, trivial;
  vec <Lit> newCls;
  int end=s_cnf2pos (cnf)+s_cnf2size (cnf);
  int elimFlag=1;
  int count=0;
  for (int i = end-1; i >= s_cnf2pos (cnf); i--) {
     cls = clv[i];
     trivial = 0;
     newCls.clear();
     for (v = 0; v < FUNVAR; v++) {
         int ulit;
         if (cls & (1 << (2*v + 1)))  ulit = s_m2i (2*v+5);
         else if (cls & (1 << (2*v))) ulit = s_m2i (2*v+4);
              else continue;
         Lit lit=toLit(ulit);
         if (value (lit) == l_False) continue;
         if (value (lit) == l_True) trivial = 1;
         newCls.push(lit);
     }
     if (!trivial) {//small elimination resolvent
          count++;
          if(newCls.size()>1) {
              if(newaddflag) s_addfullcls (newCls, 0);
          }
          else {
             if(newCls.size()==1){
                  if(checkUnit (toInt(newCls[0]), 's')){
                      CRef confl = unitPropagation(newCls[0]);
                      if (confl != CRef_Undef) return l_False;
                  }
                  else elimFlag=0;
             }
             else elimFlag=0;
          } 
     }
  }
  if(elimFlag && count && newaddflag){
      s_epusheliminated (pivotv);
  }
  return l_Undef;
}

void Solver :: s_epusheliminated (int v) 
{ 
   setDecisionVar(v, false);
   int pos=fullwatch[2*v].size();
   int neg=fullwatch[2*v+1].size();
   deletedCls.clear();
   if(pos==0 && neg==0) return;
   int ulit= (pos <= neg) ? (2*v) : (2*v+1);
   vec<CRef> &  pcs  = fullwatch[ulit];
   Lit pivot=toLit(ulit);
   for(int i = 0; i < pcs.size(); i++){
        CRef pcr=pcs[i];
        deletedCls.push(pcr);
        Clause& c = ca[pcr];
        extendRemLit.push (lit_Undef);
        extendRemLit.push(pivot);
        for(int k = 0; k < c.size(); k++){
               if (c[k] == pivot) continue;
               extendRemLit.push(c[k]);
        }
  }
  extendRemLit.push (lit_Undef);
  extendRemLit.push(~pivot);
  vec<CRef> &  ncs  = fullwatch[ulit^1];
  for(int i = 0; i < ncs.size(); i++) deletedCls.push(ncs[i]);
}

lbool Solver :: s_trysmallve (int v, int & res) 
{
  int newsz, old, units;
  Fun pos, neg, fun;
  Cnf cnf;

  elm_m2i.clear();
  clv.clear();
  clv.push(0);
  res = 0;
//too many variables for small elimination
  if (s_initsmallve (2*v, pos) && s_initsmallve (2*v+1, neg)) {
   //     printPivotClause (2*v);
        s_or3fun (fun, pos, neg); //fun = pos | neg
        cnf = s_smallipos (fun, fun, 0);
        newsz = s_cnf2size (cnf);
        units = s_smallcnfunits (cnf);
        old = fullwatch[2*v].size() + fullwatch[2*v+1].size();
        //small elimination of %d replaces "%d old with %d new clauses and %d units",idx, old, newsz, units);
        if ((newsz-units) < old || units > 0) {
                int cnt=s_smallvccheck (v);
                if(cnt==newsz){
                    res = 1;
                    return s_smallve (cnf, v, newsz <= old);
                }
                if(cnt<old) {
                     res = 1;
                     return s_forcedve (v);
                }
                if(units > 0){
                    res = 1;
                    return s_smallve (cnf, v, 0);
                } 
        }
  } 
  return l_Undef;
}

lbool Solver ::s_forcedve (int v) 
{
   int pos=fullwatch[2*v].size();
   int neg=fullwatch[2*v+1].size();
   if(pos==0 && neg==0) return l_Undef;
 
   int pivot = (pos <= neg) ? (2*v) : (2*v+1);
   int npivot = pivot^1;
   int elimflag=1;
   int prevsize;
   lbool ret = l_Undef;
   vec<Lit> newcls;
   vec<CRef> &  pcs  = fullwatch[pivot];
   vec<CRef> &  ncs  = fullwatch[npivot];
   Lit plit=toLit(pivot);
   Lit nlit=~plit;
   for(int i = 0; i < pcs.size(); i++){
        CRef pcr=pcs[i];
        Clause & a = ca[pcr];
        newcls.clear();
        for(int k = 0; k < a.size(); k++){
               if (a[k] == plit) continue;
               if (value(a[k]) == l_False) continue;
               if (value(a[k]) == l_True) goto DONE;
               mark[toInt(a[k])]=1;
               newcls.push(a[k]);
        }
        if(newcls.size()==0) return l_Undef;
        prevsize=newcls.size();
        for(int j = 0; j < ncs.size(); j++){
               CRef ncr=ncs[j];
               Clause& b = ca[ncr];
               for(int k = 0; k < b.size(); k++){
                     if (b[k] == nlit) continue;
                     if (value(b[k]) == l_False) continue;
                     if (value(b[k]) == l_True) goto NEXT;
                     int ul=toInt(b[k]);
                     if (mark[ul]) continue;
                     if (mark[ul^1]) goto NEXT;
                     newcls.push(b[k]);
               }
               if(newcls.size()==1){
                    if( value(newcls[0]) != l_Undef ){
                               elimflag=0;
                               goto DONE;
                     }
                     if(checkUnit (toInt(newcls[0]), 'e')){
                            CRef confl = unitPropagation(newcls[0]);
                            if (confl != CRef_Undef) {ret=l_False; goto DONE;}
                       }
                       else elimflag=0; 
              }
              else{
                  s_addfullcls (newcls, 0);
              }
        NEXT:  
              newcls.shrink(newcls.size()-prevsize);
        } 
  DONE:
        for(int k = 0; k < a.size(); k++) mark[toInt(a[k])]=0;
        if(ret==l_False || elimflag==0) return ret;
   }
   if(elimflag)  s_epusheliminated (v);
   return ret;
}

int Solver ::s_smallvccheck (int v) 
{
   int pos=fullwatch[2*v].size();
   int neg=fullwatch[2*v+1].size();
   int pivot = (pos <= neg) ? (2*v) : (2*v+1);
   int npivot = pivot^1;
   vec<CRef> &  pcs  = fullwatch[pivot];
   vec<CRef> &  ncs  = fullwatch[npivot];
   Lit plit=toLit(pivot);
   Lit nlit=~plit;
   int oldsz=pcs.size()+ncs.size();
   int newsz=0;
   for(int i = 0; i < pcs.size(); i++){
        CRef pcr=pcs[i];
        Clause& a = ca[pcr];
        for(int k = 0; k < a.size(); k++){
               if (a[k] == plit) continue;
               mark[toInt(a[k])]=1;
        }
        for(int j = 0; j < ncs.size(); j++){
               CRef ncr=ncs[j];
               Clause & b = ca[ncr];
               for(int k = 0; k < b.size(); k++){
                     if (b[k] == nlit) continue;
                     int ul=toInt(b[k]);
                     if (mark[ul]) continue;
                     if (mark[ul^1]) goto NEXT;
               }
               newsz++;
               if(newsz>=oldsz) goto DONE;
        NEXT: ;
        } 
  DONE:
        for(int k = 0; k < a.size(); k++) mark[toInt(a[k])]=0;
        if(newsz>=oldsz) return newsz;
   }
   return newsz;
}

int Solver :: s_forcedvechk (int v) 
{
  int pos=fullwatch[2*v].size();
  int neg=fullwatch[2*v+1].size();
  if (pos >= (1<<15)) return 0;
  if (neg >= (1<<15)) return 0;
  int old = pos + neg;
  int newpn = pos * neg;
  return newpn <= old;
}

typedef struct ELM_CLAUSE { CRef cr; int size; unsigned csig;} ELM_CLAUSE;
vec <ELM_CLAUSE> eclsInfo; //elim clause info

// backward subsume and strengthened 
int Solver :: s_backsub (int cIdx, int startidx, int lastIdx, Lit pivot, int streFlag)
{
   int size = eclsInfo[cIdx].size;
   unsigned csig = eclsInfo[cIdx].csig;
   int res = 0;
   int marked=0;

   for (int i = startidx; i<lastIdx; i++){
        if(i == cIdx) continue;
        int osize = eclsInfo[i].size;
        if (osize > size || osize==0) continue;//size=0 => deleted
        unsigned ocsig = eclsInfo[i].csig;
        if ((ocsig & ~csig)) continue;
        if (!marked) {
               CRef cr=eclsInfo[cIdx].cr;
               Clause& c = ca[cr];
               for(int j = 0; j < c.size(); j++){
                    int ul=toInt(c[j]);
                    if(streFlag && pivot==c[j])  ul=ul^1;
                    mark[ul]=1;
               }
               marked = 1;
        }
        CRef cr=eclsInfo[i].cr;
        Clause & c = ca[cr];
        res=1;
        for(int k = 0; k < c.size(); k++){
              res=mark[toInt(c[k])];
              if(res==0) break;
        }
        if ( !res || !streFlag || osize < size) {
               if(res) break;
               continue;
        }
       //strengthening by double self-subsuming resolution, 
      // strengthened and subsumed original irredundant clause
      
        deletedCls.push(cr);
        eclsInfo[i].size=0;
        break;
  }
  if (marked) {
         CRef cr=eclsInfo[cIdx].cr;
         Clause & c = ca[cr];
         for(int j = 0; j < c.size(); j++){
                int ul=toInt(c[j]);
                if(streFlag && pivot==c[j])  ul=ul^1;
                mark[ul]=0;
         }
   }
   return res;
}
// elimiate subsume
void  Solver :: s_elmsub (int v) 
{
  Lit pivot = toLit(2*v);
  int lastIdx=eclsInfo.size();
  int ret;
  for (int cIdx =0;  cIdx < lastIdx; cIdx++){
       if(cIdx < neglidx){
            if(neglidx<2) return;
            ret = s_backsub (cIdx, 0,       neglidx, pivot, 0);
       }
       else {
            if(lastIdx-neglidx<2) return;
            ret = s_backsub (cIdx, neglidx, lastIdx, ~pivot,0);
       }
       if (ret) {   //subsumed original irredundant clause, subsumed mapped irredundant clause
            deletedCls.push(eclsInfo[cIdx].cr);
            eclsInfo[cIdx].size=0;
       } 
  }
  //subsumed %d clauses containing %d or %d,subsumed, spf->elm.pivot, -spf->elm.pivot);
}

  // strengthening with pivot 
lbool Solver :: s_elmstr (int v, int & res) 
{ int ret;
  vec <Lit> newCls; 
  Lit lit = toLit(2*v);
  int lastIdx=eclsInfo.size();
  if(neglidx==0 || neglidx >= lastIdx) return l_Undef;
  Lit pivot;
  for (int cIdx =0;  cIdx < lastIdx; cIdx++){
//strengthening with pivot
       for(int i=0; i < deletedCls.size();i++) if(eclsInfo[cIdx].cr==deletedCls[i]) goto NEXT;
       if(cIdx < neglidx){
              pivot= lit;
              ret =s_backsub (cIdx, neglidx, lastIdx, pivot, 1);
       }else  {
              pivot=~lit; 
              ret =s_backsub (cIdx, 0,       neglidx, pivot, 1);
       }
       if (ret) {   //subsumed original irredundant clause, subsumed mapped irredundant clause
              CRef cr=eclsInfo[cIdx].cr;
              deletedCls.push(cr);
              eclsInfo[cIdx].size=0;
              newCls.clear();
              Clause& c = ca[cr];

              for(int j = 0; j < c.size(); j++){
                   if(pivot==c[j]) continue;
                   newCls.push(c[j]);
              }
              if(newCls.size()==1){
                       res = 1;
                       if(value(newCls[0]) != l_Undef){
                             return l_Undef;
                       }
                       if(checkUnit (toInt(newCls[0]), 'D')){
                              CRef confl = unitPropagation(newCls[0]);
                              if (confl != CRef_Undef) return l_False;
                       }
                       return l_Undef;
             }
             if(newCls.size() >1) s_addfullcls (newCls, 0);
       }
NEXT:  ; 
  }
  res=0;
  return l_Undef;
}

//blocked clause elimination and forced resolution of clauses
void Solver :: s_elmfrelit (Lit pivot, int startp, int endp, int startn, int endn) 
{ int k;
  int cover = fullwatch[toInt(~pivot)].size();
  for (int i= startp;  i < endp; i++) {
        CRef cr=eclsInfo[i].cr;
        Clause & a = ca[cr];
        int maxcover = 0;
        for(k = 0; k < a.size(); k++){
              int ul=toInt(a[k]);
              maxcover += fullwatch[ul^1].size();
        }
        if (maxcover < 2*cover - 1) continue;
        for(k = 0; k < a.size(); k++) mark[toInt(a[k])]=1;
        int nontrivial = 0;
        for (int j= startn;  j < endn; j++) {
                CRef bcr=eclsInfo[j].cr;
                Clause & b = ca[bcr];
                int m=0;
                for(k = 0; k < b.size(); k++){
                       m = m+ mark[toInt(b[k])^1];
                       if(m >= 2) break;
                }
                if(m < 2) {	//non trivial resolvent in blocked clause elimination
                    nontrivial = 1;
                    break;
                }
        }
        for(k = 0; k < a.size(); k++) mark[toInt(a[k])]=0;
        if(nontrivial == 0){
              extendRemLit.push (lit_Undef);
              extendRemLit.push(pivot);
              for(k = 0; k < a.size(); k++) {
                     if(pivot == a[k]) continue;
                     extendRemLit.push(a[k]);
             }
             deletedCls.push(cr);
       }
   }
}

void Solver :: s_elmfre (Lit pivot) 
{
  s_elmfrelit (pivot, 0, neglidx, neglidx,eclsInfo.size());
  s_elmfrelit (~pivot, neglidx, eclsInfo.size(),0,neglidx);
}

#define PUSHDF(POSNEG, n, LIT) \
do { \
  if(!dfpr[LIT].discovered) break; \
  POSNEG[n].ulit = LIT; \
  POSNEG[n].discovered = dfpr[LIT].discovered; \
  POSNEG[n++].finished = dfpr[LIT].finished; \
} while (0)

typedef struct DF { int discovered, finished; int ulit;} DF;
DF *pos_df,*neg_df;
// DF *pos_df  = (DF *)malloc (size*sizeof(DF));
 // DF *neg_df = (DF *)malloc (size*sizeof(DF));
 
int cmpdf (const void * a, const void * b)
{  DF * c =(DF *)a;
   DF * d =(DF *)b;
   return c->discovered - d->discovered;
}

int Solver :: s_uhte (vec <Lit> & resolv) 
{
  int size = resolv.size();
  int i, p, n;
  if (size <= 2 || size > 1000) return 0;

  int posN=0;
  int negN=0;
  for (i = 0; i < size; i++) {
      int ulit = toInt(resolv[i]);
      PUSHDF (pos_df, posN,ulit);
      int nlit = ulit^1;
      PUSHDF (neg_df, negN,nlit);
  }
  if (posN==0 || negN==0) return 0;
//  SORT3 (spf->df.pos.dfs, spf->df.pos.ndfs, s_cmpdf);
   Adp_SymPSort((void *)pos_df, posN, sizeof(DF), cmpdf);
   Adp_SymPSort((void *)neg_df, negN, sizeof(DF), cmpdf);
  p = n = 0;
  for (;;) {
    if (neg_df[n].discovered > pos_df[p].discovered) {
      if (++p == posN) return 0;
    } 
    else if (neg_df[n].finished < pos_df[p].finished) {
      if (++n == negN) return 0;
    } 
    else {
        vec<Lit> ps;
        ps.push(~toLit(neg_df[n].ulit));
        ps.push(toLit(pos_df[p].ulit));
        if(is_conflict(ps)) return 1;
        return 0;
    }
  }
}

lbool Solver :: s_trylargeve (int v, int & res) 
{
  int ulit = 2*v;
  res=0;
  for (int i = 0; i <= 1; i++) {
      int clit = ulit^i;
      int n = fullwatch[clit].size();
      vec<CRef> &  crs  = fullwatch[clit];
      for (int j =0;  j < n; j++) {
           CRef cr=crs[j];
           Clause& c = ca[cr];
           for(int k = 0; k < c.size(); k++){
               if(fullwatch[toInt(c[k])].size() >1000) return l_Undef;//number of occurrences of %d larger than limit, ilit
           }
      }
  }
  int limit = fullwatch[ulit].size()+fullwatch[ulit^1].size();;
  // try clause distribution for %d with limit %d ip, limit
  int nlit=ulit^1;
  int n = fullwatch[ulit].size();
  int m = fullwatch[nlit].size();
  Lit pivot = toLit(ulit);
  vec<CRef> &  acrs  = fullwatch[ulit];
  vec<CRef> &  bcrs  = fullwatch[nlit];
  vec<CRef> PairCref;
  vec <Lit> resolvent;
  int j, leftsize;
  for (int i =0;  i < n && limit >= 0; i++) {
         CRef acr=acrs[i];
         Clause& a = ca[acr];
         int asize=a.size();
         resolvent.clear();
         for(int k = 0; k < asize; k++){
                if(a[k] == pivot) continue;
                if (value(a[k]) == l_False) continue;
                if (value(a[k]) == l_True) goto DONE1;
                mark[toInt(a[k])]=1;
                resolvent.push(a[k]);
         }
         leftsize = resolvent.size();
         if(leftsize==0){
                limit = -2; res=1;
                goto DONE1;
         }
         for (int j=0;  j < m && limit >= 0; j++) {
                 CRef bcr=bcrs[j];
                 Clause & b = ca[bcr];
                 int bsize=b.size();
                 int taut=0;     
                 for(int k = 0; k < bsize; k++){
                       if(b[k] == ~pivot) continue;
                       if (value(b[k]) == l_False) continue;
                       if (value(b[k]) == l_True) { taut=1; break;}
                       int ul=toInt(b[k]);
                       taut = mark[ul^1];
                       if(taut) break;
                       if(mark[ul]==0) resolvent.push(b[k]);
                 }       
                 int rsize=resolvent.size();
                 if (taut == 0){
                        if(  rsize == 1) {//trying resolution ends with unit clause");
                             limit += fullwatch[toInt(resolvent[0])].size();
                             goto addpair;
                        }
                         //trying resolution ends with hidden tautology");
                       if(dfpr && (rsize > 2 || asize > 1 || bsize > 1) && s_uhte (resolvent)) goto NEXT;
                       limit--;
      addpair:
                       PairCref.push(acr);
                       PairCref.push(bcr);
                }
         NEXT:  resolvent.shrink(rsize-leftsize);
         }
     DONE1:                
         for(int k = 0; k < asize; k++) mark[toInt(a[k])]=0;
   }
   if (limit < 0) return l_Undef; // resolving away %d would increase number of clauses;
   int elimflag=1; 
   lbool ret=l_Undef;
   for(int i=0; i<PairCref.size(); ){
         CRef acr=PairCref[i];
         Clause& a = ca[acr];
         resolvent.clear();
         for(int k = 0; k < a.size(); k++) {
               if(a[k] == pivot) continue;
               if (value(a[k]) == l_False) continue;
               mark[toInt(a[k])]=1;
               resolvent.push(a[k]);
         }
         int leftsize=resolvent.size();
         for(j=i+1;  j<PairCref.size() && acr==PairCref[j-1]; j+=2){
               CRef bcr=PairCref[j];
               Clause& b = ca[bcr];
               for(int k = 0; k < b.size(); k++) {
                   if(b[k] == ~pivot) continue;
                   if (value(b[k]) == l_False) continue;
                   if(mark[toInt(b[k])]==0) resolvent.push(b[k]);
               }
                if(resolvent.size()==1){
                       if(value(resolvent[0]) != l_Undef){
                               elimflag=0;
                               goto DONE2;
                       }
                       if(checkUnit (toInt(resolvent[0]), 'l')){
                            CRef confl = unitPropagation(resolvent[0]);
                            if (confl != CRef_Undef) {ret=l_False; goto DONE2;}
                       }
                       else elimflag=0; 
              }
              else {
                  s_addfullcls (resolvent, 0);
              }
              resolvent.shrink(resolvent.size()-leftsize);
         }
         i=j-1;
DONE2:
         for(int k = 0; k < a.size(); k++) mark[toInt(a[k])]=0;
         if (ret==l_False || elimflag==0) return ret;
   }
   if(elimflag) s_epusheliminated (v);
   res=1;
   return l_Undef;
}

lbool Solver :: s_tryforcedve (int v, int & success) 
{
    if (!s_forcedvechk (v)){
        success=0;
        return l_Undef;
    }
   // printPivotClause (2*v);
   // printPivotClause (2*v+1);
    success=1;       
    return s_forcedve (v);
}

lbool Solver :: s_elimlitaux (int v) 
{
   s_elmsub (v);
 //  if(deletedCls.size()) return  l_Undef;
   return  l_Undef;
}

// init eliminate clause
int Solver :: s_initecls (int v) 
{
   eclsInfo.clear();
   elm_m2i.clear();
   neglidx = fullwatch[2*v].size();
  
  if(!s_ecls (2*v)) return 0;
  if(!s_ecls (2*v+1)) return 0;
  return 1;
}

unsigned s_sig (int ulit) 
{
  unsigned res = (1u << (ulit & 31));
  return res;
}

int Solver :: s_addecl (CRef cr, Lit pivot)
{
    unsigned csig = 0;
    Clause& c = ca[cr];
    int idx=eclsInfo.size();
    eclsInfo.push();
    eclsInfo[idx].cr=cr;
    eclsInfo[idx].size=c.size();
    for(int i = 0; i < c.size(); i++){
          if( pivot == c[i] ) continue;
          int ul=toInt(c[i]);
          int markedlit = s_i2m (ul);
          if(markedlit>1000) return 0;
          csig |= s_sig (markedlit);
    }
    eclsInfo[idx].csig = csig;
   // for(int i = 0; i < c.size(); i++){
     //     int ul=toInt(c[i]);
    //      int umlit = s_i2m (ul);
         // if(umlit <= elm_lsigs.size()) {
         //     elm_lsigs.growTo(umlit+1);
         //     elm_lsigs[umlit] = csig;
         // }
         // else elm_lsigs[umlit] |= csig;
       //   if(umlit>1998) return 0;
        //  cls_idx[umlit].push(idx);
   // }
    return 1;
}

int Solver :: s_ecls (int ulit) 
{
   int occNum = fullwatch[ulit].size();
   vec<CRef> &  crs  = fullwatch[ulit];
   Lit lit=toLit(ulit);
   for(int i = 0; i < occNum; i++){
         if(!s_addecl (crs[i], lit)) return 0;
   }
   return 1;
}

inline void Solver :: clearMarkNO()
{ 
   for(int i=0; i<elm_m2i.size(); i++) markNo[elm_m2i[i]]=0;
   elm_m2i.clear();
}   
// trying to eliminate v
lbool Solver :: s_elimlit (int v) 
{
     if (!s_chkoccs4elm (v)) return l_Undef;
     int success=0;
     lbool ret=l_Undef;
     int pos=fullwatch[2*v].size();
     int neg=fullwatch[2*v+1].size();
     if(pos==0 && neg==0) return l_Undef;
     deletedCls.clear();
     if(pos==0 || neg==0){
         s_epusheliminated (v);
         goto DONE;
     }
     ret = s_trysmallve (v, success);
     clearMarkNO();
     if(success || ret == l_False) goto DONE;

   //  ret = s_tryforcedve (v, res);//inefficient
   //   clearMarkNO(); 
   //  if(res || ret == l_False) goto DONE;

   //  replaceClause (2*v);
   //  replaceClause (2*v+1);
   //  printPivotClause (2*v);
   //  printPivotClause (2*v+1);
   
    if(s_initecls (v)){
          ret=s_elimlitaux (v);
   }

DONE: 
     clearMarkNO();
     for(int i=0; i<deletedCls.size(); i++) {
          CRef cr=deletedCls[i];
          if(ca[cr].mark()==0) removefullclause(cr);
     }
   
     deletedCls.clear();
     eclsInfo.clear();
     return ret;
}

void Solver ::  s_eschedall() 
{   int nV=nVars();
    vscore.growTo(nV);
    sched_heap.clear();
    for(int v=0; v<nV; v++){
          if (assigns[v] == l_Undef && decision[v]){
              int pos=fullwatch[2*v].size();
              int neg=fullwatch[2*v+1].size();
              if( !pos  || !neg ) vscore[v] = 0;
              else  if(pos < 10000 && neg < 10000) vscore[v] = pos*neg;
                    else continue;
             sched_heap.insert(v);
         }
    }
}
/*
void Solver :: addlearnt()
{
   for (int i =0; i < learnts.size(); i++){
       CRef  cr=learnts[i];
       Clause & c = ca[cr];
	   int sz=0;
       for (int j = 0; j < c.size(); j++) {
		    Lit p=c[j];
          	if (value(p) == l_True) goto nextlc;
	    	if (value(p) == l_False) continue;
            sz++;
       }
       if(sz==2) {
            c.clearlearnt();
            clauses.push(cr);
            continue;
       }
       nextlc:  
       removeClause(cr);
   }
   learnts.clear(true);
   checkGarbage();
}  
*/
/*
lbool Solver :: inprocess()
{
    lbool status = s_lift ();
    if(status != l_Undef) return status;
    
    status = s_probe ();
    return status;
}
*/
  
lbool Solver :: s_eliminate ()
{   int loop;
    if( nVars() < 20 || nVars() > 500000) return l_Undef;
    mark = (char * ) calloc (2*nVars()+1, sizeof(char));
 
    simpleCancelUntil(0);
    markNo=0;
    pos_df=neg_df=0;
    vscore.clear(true);

    lbool ret = l_Undef;
    
    fullwatch = new vec<CRef>[2*nVars()];
    buildfullwatch ();
              
    ret = s_hte ();
    if( ret != l_Undef )  goto DONE;
 
    s_eschedall();
    s_block ();
//  
    s_eschedall ();
    loop = sched_heap.size();
    if( loop > 20000) loop =20000;
    markNo = (int * ) calloc (nVars()+1, sizeof(int));
    pos_df = (DF *)malloc (1000*sizeof(DF));
    neg_df = (DF *)malloc (1000*sizeof(DF));
   
    while ( --loop > 0){
        if (sched_heap.empty()) goto DONE;
        int v = sched_heap.removeMin();
        if(vscore[v]>160) continue;
        if (assigns[v] == l_Undef && decision[v]){
             ret = s_elimlit (v);
             if( ret != l_Undef ) goto DONE;
        }
   }

DONE:
  if (dfpr) free(dfpr);
  if(markNo) free(markNo);
  if(pos_df){
       free(pos_df);
       free(neg_df);
  }
  sched_heap.clear(true);
  vscore.clear(true);
  delete [] fullwatch;
  free(mark);
  cleanClauses(clauses);
  cleanNonDecision();
  return ret;
}

int Solver :: s_blockcls (int ulit) 
{
   vec<CRef>&  crs  = fullwatch[ulit];
   int occNum = fullwatch[ulit].size();
   for(int i = 0; i < occNum; i++){
        CRef cr=crs[i];
        Clause& c = ca[cr];
        int j, size =0;
        for(j = 0; j < c.size(); j++){
               if(mark[toInt(c[j])^1]) break;
               if (++size > 500) return 0;
        }
        if(j >= c.size()) return 0;
   }
   return 1;
}  

int Solver :: s_blocklit (int pivot) 
{
   int occNum = fullwatch[pivot].size();
   if(occNum == 0 || occNum >1500) return 0;

   vec<int> scan;
   vec<CRef> blockedcls;
   vec<CRef> &  crs  = fullwatch[pivot];
   Lit lit=toLit(pivot);
   for(int i = 0; i < occNum; i++){
        CRef cr=crs[i];
        Clause& c = ca[cr];
        int blocked = 0;
        scan.clear();
        int size =0;
        for(int j = 0; j < c.size(); j++){
               if (c[j] == lit) continue;
               if(fullwatch[toInt(c[j])].size() >1000) goto CONTINUE;
               if (++size > 1500) goto CONTINUE;
               int ul=toInt(c[j]);
                scan.push(ul);
	        mark[ul]=1;
        }
        blocked = s_blockcls (pivot^1);
CONTINUE:
        for(int k = 0; k < scan.size(); k++) mark[scan[k]]=0;
        if (blocked==0) continue;
       blockedcls.push(cr);
  }   
  int count = blockedcls.size();
  for(int i=0; i < count; i++){
        CRef cr=blockedcls[i];
        removefullclause(cr);
        Clause & c = ca[cr];
        extendRemLit.push (lit_Undef);
        extendRemLit.push (lit);
        for(int j = 0; j < c.size(); j++){
               if (c[j] == lit) continue;
               extendRemLit.push(c[j]);
        }
     }
  return count;
}

void Solver :: s_block () 
{
  int count = 0;
  int loop = sched_heap.size();
  if( loop > 20000) loop =20000;
  while ( --loop > 0 && count <10000){
        if (sched_heap.empty()) return;
        int v = sched_heap.removeMin();
        if ( assigns [v] != l_Undef ) continue;

      //  printPivotClause (2*v);
      //  printPivotClause (2*v+1);
  
        count += s_blocklit (2*v);
        count += s_blocklit (2*v+1);
  }
}

// hidden literal addition 
lbool Solver :: s_hla (Lit start,  vec <Lit> & scan) 
{
  scan.clear();
  scan.push(start);
  mark[toInt(start)]=1;
  //starting hidden literal addition start
  for(int next=0; next < scan.size() && next<1000; next++) {
          Lit lit = scan[next];
	  vec<Watcher>&  bin  = watches_bin[lit];
          for(int k = 0;k<bin.size();k++) {
                 Lit other = bin[k].blocker;
                 if( value(other) != l_Undef) continue;
                 int uo=toInt(other);
                 if ( mark[uo] ) continue;
                 if ( mark[uo^1]) {
                  	// failed literal %d in hidden tautology elimination, start
                      if(checkUnit (toInt(start)^1, 'h')){
                          CRef confl = unitPropagation(~start);
                          if (confl != CRef_Undef) return l_False;
                          return l_True;
                       }
                 }
                 mark[uo]=1;
                 scan.push(other);
          }
  }
  return l_Undef;
}

//Hidden Tautology Elimination
//hidden literal addition
lbool Solver :: s_hte () //need remove learnt clauses
{ 
  unsigned int nlits = 2*nVars();
  if (nlits <= 40) return l_Undef;
 
  unsigned pos, delta; 
  find_relative_prime(pos, delta, nlits);
  lbool ret;
  vec <Lit> scan;
  vec <Lit> newCs;
  int limit= nlits/2;
  if(limit>10000) limit=10000; 
  vec <CRef> bigCr;
  int lsize;
  for(; limit>0; limit--) {
       Lit root = toLit(pos);
       if ( value(root) != l_Undef) goto CONTINUE;
       ret=s_hla(~root,scan); // root -> a^b^c.....
       if(ret != l_Undef) goto CONTINUE;
       lsize  = fullwatch[pos].size();
       bigCr.clear();
       for(int j = 0; j<lsize; j++) bigCr.push(fullwatch[pos][j]);
       for(int j = 0; j<bigCr.size(); j++){
              CRef cr=bigCr[j];
              Clause & c = ca[cr];
              if(c.mark()==1 || c.size()<3) continue;
              int taut=0;
              newCs.clear();
              newCs.push(root);
              for(int k=0; k<c.size(); k++){
                    if( c[k] == root) continue;
                    int ulit=toInt(c[k]);
                    if(mark[ulit]){
                         taut=1;
                         break;
                    }
                    if(mark[ulit^1]==0) newCs.push(c[k]);
              }
              if(taut==0){
                   if(newCs.size()==1){
                        if(checkUnit (toInt(newCs[0]), 'u')){
                            CRef confl = unitPropagation(newCs[0]);
                            if (confl != CRef_Undef) ret=l_False;
                         }
                         goto CONTINUE;
                   }
                   if(newCs.size() < c.size()) {
                        s_addfullcls (newCs, c.learnt());
                    }
              }
              if( newCs.size() < c.size()) {
                   removefullclause(cr);
              }
      }
CONTINUE:
       for(int j = 0; j<scan.size(); j++) mark[toInt(scan[j])]=0;
       if(ret == l_False ) return l_False;
       pos = (pos+delta) % nlits;
  }
  return l_Undef;
}

//=============================================
/*
void Solver::simpleUncheckEnqueue(Lit p, CRef from)
{
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p)); // this makes a lbool object whose value is sign(p)
    vardata[var(p)].reason = from;
    trail.push_(p);
}
void Solver::simpleuncheckedEnqueue(Lit p, CRef from)
{
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel());
    trail.push_(p);
}
*/
void Solver::simpleCancelUntil(int level) 
{
    if (decisionLevel() > level){
           for (int c = trail.size()-1; c >= trail_lim[level]; c--){
               Var      x  = var(trail[c]);
               assigns [x] = l_Undef;
           }
           qhead = trail_lim[level];
           trail.shrink(trail.size() - trail_lim[level]);
           trail_lim.shrink(trail_lim.size() - level);
     }
}

//==========================================================================================
//--------------------------------------------------------------
// parallel
bool Solver:: parallelExportUnitClause(Lit p) {
    return true;
}

void Solver:: parallelExportBinClause(Lit p, Lit q) {
    return;
}

Lit Solver::getUnit() {
    return lit_Undef;
}

void Solver:: getbin(Lit & p, Lit & q){
    return;
}

bool Solver::panicModeIsEnabled() {
    return false;
}

struct freq_lt {
    unsigned int * & freq2;
    freq_lt( unsigned int * & freq2_) : freq2(freq2_) { }
    bool operator()(int v1, int v2) { return freq2[v1]>freq2[v2];}
};

void Solver :: extractHighVar(vec <Lit> & highLit)
{
     int *freq = (int  * ) calloc (2*nVars()+1, sizeof(int));
     for (int i =0; i < clauses.size(); i++){
        CRef cr =clauses[i];
        Clause& c = ca[cr];
        for(int j=0; j<c.size(); j++) freq[toInt(c[j])]++;
     }
     int *highv = (int  *) malloc (nVars()*sizeof(int));
     unsigned int *freq2 = (unsigned int  *) malloc (nVars()*sizeof(int));
     unsigned int max_int=0x7ffffff0;
     for (int v =0; v < nVars(); v++){
           uint64_t nowf=(uint64_t)freq[2*v]*(uint64_t)freq[2*v+1];
           if(nowf > max_int) nowf = max_int;
           freq2[v]=nowf;
           highv[v]=v;
     }
     sort(highv, nVars(), freq_lt(freq2));
     highLit.clear();
     for (int i =0; i < nVars() && i<23; i++){
          int v=highv[i];
           if( value(v) != l_Undef) continue;
           Lit lit = (freq[2*v] < freq[2*v+1]) ? toLit(2*v+1) :toLit(2*v);
            if(i>14) lit = ~lit; 
           highLit.push(lit);
     }
     free(freq);
     free(freq2);
     free(highv);
}       

void Solver::ExtendCopyModel() {
      s_extend ();     // Extend & copy model:
      model.growTo(nVars());
      for (int i = 0; i < nVars(); i++) model[i] = value(i);
      solveEqu(equhead, nVars(), model);
      //int msz=originVars ? originVars : model.size();
      //model.shrink(model.size()-msz);
}

double Solver::progressEstimate() const {
    double progress = 0;
    double F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++) {
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}

inline bool Solver :: non_decision(Lit p)
{    Var v=var(p);
     if (value(v) != l_Undef || !decision[v]) return true;
     return false;
}

void Solver:: putbin(Lit p, Lit q)
{
      if(non_decision(p)) return; 
      if(non_decision(q)) return;
      if(equhead){
             int v = var(p)+1;
             if(equhead[v] &&  equhead[v] !=v){
                    setDecisionVar(v, false);
                    return;
             }
             v = var(q)+1;
             if(equhead[v] &&  equhead[v] !=v){
                    setDecisionVar(v, false);
                    return;
             }
      }         
      if( hasBin(p,q) ) return;
      vec<Lit> ps;
      ps.push(p);
      ps.push(q);
      CRef cr = ca.alloc(ps, false);
      clauses.push(cr);
      attachClause(cr);
}

