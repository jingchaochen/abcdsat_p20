/****************************************************************************************[Solver.h]
**************************************************************************************************/

#ifndef abcdsat_Solver_M_h
#define abcdsat_Solver_M_h

#define ANTI_EXPLORATION
//#define BIN_DRUP

#define INT_QUEUE_AVG
#define LOOSE_PROP_STAT

#include "mtl/Vec.h"
#include "mtl/Heap.h"
#include "mtl/Alg.h"
#include "utils/Options.h"
#include "core/SolverTypes.h"

// Don't change the actual numbers.
#define LOCAL 0
#define TIER2 2
#define CORE  3

namespace abcdSAT {

//=================================================================================================
// Solver_Mix -- the main class:

class Solver_Mix {
private:
    template<typename T>
    class MyQueue {
        int max_sz, q_sz;
        int ptr;
        int64_t sum;
        vec<T> q;
    public:
        MyQueue(int sz) : max_sz(sz), q_sz(0), ptr(0), sum(0) { assert(sz > 0); q.growTo(sz); }
        inline bool   full () const { return q_sz == max_sz; }
#ifdef INT_QUEUE_AVG
        inline T      avg  () const { assert(full()); return sum / max_sz; }
#else
        inline double avg  () const { assert(full()); return sum / (double) max_sz; }
#endif
        inline void   clear()       { sum = 0; q_sz = 0; ptr = 0; }
        void push(T e) {
            if (q_sz < max_sz) q_sz++;
            else sum -= q[ptr];
            sum += e;
            q[ptr++] = e;
            if (ptr == max_sz) ptr = 0;
        }
    };

public:

    // Constructor/Destructor:
    //
    Solver_Mix();
    virtual ~Solver_Mix();

    // Problem specification:
    //
    Var     newVar    (bool polarity = true, bool dvar = true); // Add a new variable with parameters specifying variable mode.

    bool    addClause (const vec<Lit>& ps);                     // Add a clause to the solver.
    bool    addEmptyClause();                                   // Add the empty clause, making the solver contradictory.
    bool    addClause (Lit p);                                  // Add a unit clause to the solver.
    bool    addClause (Lit p, Lit q);                           // Add a binary clause to the solver.
    bool    addClause (Lit p, Lit q, Lit r);                    // Add a ternary clause to the solver.
    bool    addClause_(      vec<Lit>& ps);                     // Add a clause to the solver without making superflous internal copy. Will
    // change the passed vector 'ps'.

    // Solving:
    //
    bool    simplify     ();                        // Removes already satisfied clauses.
    bool    solve        (const vec<Lit>& assumps); // Search for a model that respects a given set of assumptions.
    lbool   solveLimited (const vec<Lit>& assumps); // Search for a model that respects a given set of assumptions (With resource constraints).
    bool    solve        ();                        // Search without assumptions.
    bool    solve        (Lit p);                   // Search for a model that respects a single assumption.
    bool    solve        (Lit p, Lit q);            // Search for a model that respects two assumptions.
    bool    solve        (Lit p, Lit q, Lit r);     // Search for a model that respects three assumptions.
    bool    okay         () const;                  // FALSE means solver is in a conflicting state

    void    toDimacs     (FILE* f, const vec<Lit>& assumps);            // Write CNF to file in DIMACS-format.
    void    toDimacs     (const char *file, const vec<Lit>& assumps);
    void    toDimacs     (FILE* f, Clause& c, vec<Var>& map, Var& max);

    // Convenience versions of 'toDimacs()':
    void    toDimacs     (const char* file);
    void    toDimacs     (const char* file, Lit p);
    void    toDimacs     (const char* file, Lit p, Lit q);
    void    toDimacs     (const char* file, Lit p, Lit q, Lit r);
    
    // Variable mode:
    //
    void    setPolarity    (Var v, bool b); // Declare which polarity the decision heuristic should use for a variable. Requires mode 'polarity_user'.
    void    setDecisionVar (Var v, bool b); // Declare if a variable should be eligible for selection in the decision heuristic.

    // Read state:
    //
    lbool   value      (Var x) const;       // The current value of a variable.
    lbool   value      (Lit p) const;       // The current value of a literal.
    lbool   modelValue (Var x) const;       // The value of a variable in the last model. The last call to solve must have been satisfiable.
    lbool   modelValue (Lit p) const;       // The value of a literal in the last model. The last call to solve must have been satisfiable.
    int     nAssigns   ()      const;       // The current number of assigned literals.
    int     nClauses   ()      const;       // The current number of original clauses.
    int     nLearnts   ()      const;       // The current number of learnt clauses.
    int     nVars      ()      const;       // The current number of variables.
    int     nFreeVars  ()      const;

    // Resource contraints:
    //
    void    setConfBudget(int64_t x);
    void    setPropBudget(int64_t x);
    void    budgetOff();
    void    interrupt();          // Trigger a (potentially asynchronous) interruption of the solver.
    void    clearInterrupt();     // Clear interrupt indicator flag.

    // Memory managment:
    //
    virtual void garbageCollect();
    void    checkGarbage(double gf);
    void    checkGarbage();

    // Extra results: (read-only member variable)
    //
    vec<lbool> model;             // If problem is satisfiable, this vector contains the model (if any).
    vec<Lit>   conflict;          // If problem is unsatisfiable (possibly under assumptions),
    // this vector represent the final conflict clause expressed in the assumptions.

    // Mode of operation:
    //
    FILE*     drup_file;
    int       verbosity;
    double    step_size;
    double    step_size_dec;
    double    min_step_size;
    int       timer;
    double    var_decay;
    double    clause_decay;
    double    random_var_freq;
    double    random_seed;
    bool      VSIDS;
    int       ccmin_mode;         // Controls conflict clause minimization (0=none, 1=basic, 2=deep).
    int       phase_saving;       // Controls the level of phase saving (0=none, 1=limited, 2=full).
    bool      rnd_pol;            // Use random polarities for branching heuristics.
    bool      rnd_init_act;       // Initialize variable activities with a small random value.
    double    garbage_frac;       // The fraction of wasted memory allowed before a garbage collection is triggered.

    int       restart_first;      // The initial restart limit.                                                                (default 100)
    double    restart_inc;        // The factor with which the restart limit is multiplied in each restart.                    (default 1.5)
    double    learntsize_factor;  // The intitial limit for learnt clauses is a factor of the original clauses.                (default 1 / 3)
    double    learntsize_inc;     // The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)

    int       learntsize_adjust_start_confl;
    double    learntsize_adjust_inc;

    // Statistics: (read-only member variable)
    //
    uint64_t solves, starts, decisions, rnd_decisions, propagations, conflicts, conflicts_VSIDS;
    uint64_t dec_vars, clauses_literals, learnts_literals, max_literals, tot_literals;
    uint64_t chrono_backtrack, non_chrono_backtrack;

    vec<uint32_t> picked;
    vec<uint32_t> conflicted;
    vec<uint32_t> almost_conflicted;
#ifdef ANTI_EXPLORATION
    vec<uint32_t> canceled;
#endif

protected:

    // Helper structures:
    //
    struct VarData { CRef reason; int level; };
    static inline VarData mkVarData(CRef cr, int l){ VarData d = {cr, l}; return d; }

    struct Watcher {
        CRef cref;
        Lit  blocker;
        Watcher(CRef cr, Lit p) : cref(cr), blocker(p) {}
        bool operator==(const Watcher& w) const { return cref == w.cref; }
        bool operator!=(const Watcher& w) const { return cref != w.cref; }
    };

    struct WatcherDeleted
    {
        const ClauseAllocator& ca;
        WatcherDeleted(const ClauseAllocator& _ca) : ca(_ca) {}
        bool operator()(const Watcher& w) const { return ca[w.cref].mark() == 1; }
    };

    struct VarOrderLt {
        const vec<double>&  activity;
        bool operator () (Var x, Var y) const { return activity[x] > activity[y]; }
        VarOrderLt(const vec<double>&  act) : activity(act) { }
    };
    
    struct ConflictData
	{
		ConflictData() :
			nHighestLevel(-1),
			bOnlyOneLitFromHighest(false)
		{}

		int nHighestLevel;
		bool bOnlyOneLitFromHighest;
	};

    // Solver_Mix state:
    //
    bool                ok;               // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    vec<CRef>           clauses;          // List of problem clauses.
    vec<CRef>           learnts_core,     // List of learnt clauses.
    learnts_tier2,
    learnts_local;
    double              cla_inc;          // Amount to bump next clause with.
    vec<double>         activity_CHB,     // A heuristic measurement of the activity of a variable.
                        activity_VSIDS;
    double              var_inc;          // Amount to bump next variable with.
    OccLists<Lit, vec<Watcher>, WatcherDeleted>
    watches_bin,      // Watches for binary clauses only.
    watches;          // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
public:
    vec<lbool>          assigns;          // The current assignments.
    vec<char>           polarity;         // The preferred polarity of each variable.
    vec<char>           decision;         // Declares if a variable is eligible for selection in the decision heuristic.
    vec<Lit>            trail;            // Assignment stack; stores all assigments made in the order they were made.
    vec<int>            trail_lim;        // Separator indices for different decision levels in 'trail'.
    vec<VarData>        vardata;          // Stores reason and level for each variable.
    int                 qhead;            // Head of queue (as index into the trail -- no more explicit propagation queue in abcdSAT).
    int                 simpDB_assigns;   // Number of top-level assignments since last execution of 'simplify()'.
    int64_t             simpDB_props;     // Remaining number of propagations that must be made before next execution of 'simplify()'.
    vec<Lit>            assumptions;      // Current set of assumptions provided to solve by the user.
    Heap<VarOrderLt>    order_heap_CHB,   // A priority queue of variables ordered with respect to the variable activity.
                        order_heap_VSIDS;
    double              progress_estimate;// Set by 'search()'.
    bool                remove_satisfied; // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.

    int                 core_lbd_cut;
    float               global_lbd_sum;
    uint64_t             lbd_sum;
    MyQueue<int>        lbd_queue;  // For computing moving averages of recent LBD values.

    uint64_t            next_T2_reduce,
    next_L_reduce;

    ClauseAllocator     ca;
  
    int 				confl_to_chrono;
    int 				chrono;

    // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
    // used, exept 'seen' wich is used in several places.
    //
    vec<char>           seen;
    vec<Lit>            analyze_stack;
    vec<Lit>            analyze_toclear;
    vec<Lit>            add_tmp;
    vec<Lit>            add_oc;

    vec<uint64_t>       seen2;    // Mostly for efficient LBD computation. 'seen2[i]' will indicate if decision level or variable 'i' has been seen.
    uint64_t            counter;  // Simple counter for marking purpose with 'seen2'.

    double              max_learnts;
    double              learntsize_adjust_confl;
    int                 learntsize_adjust_cnt;

    // Resource contraints:
    //
    int64_t             conflict_budget;    // -1 means no budget.
    int64_t             propagation_budget; // -1 means no budget.
    bool                asynch_interrupt;

    // Main internal methods:
    //
    void     insertVarOrder   (Var x);                                                 // Insert a variable in the decision order priority queue.
    Lit      pickBranchLit    ();                                                      // Return the next decision variable.
    void     newDecisionLevel ();                                                      // Begins a new decision level.
    void     uncheckedEnqueue (Lit p, int level = 0, CRef from = CRef_Undef);                         // Enqueue a literal. Assumes value of literal is undefined.
    bool     enqueue          (Lit p, CRef from = CRef_Undef);                         // Test if fact 'p' contradicts current state, enqueue otherwise.
    CRef     propagate        ();                                                      // Perform unit propagation. Returns possibly conflicting clause.
    void     cancelUntil      (int level);                                             // Backtrack until a certain level.
    void     analyze          (CRef confl, vec<Lit>& out_learnt, int& out_btlevel, int& out_lbd);    // (bt = backtrack)
    void     analyzeFinal     (Lit p, vec<Lit>& out_conflict);                         // COULD THIS BE IMPLEMENTED BY THE ORDINARIY "analyze" BY SOME REASONABLE GENERALIZATION?
    bool     litRedundant     (Lit p, uint32_t abstract_levels);                       // (helper method for 'analyze()')
    lbool    search           (int& nof_conflicts);                                    // Search for a given number of conflicts.
    lbool    solve_           ();                                                      // Main solve method (assumptions given in 'assumptions').
    void     reduceDB         ();                                                      // Reduce the set of learnt clauses.
    void     reduceDB_Tier2   ();
    void     removeSatisfied  (vec<CRef>& cs);                                         // Shrink 'cs' to contain only non-satisfied clauses.
    void     safeRemoveSatisfied(vec<CRef>& cs, unsigned valid_mark);
    void     rebuildOrderHeap ();
    bool     binResMinimize   (vec<Lit>& out_learnt);                                  // Further learnt clause minimization by binary resolution.

    // Maintaining Variable/Clause activity:
    //
    void     varDecayActivity ();                      // Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
    void     varBumpActivity  (Var v, double mult);    // Increase a variable with the current 'bump' value.
    void     claDecayActivity ();                      // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead.
    void     claBumpActivity  (Clause& c);             // Increase a clause with the current 'bump' value.

    // Operations on clauses:
    //
    void     attachClause     (CRef cr);               // Attach a clause to watcher lists.
    void     detachClause     (CRef cr, bool strict = false); // Detach a clause to watcher lists.
    void     removeClause     (CRef cr);               // Detach and free a clause.
    bool     locked           (const Clause& c) const; // Returns TRUE if a clause is a reason for some implication in the current state.
    bool     satisfied        (const Clause& c) const; // Returns TRUE if a clause is satisfied in the current state.

    void     relocAll         (ClauseAllocator& to);

    // Misc:
    //
    int      decisionLevel    ()      const; // Gives the current decisionlevel.
    uint32_t abstractLevel    (Var x) const; // Used to represent an abstraction of sets of decision levels.
    CRef     reason           (Var x) const;
    
    ConflictData FindConflictLevel(CRef cind);
    
public:
    int      level            (Var x) const;
protected:
    double   progressEstimate ()      const; // DELETE THIS ?? IT'S NOT VERY USEFUL ...
    bool     withinBudget     ()      const;

    template<class V> int computeLBD(const V& c) {
        int lbd = 0;
        counter++;
        for (int i = 0; i < c.size(); i++){
            int l = level(var(c[i]));
            if (l != 0 && seen2[l] != counter){
                seen2[l] = counter;
                lbd++; } }

        return lbd;
    }
    // Static helpers:
    //
    // Returns a random float 0 <= x < 1. Seed must never be 0.
    static inline double drand(double& seed) {
        seed *= 1389796;
        int q = (int)(seed / 2147483647);
        seed -= (double)q * 2147483647;
        return seed / 2147483647; }

    // Returns a random integer 0 <= x < size. Seed must never be 0.
    static inline int irand(double& seed, int size) {
        return (int)(drand(seed) * size); }

    // simplify
    //
public:
    bool	simplifyAll();
    void	simplifyLearnt(Clause& c);
    bool	simplifyLearnt_core();
    bool	simplifyLearnt_tier2();
  
    int		trailRecord;
    void	litsEnqueue(int cutP, Clause& c);
    void	cancelUntilTrailRecord();
    void	simpleUncheckEnqueue(Lit p, CRef from = CRef_Undef);
    CRef    simplePropagate();
    uint64_t nbSimplifyAll;
    uint64_t simplified_length_record, original_length_record;
    uint64_t s_propagations;

    vec<Lit> simp_learnt_clause;
    vec<CRef> simp_reason_clause;
    void	simpleAnalyze(CRef confl, vec<Lit>& out_learnt, vec<CRef>& reason_clause, bool True_confl);
    // in redundant
    bool removed(CRef cr);
    // adjust simplifyAll occasion
    long curSimplify;
    int nbconfbeforesimplify;
    int incSimplify;

   uint64_t       VSIDS_props_limit;
 
   int  FixedVars ()  const  { return (trail_lim.size() == 0 ? trail.size() : trail_lim[0]); }
   bool non_decision(Lit p);
   void putbin(Lit p, Lit q);
   bool hasBin(Lit p, Lit q);
};


//=================================================================================================
// Implementation of inline methods:

inline CRef Solver_Mix::reason(Var x) const { return vardata[x].reason; }
inline int  Solver_Mix::level (Var x) const { return vardata[x].level; }

inline void Solver_Mix::insertVarOrder(Var x) {
     Heap<VarOrderLt> & order_heap = VSIDS? order_heap_VSIDS:order_heap_CHB;
     if (!order_heap.inHeap(x) && decision[x]) order_heap.insert(x); 
}

inline void Solver_Mix::varDecayActivity() {
    var_inc *= (1 / var_decay); }

inline void Solver_Mix::varBumpActivity(Var v, double mult) {
    if ( (activity_VSIDS[v] += var_inc * mult) > 1e100 ) {
        // Rescale:
        for (int i = 0; i < nVars(); i++)
            activity_VSIDS[i] *= 1e-100;
        var_inc *= 1e-100; }

    // Update order_heap with respect to new activity:
    if (order_heap_VSIDS.inHeap(v)) order_heap_VSIDS.decrease(v); }

inline void Solver_Mix::claDecayActivity() { cla_inc *= (1 / clause_decay); }
inline void Solver_Mix::claBumpActivity (Clause& c) {
    if ( (c.activity() += cla_inc) > 1e20 ) {
        // Rescale:
        for (int i = 0; i < learnts_local.size(); i++)
            ca[learnts_local[i]].activity() *= 1e-20;
        cla_inc *= 1e-20; } }

inline void Solver_Mix::checkGarbage(void){ return checkGarbage(garbage_frac); }
inline void Solver_Mix::checkGarbage(double gf){
    if (ca.wasted() > ca.size() * gf)
        garbageCollect(); }

// NOTE: enqueue does not set the ok flag! (only public methods do)
inline bool     Solver_Mix::enqueue         (Lit p, CRef from)      { return value(p) != l_Undef ? value(p) != l_False : (uncheckedEnqueue(p, decisionLevel(), from), true); }
inline bool     Solver_Mix::addClause       (const vec<Lit>& ps)    { ps.copyTo(add_tmp); return addClause_(add_tmp); }
inline bool     Solver_Mix::addEmptyClause  ()                      { add_tmp.clear(); return addClause_(add_tmp); }
inline bool     Solver_Mix::addClause       (Lit p)                 { add_tmp.clear(); add_tmp.push(p); return addClause_(add_tmp); }
inline bool     Solver_Mix::addClause       (Lit p, Lit q)          { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); return addClause_(add_tmp); }
inline bool     Solver_Mix::addClause       (Lit p, Lit q, Lit r)   { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); add_tmp.push(r); return addClause_(add_tmp); }
inline bool     Solver_Mix::locked          (const Clause& c) const {
    int i = c.size() != 2 ? 0 : (value(c[0]) == l_True ? 0 : 1);
    return value(c[i]) == l_True && reason(var(c[i])) != CRef_Undef && ca.lea(reason(var(c[i]))) == &c;
}
inline void     Solver_Mix::newDecisionLevel()                      { trail_lim.push(trail.size()); }

inline int      Solver_Mix::decisionLevel ()      const   { return trail_lim.size(); }
inline uint32_t Solver_Mix::abstractLevel (Var x) const   { return 1 << (level(x) & 31); }
inline lbool    Solver_Mix::value         (Var x) const   { return assigns[x]; }
inline lbool    Solver_Mix::value         (Lit p) const   { return assigns[var(p)] ^ sign(p); }
inline lbool    Solver_Mix::modelValue    (Var x) const   { return model[x]; }
inline lbool    Solver_Mix::modelValue    (Lit p) const   { return model[var(p)] ^ sign(p); }
inline int      Solver_Mix::nAssigns      ()      const   { return trail.size(); }
inline int      Solver_Mix::nClauses      ()      const   { return clauses.size(); }
inline int      Solver_Mix::nLearnts      ()      const   { return learnts_core.size() + learnts_tier2.size() + learnts_local.size(); }
inline int      Solver_Mix::nVars         ()      const   { return vardata.size(); }
inline int      Solver_Mix::nFreeVars     ()      const   { return (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]); }
inline void     Solver_Mix::setPolarity   (Var v, bool b) { polarity[v] = b; }
inline void     Solver_Mix::setDecisionVar(Var v, bool b) 
{ 
    if      ( b && !decision[v]) dec_vars++;
    else if (!b &&  decision[v]) dec_vars--;

    decision[v] = b;
    if (b && !order_heap_CHB.inHeap(v)){
        order_heap_CHB.insert(v);
        order_heap_VSIDS.insert(v);
    }
}
inline void     Solver_Mix::setConfBudget(int64_t x){ conflict_budget    = conflicts    + x; }
inline void     Solver_Mix::setPropBudget(int64_t x){ propagation_budget = propagations + x; }
inline void     Solver_Mix::interrupt(){ asynch_interrupt = true; }
inline void     Solver_Mix::clearInterrupt(){ asynch_interrupt = false; }
inline void     Solver_Mix::budgetOff(){ conflict_budget = propagation_budget = -1; }
inline bool     Solver_Mix::withinBudget() const {
    return !asynch_interrupt &&
            (conflict_budget    < 0 || conflicts < (uint64_t)conflict_budget) &&
            (propagation_budget < 0 || propagations < (uint64_t)propagation_budget); }

// FIXME: after the introduction of asynchronous interrruptions the solve-versions that return a
// pure bool do not give a safe interface. Either interrupts must be possible to turn off here, or
// all calls to solve must return an 'lbool'. I'm not yet sure which I prefer.
inline bool     Solver_Mix::solve         ()                    { budgetOff(); assumptions.clear(); return solve_() == l_True; }
inline bool     Solver_Mix::solve         (Lit p)               { budgetOff(); assumptions.clear(); assumptions.push(p); return solve_() == l_True; }
inline bool     Solver_Mix::solve         (Lit p, Lit q)        { budgetOff(); assumptions.clear(); assumptions.push(p); assumptions.push(q); return solve_() == l_True; }
inline bool     Solver_Mix::solve         (Lit p, Lit q, Lit r) { budgetOff(); assumptions.clear(); assumptions.push(p); assumptions.push(q); assumptions.push(r); return solve_() == l_True; }
inline bool     Solver_Mix::solve         (const vec<Lit>& assumps){ budgetOff(); assumps.copyTo(assumptions); return solve_() == l_True; }
inline lbool    Solver_Mix::solveLimited  (const vec<Lit>& assumps){ assumps.copyTo(assumptions); return solve_(); }
inline bool     Solver_Mix::okay          ()      const   { return ok; }

inline void     Solver_Mix::toDimacs     (const char* file){ vec<Lit> as; toDimacs(file, as); }
inline void     Solver_Mix::toDimacs     (const char* file, Lit p){ vec<Lit> as; as.push(p); toDimacs(file, as); }
inline void     Solver_Mix::toDimacs     (const char* file, Lit p, Lit q){ vec<Lit> as; as.push(p); as.push(q); toDimacs(file, as); }
inline void     Solver_Mix::toDimacs     (const char* file, Lit p, Lit q, Lit r){ vec<Lit> as; as.push(p); as.push(q); as.push(r); toDimacs(file, as); }

//=================================================================================================
// Debug etc:


//=================================================================================================
}

#endif