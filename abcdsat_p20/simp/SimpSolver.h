
#ifndef abcdSAT_SimpSolver_h
#define abcdSAT_SimpSolver_h

#include "mtl/Queue.h"
#include "core/Solver.h"
#include "mtl/Clone.h"

namespace abcdSAT {

//=================================================================================================


class SimpSolver : public Solver {
 public:
    SimpSolver();
    ~SimpSolver();
    
    SimpSolver(const  SimpSolver &s);
 
    // Clone function
    virtual Clone* clone() const {
        return  new SimpSolver(*this);
    }   
  
    // Problem specification:
    //
    virtual Var     newVar    (bool polarity = true, bool dvar = true); // Add a new variable with parameters specifying variable mode.
    bool    addClause (const vec<Lit>& ps);
    bool    addEmptyClause();                // Add the empty clause to the solver.
    bool    addClause (Lit p);               // Add a unit clause to the solver.
    bool    addClause (Lit p, Lit q);        // Add a binary clause to the solver.
    bool    addClause (Lit p, Lit q, Lit r); // Add a ternary clause to the solver.
    virtual bool    addClause_(      vec<Lit>& ps);
    bool    substitute(Var v, Lit x);  // Replace all occurences of v with x (may cause a contradiction).

    // Variable mode:
    // 
    void    setFrozen (Var v, bool b); // If a variable is frozen it will not be eliminated.
    bool    isEliminated(Var v) const;

    // Solving:
    //
    bool    solve       (                     bool do_simp = true, bool turn_off_simp = false);
    bool    eliminate   (bool turn_off_elim = false);  // Perform variable elimination based simplification. 
    bool    eliminate_  ();
    void    removeSatisfied();

    // Memory managment:
    //
    virtual void garbageCollect();

    // Mode of operation:
    //
    int     parsing;
    int     grow;              // Allow a variable elimination step to grow by a number of clauses (default to zero).
    int     clause_lim;        // Variables are not eliminated if it produces a resolvent with a length above this limit.
                               // -1 means no limit.
    int     subsumption_lim;   // Do not check if subsumption against a clause larger than this. -1 means no limit.
    double  simp_garbage_frac; // A different limit for when to issue a GC during simplification (Also see 'garbage_frac').

    bool    use_asymm;         // Shrink clauses by asymmetric branching.
    bool    use_rcheck;        // Check if a clause is already implied. Prett costly, and subsumes subsumptions :)
    bool    use_elim;          // Perform variable elimination.
    // Statistics:
    //
    int     merges;
    int     asymm_lits;
    int     eliminated_vars;

 protected:
    // Helper structures:
    //
    struct ElimLt {
        const vec<int>& n_occ;
        explicit ElimLt(const vec<int>& no) : n_occ(no) {}

        // TODO: are 64-bit operations here noticably bad on 32-bit platforms? Could use a saturating
        // 32-bit implementation instead then, but this will have to do for now.
        uint64_t cost  (Var x)        const { return (uint64_t)n_occ[toInt(mkLit(x))] * (uint64_t)n_occ[toInt(~mkLit(x))]; }
        bool operator()(Var x, Var y) const { return cost(x) < cost(y); }
    };

    struct ClauseDeleted {
        const ClauseAllocator& ca;
        explicit ClauseDeleted(const ClauseAllocator& _ca) : ca(_ca) {}
        bool operator()(const CRef& cr) const { return ca[cr].mark() == 1; } };

    // Solver state:
    //
    int                 elimorder;
    bool                use_simplification;
    vec<uint32_t>       elimclauses;
    vec<char>           touched;
    OccLists<Var, vec<CRef>, ClauseDeleted>
                        occurs;
    vec<int>            n_occ;
    Heap<ElimLt>        elim_heap;
    Queue<CRef>         subsumption_queue;
    vec<char>           frozen;
    vec<char>           eliminated;
    int                 bwdsub_assigns;
    int                 n_touched;

    // Temporaries:
    //
    CRef                bwdsub_tmpunit;

    // Main internal methods:
    //
public:
    lbool         ssolve_                  (bool do_simp = true, bool turn_off_simp = false);
 
    bool          asymm                    (Var v, CRef cr);
    bool          asymmVar                 (Var v);
    void          updateElimHeap           (Var v);
    void          gatherTouchedClauses     ();
    bool          merge                    (const Clause& _ps, const Clause& _qs, Var v, vec<Lit>& out_clause);
    bool          merge                    (const Clause& _ps, const Clause& _qs, Var v, int& size);
    bool          backwardSubsumptionCheck (bool verbose = false);
    bool          eliminateVar             (Var v);
    void          extendModel              ();
    void          getModel                 ();

    void          removeClause             (CRef cr);
    bool          strengthenClause         (CRef cr, Lit l);
    void          cleanUpClauses           ();
    bool          implied                  (const vec<Lit>& c);
    virtual void          relocAll                 (ClauseAllocator& to);
};


//=================================================================================================
// Implementation of inline methods:


inline bool SimpSolver::isEliminated (Var v) const { return eliminated[v]; }
inline void SimpSolver::updateElimHeap(Var v) {
    assert(use_simplification);
    // if (!frozen[v] && !isEliminated(v) && value(v) == l_Undef)
    if (elim_heap.inHeap(v) || (!frozen[v] && !isEliminated(v) && value(v) == l_Undef))
        elim_heap.update(v); }


inline bool SimpSolver::addClause    (const vec<Lit>& ps)    { ps.copyTo(add_tmp); return addClause_(add_tmp); }
inline bool SimpSolver::addEmptyClause()                     { add_tmp.clear(); return addClause_(add_tmp); }
inline bool SimpSolver::addClause    (Lit p)                 { add_tmp.clear(); add_tmp.push(p); return addClause_(add_tmp); }
inline bool SimpSolver::addClause    (Lit p, Lit q)          { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); return addClause_(add_tmp); }
inline bool SimpSolver::addClause    (Lit p, Lit q, Lit r)   { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); add_tmp.push(r); return addClause_(add_tmp); }
inline void SimpSolver::setFrozen    (Var v, bool b) { frozen[v] = (char)b; if (use_simplification && !b) { updateElimHeap(v); } }

inline bool SimpSolver::solve ( bool do_simp, bool turn_off_simp)  { budgetOff(); return ssolve_(do_simp, turn_off_simp) == l_True; }

//=================================================================================================
}

#endif
