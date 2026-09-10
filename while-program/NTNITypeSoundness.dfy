include "WhileProgram.dfy"
include "NTNITypeSystem.dfy"

module NTNISoundness {
    import opened WhileProgram
    import opened NontransitiveFlowType

    /** We prove the nontransitive information flow security is enforced by the type system
     *  NTNI security for program c:
     *  For all label l in labels, for all states M1 =CanFlow(l)= M2
     *  (M1, c) ==>* (M1', Skip) /\ (M2, c) ==>* (M2', Skip)
     *  we have M1' ={l}= M2'
     *  This says the l component of a state can only be influenced by the components labeled by l'
     *  with (l', l) in flow as defined by the (global) security policy
     */
    
    // The equivalence relation on states regarding a set of variables
    predicate Equiv(vctx: VContext, group: BaseType, s1: MState, s2: MState)
    requires vctx.Keys == s1.Keys == s2.Keys
    {
        forall x :: x in vctx.Keys && x in group  ==> s1[x] == s2[x]
    }
    // If two states are equivalent to a larger set of variables, then they
    // must look equivalent to a smaller set of variables
    lemma EquivalentStates(vctx: VContext, g1: BaseType, g2: BaseType, s1: MState, s2: MState)
    requires vctx.Keys == s1.Keys == s2.Keys
    requires g1 <= g2
    requires Equiv(vctx, g2, s1, s2)
    ensures Equiv(vctx, g1, s1, s2)
    {}
    // Next we have two properties regarding state transitions
    // First, if none of the updated variables from c is in g1, and s1 -- c --> s2, then s1 =g= s2
    // lemma LocalUpdate(vctx: VContext, g1: BaseType, HasCmdType(vctx, vpc, c) <= g2, s1: MState, s2: MState, c: Cmd)
    lemma {:induction false} LocalUpdate(vctx: VContext, vpc: set<Variable>, g1: BaseType, g2: BaseType, s1: MState, s2: MState, n: int, c: Cmd)
    requires vctx.Keys == s1.Keys == s2.Keys
    requires validContext(vctx)
    requires VariablesInCmd(c) <= vctx.Keys 
    requires vpc <= variables
    requires HasCmdType(vctx, vpc, c) != Invalid
    requires GetBaseType(HasCmdType(vctx, vpc, c)) <= g2
    requires typeOK(s1) && typeOK(s2) && n >= 0
    requires VariablesInCmd(c) <= s1.Keys == s2.Keys
    requires Terminates(c, s1, s2, n)
    requires g1 * g2 == {} // forall v :: v in g2 ==> !(v in g1)
    ensures Equiv(vctx, g1, s1, s2)
    decreases n, c
    {
        match c {
            case Skip => // trivial
            case Assn(x, e) => // assignment
            case If(e, c1, c2) => // if-then-else
                var te := HasExprType(vctx, e);
                var t1 := HasCmdType(vctx, vpc + GetBaseType(te), c1); 
                var t2 := HasCmdType(vctx, vpc + GetBaseType(te), c2);
                var s', c' := SmallStepTermination(s1, s2, c, n);
                if c' == c1 {
                    assert HasCmdType(vctx, vpc + GetBaseType(HasExprType(vctx, e)), c1) != Invalid;
                    LocalUpdate(vctx, vpc+ GetBaseType(HasExprType(vctx, e)), g1, g2, s1, s2, n-1, c1);
                } else {
                    LocalUpdate(vctx, vpc+ GetBaseType(HasExprType(vctx, e)), g1, g2, s1, s2, n-1, c2);
                }
            case  While(e, c1) => // while loop
                var te := HasExprType(vctx, e);
                var t1 := HasCmdType(vctx, vpc + GetBaseType(te), c1); 
                var res := Evaluate(s1, e);
                if res == 0 {
                    // trivial
                } else {
                    LocalUpdate(vctx, vpc + GetBaseType(HasExprType(vctx, e)), g1, g2, s1, s2, n-1, Seq(c1, c));
                }
            case Seq(c1, c2) => // sequential composition
                var t1, t2 := HasCmdType(vctx, vpc, c1), HasCmdType(vctx, vpc, c2);
                var s', n' := Sequencing(s1, s2, c1, c2, n);
                // two sub-cases
                LocalUpdate(vctx, vpc, g1, g2, s1, s', n', c1);
                LocalUpdate(vctx, vpc, g1, g2, s', s2, n-n'-1, c2);
        }
    }
    /// An auxiliary lemma for the next lemma
    lemma EquivEval(vctx: VContext, g: BaseType, s1: MState, s2: MState, e: Expr)
    requires vctx.Keys == s1.Keys == s2.Keys
    requires validContext(vctx)
    requires g <= vctx.Keys // the set of variables in the group must be in the type context
    requires VariablesInExpr(e) <= vctx.Keys 
    requires typeOK(s1) && typeOK(s2)
    requires Equiv(vctx, g, s1, s2)
    requires GetBaseType(HasExprType(vctx, e)) <= g
    ensures Evaluate(s1, e) == Evaluate(s2, e)
    {}
    // The second property: if x in g and that all variables appearing in e are also in g, then
    // given s1 =g= s2, s1 -- Assn(x, e) --> s1', and s2 -- Assn(x, e) --> s2'
    // we must have s1' =g= s2'
    lemma {:induction false} StepConsistency(vctx: VContext, vpc: set<Variable>, g: BaseType, s1: MState, s2: MState, s1': MState, s2': MState,x: Variable, e: Expr)
    requires vctx.Keys == s1.Keys == s2.Keys == s1'.Keys == s2'.Keys 
    requires validContext(vctx)
    requires g <= vctx.Keys // the set of variables in the group must be in the type context
    requires VariablesInExpr(e) + {x} <= vctx.Keys 
    requires vpc <= variables
    requires typeOK(s1) && typeOK(s2) && typeOK(s1') && typeOK(s2')
    requires vpc <= g // the control context is included in the set of variables in g
    requires GetBaseType(HasExprType(vctx, e)) <= g // the assigned value is from the set of variables in g
    requires HasCmdType(vctx, vpc, Assn(x, e)) != Invalid
    requires TransitionSmallStep(s1, Assn(x, e)) == (s1', Skip)
    requires TransitionSmallStep(s2, Assn(x, e)) == (s2', Skip)
    requires Equiv(vctx, g, s1, s2)
    ensures Equiv(vctx, g, s1', s2')
    {
        EquivEval(vctx, g, s1, s2, e);
        // assert Evaluate(s1, e) == Evaluate(s2, e);
        assert s1'[x] == s2'[x];
    }
    // The following lemmas form the centre of the proof. 
    // Suppose v is a variable, MaxSet(v) is the set of variables that may influcence v   
    // Then we can treat MaxSet(v) as the set of variables of Low level, which should not be influenced by all the other variables
    function MaxSet(vctx: VContext, vpc: set<Variable>, c:Cmd, vset: set<Variable>): set<Variable>
    requires vset <= variables 
    requires validContext(vctx)
    requires vpc <= variables
    requires VariablesInCmd(c) <= vctx.Keys 
    // requires forall x :: x in vctx.Keys ==> vctx[x] <= variables
    requires forall y :: y in vpc ==> vctx[y] <= vpc
    requires HasCmdType(vctx, vpc, c) != Invalid
    {
        (set v1, v2 | v1 in vset && v2 in vctx[v1] :: v2)
    }
    /// The set of Maximal allowed variables are automatically reflexive and transitive
    /// We also show that this set also complies with the policy defined by CanFlow 
    /// (this is not provable if not all variables vset are updated in the program execution)
    lemma MaxSetCanFlow(vctx: VContext, vpc: set<Variable>, c:Cmd, vset: set<Variable>)
    requires validContext(vctx)
    requires vset <= variables 
    requires vpc <= variables
    requires VariablesInCmd(c) <= vctx.Keys 
    requires forall y :: y in vpc ==> vctx[y] <= vpc // vpc is transitive
    requires HasCmdType(vctx, vpc, c) != Invalid
    ensures forall x, y :: x in vctx.Keys && x in MaxSet(vctx, vpc, c, vset * GetBaseType(HasCmdType(vctx, vpc, c))) && y in vctx[x] ==> 
        (x in vctx[x] && vctx[y] <= vctx[x] <= MaxSet(vctx, vpc, c, vset * GetBaseType(HasCmdType(vctx, vpc, c))))
    ensures forall x, y :: x in vctx.Keys && x in MaxSet(vctx, vpc, c, vset * GetBaseType(HasCmdType(vctx, vpc, c))) && y in vctx[x] ==> 
        coarse_label[y] in CanFlow(coarse_label[x])
    {}

    // // We define for an arbitrary set of variables, MaxSet(vset) is the set of variables that may influcence variables in vset
    // // We shall then treat MaxSet(vset) as the set of variables of Low level, which should not be influenced by all the other variables
    lemma {:induction false} MaxSetConsistency(vctx: VContext, 
                             vpc: set<Variable>, 
                            vset: set<Variable>, 
                              s1: MState, s2: MState, s1': MState, s2': MState, 
                              k1: int, k2: int, c:Cmd)
    requires vctx.Keys == s1.Keys == s2.Keys == s1'.Keys == s2'.Keys 
    requires validContext(vctx)
    requires vset <= vctx.Keys // the set of variables in the group must be in the type context
    requires vpc <= variables
    requires typeOK(s1) && typeOK(s2) && typeOK(s1') && typeOK(s2')
    requires vpc <= vset // the control context is included in the set of variables in vset, need more properties (1,2,3) for vset
    requires VariablesInCmd(c) <= vctx.Keys 
    requires HasCmdType(vctx, vpc, c) != Invalid
    requires forall x, y :: x in vset && y in vctx[x] ==> vctx[y] <= vctx[x] <= vset
    requires forall x, y :: x in vset && y in vctx[x] ==> coarse_label[y] in CanFlow(coarse_label[x])
    requires Equiv(vctx, vset, s1, s2)
    requires k1 >= 0 && Terminates(c, s1, s1', k1)
    requires k2 >= 0 && Terminates(c, s2, s2', k2)
    ensures Equiv(vctx, vset, s1', s2')
    decreases k1, k2, c
    {
        match c {
            case Skip => // termination
            case Assn(x, e) => // assignment
                if x in vset { 
                    var vpce := GetBaseType(HasExprType(vctx, e));
                    assert GetBaseType(HasCmdType(vctx, vpc, c)) <= vset;
                    EquivEval(vctx, vpce, s1, s2, e);
                    assert Evaluate(s1, e) == Evaluate(s2, e);
                } else { // values in vset remain the same
                    LocalUpdate(vctx, vpc, vset, {x}, s1, s1', k1, c);
                    LocalUpdate(vctx, vpc, vset, {x}, s2, s2', k2, c);
                    assert Equiv(vctx, vset, s1', s2');
                }
            case If(e, c1, c2) => // if-then-else
                var vpce := GetBaseType(HasExprType(vctx, e));
                if (GetBaseType(HasCmdType(vctx, vpc, c)) * vset) != {}
                {
                    var x :| x in (GetBaseType(HasCmdType(vctx, vpc, c)) * vset);
                    assert vpce <= vctx[x];
                    assert vpce <= vset; 
                    assert Equiv(vctx, vpce, s1, s2);
                    EquivEval(vctx, vpce, s1, s2, e);
                    assert Evaluate(s1, e) == Evaluate(s2, e);
                    var res := Evaluate(s1, e);
                    if res != 0 {
                        assert k1-1 >= 0 && Terminates(c1, s1, s1', k1-1);
                        assert k2-1 >= 0 && Terminates(c1, s2, s2', k2-1);
                        MaxSetConsistency(vctx, vpc + vpce, vset, s1, s2, s1', s2', k1-1, k2-1, c1);
                    } else {
                        assert k1-1 >= 0 && Terminates(c2, s1, s1', k1-1);
                        assert k2-1 >= 0 && Terminates(c2, s2, s2', k2-1);
                        MaxSetConsistency(vctx, vpc + vpce, vset, s1, s2, s1', s2', k1-1, k2-1, c2);
                    }
                } else {
                    // (GetBaseType(HasCmdType(vctx, vpc, c)) * vset) == {}
                    var vars := GetBaseType(HasCmdType(vctx, vpc, c));
                    LocalUpdate(vctx, vpc, vset, vars, s1, s1', k1, c);
                    LocalUpdate(vctx, vpc, vset, vars, s2, s2', k2, c);
                    assert Equiv(vctx, vset, s1', s2');
                }
            case While(e, c1) => // while-loop
                var vpce := GetBaseType(HasExprType(vctx, e));
                if (GetBaseType(HasCmdType(vctx, vpc, c)) * vset) != {}
                {
                    var x :| x in (GetBaseType(HasCmdType(vctx, vpc, c)) * vset);
                    assert vpce <= vctx[x];
                    assert vpce <= vset; 
                    assert Equiv(vctx, vpce, s1, s2);
                    EquivEval(vctx, vpce, s1, s2, e);
                    assert Evaluate(s1, e) == Evaluate(s2, e);
                    var res := Evaluate(s1, e);
                    if res != 0 {
                        assert k1-1 >= 0 && Terminates(Seq(c1, c), s1, s1', k1-1);
                        assert k2-1 >= 0 && Terminates(Seq(c1, c), s2, s2', k2-1);
                        MaxSetConsistency(vctx, vpc + vpce, vset, s1, s2, s1', s2', k1-1, k2-1, Seq(c1, c));
                    } else {} // trivial
                } else {
                    // (GetBaseType(HasCmdType(vctx, vpc, c)) * vset) == {}
                    var vars := GetBaseType(HasCmdType(vctx, vpc, c));
                    LocalUpdate(vctx, vpc, vset, vars, s1, s1', k1, c);
                    LocalUpdate(vctx, vpc, vset, vars, s2, s2', k2, c);
                    assert Equiv(vctx, vset, s1', s2');
                }
            case Seq(c1, c2) => // sequential composition
                var s12, k12 := Sequencing(s1, s1', c1, c2, k1);
                var s22, k22 := Sequencing(s2, s2', c1, c2, k2);
                MaxSetConsistency(vctx, vpc, vset, s1, s2, s12, s22, k12, k22, c1);
                MaxSetConsistency(vctx, vpc, vset, s12, s22, s1', s2', k1-k12-1, k2-k22-1, c2);
        }
    }
    // The NTNI security by NTNI type system (Theorem 2 in the paper)
    lemma {:induction false} Noninterference(vctx: VContext,
                               l: Label, 
                              s1: MState, s2: MState, s1': MState, s2': MState, 
                              k1: int, k2: int, c:Cmd)
    requires vctx.Keys == s1.Keys == s2.Keys == s1'.Keys == s2'.Keys 
    requires l in labels
    requires validContext(vctx)
    requires forall x :: x in variables && coarse_label[x] == l ==> x in vctx.Keys // the set of variables that has the label l
    requires typeOK(s1) && typeOK(s2) && typeOK(s1') && typeOK(s2')
    requires VariablesInCmd(c) <= vctx.Keys 
    requires HasCmdType(vctx, {}, c) != Invalid // c passes type checking
    requires Equiv(vctx, (set x | x in variables && coarse_label[x] in CanFlow(l) :: x), s1, s2)
    requires k1 >= 0 && Terminates(c, s1, s1', k1)
    requires k2 >= 0 && Terminates(c, s2, s2', k2)
    ensures Equiv(vctx, (set x | x in variables && coarse_label[x] == l :: x), s1', s2')
    {
        var maxVars := MaxSet(vctx, {}, c, (set x | x in variables && coarse_label[x] == l :: x));
        assert (set x | x in variables && coarse_label[x] == l :: x) <= maxVars;
        assert maxVars <= (set x | x in variables && coarse_label[x] in CanFlow(l) :: x);
        assert forall x, y :: x in maxVars && y in vctx[x] ==> y in maxVars; 
        EquivalentStates(vctx, maxVars, (set x | x in variables && coarse_label[x] in CanFlow(l) :: x), s1, s2);
        assert Equiv(vctx, maxVars, s1, s2); 
        MaxSetConsistency(vctx, {}, maxVars, s1, s2, s1', s2', k1, k2, c);
    }
}
