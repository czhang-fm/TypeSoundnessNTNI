include "WhileProgram.dfy"
include "VSITypeSystem.dfy"

module VSISoundness {
    import opened WhileProgram
    import opened VolpanoSmithIrvine

    /** In the following we prove the type information is preserved by SOS */
    lemma SubjectReduction(s: MState, ctx: Context, c: Cmd) returns (s': MState, c': Cmd)
    requires typeOK(s) && VariablesInCmd(c) <= s.Keys
    requires VariablesInCmd(c) <= ctx.Keys
    requires HasCmdType(ctx, c) != Invalid
    ensures TransitionSmallStep(s, c) == (s', c')
    ensures VariablesInCmd(c') <= ctx.Keys
    ensures HasCmdType(ctx, c') != Invalid
    {
        match c{
            case Skip => // termination
                s', c' := s, c; 
                assert TransitionSmallStep(s, c) == (s', c');
            case Assn(x, e) => // assignment
                s', c' := s[x:= Evaluate(s, e)], Skip;
                assert TransitionSmallStep(s, c) == (s', c');
                assert VariablesInCmd(c') <= ctx.Keys;
            case If(e, c1, c2) => // if-then-else
                var res := Evaluate(s, e);
                if (res != 0) {
                    s', c' := s, c1;
                } else {
                    s', c' := s, c2;
                } 
                assert TransitionSmallStep(s, c) == (s', c');
                assert VariablesInCmd(c') <= ctx.Keys;
            case While(e, c1) => // while-loop
                var res := Evaluate(s, e);
                if (res != 0) {
                    s', c' := s, Seq(c1, c);
                } else {
                    s', c' := s, Skip;
                } 
                assert TransitionSmallStep(s, c) == (s', c');
                assert VariablesInCmd(c') <= ctx.Keys;
            case Seq(c1, c2) => // sequential composition
                match c1 {
                    case Skip => 
                        s', c' := s, c2; 
                        assert TransitionSmallStep(s, c) == (s', c');
                    case _ => 
                        var s1', c1' := SubjectReduction(s, ctx, c1); 
                        s' := s1';
                        c' := Seq(c1', c2);
                        assert TransitionSmallStep(s, c) == (s', c');
                }
                assert VariablesInCmd(c') <= ctx.Keys;
        }
    }

    /**  We prove the information flow security is enforced by the VSI type checking
     */
    // Low equivalent states
    predicate LowEquiv(ctx: Context, s1: MState, s2: MState)
    requires ctx.Keys == s1.Keys == s2.Keys
    {
        forall x :: x in ctx.Keys && ctx[x] == Low ==> s1[x] == s2[x]
    }
    // First, we show that every expression (not Cmd) has a valid type
    lemma ValidExprType(ctx: Context, e: Expr)
    requires VariablesInExpr(e) <= ctx.Keys
    requires forall x :: x in ctx.Keys ==> ctx[x] != InvalidBase
    ensures HasExprType(ctx, e) != Invalid
    ensures GetBaseType(HasExprType(ctx, e)) != InvalidBase
    {}
    // If e is typed Low, then e only contains variables of type Low *** 
    lemma {:induction false} SimpleSecurity(ctx: Context, e: Expr, x: Variable)
    requires VariablesInExpr(e) <= ctx.Keys
    requires HasExprType(ctx, e) == ExprType(Low)
    requires forall x :: x in ctx.Keys ==> ctx[x] != InvalidBase
    requires x in VariablesInExpr(e) 
    ensures ctx[x] == Low
    {
        match e {
            case Num(_) => assert (! (x in VariablesInExpr(e))); assert false;
            case Var(y) => assert x == y;
            case Plus(e1, e2) => 
                assert Join(GetBaseType(HasExprType(ctx, e1)), GetBaseType(HasExprType(ctx, e2))) == Low;
                ValidExprType(ctx, e1);
                SubTypeJoin(GetBaseType(HasExprType(ctx, e1)), Join(GetBaseType(HasExprType(ctx, e1)), GetBaseType(HasExprType(ctx, e2))));
                assert GetBaseType(HasExprType(ctx, e1)) == Low;
                if (x in VariablesInExpr(e1)){
                    SimpleSecurity(ctx, e1, x);
                } else {
                    assert x in VariablesInExpr(e2);
                    SimpleSecurity(ctx, e2, x);
                }
        }
    }

    // Low equivalent expressions
    lemma {:induction false} LowEquivExpr(ctx: Context, s1: MState, s2: MState, e: Expr)
    requires ctx.Keys == s1.Keys == s2.Keys
    requires typeOK(s1) && typeOK(s2)
    requires VariablesInExpr(e) <= ctx.Keys
    requires forall x :: x in ctx.Keys ==> ctx[x] != InvalidBase
    requires LowEquiv(ctx, s1, s2)
    requires HasExprType(ctx, e) == ExprType(Low)
    ensures Evaluate(s1, e) == Evaluate(s2, e)
    {
        match e {
            case Num(_) => assert Evaluate(s1, e) == Evaluate(s2, e);
            case Var(x) => 
                assert ctx[x] == Low;
            case Plus(e1, e2) => 
                assert Join(GetBaseType(HasExprType(ctx, e1)), GetBaseType(HasExprType(ctx, e2))) == Low;
                ValidExprType(ctx, e1);
                SubTypeJoin(GetBaseType(HasExprType(ctx, e1)), Join(GetBaseType(HasExprType(ctx, e1)), GetBaseType(HasExprType(ctx, e2))));
                assert HasExprType(ctx, e1) == ExprType(Low);
                LowEquivExpr(ctx, s1, s2, e1);
                LowEquivExpr(ctx, s1, s2, e2);
        }
    }

    // Confinement: if a program is typed High, then only High variables are updated during the execution
    // Given s1 ==>* s2, then only High variables are updated iff s1 =Low= s2
    lemma {:induction false} Confinement(ctx: Context, s1: MState, s2: MState, c: Cmd, k: int)
    requires ctx.Keys == s1.Keys == s2.Keys
    requires typeOK(s1) && typeOK(s2)
    requires VariablesInCmd(c) <= ctx.Keys
    requires forall x :: x in ctx.Keys ==> ctx[x] != InvalidBase
    requires HasCmdType(ctx, c) == CmdType(High)
    requires k >= 0 && Terminates(c, s1, s2, k)
    ensures LowEquiv(ctx, s1, s2)
    decreases k, c
    {
        match c {
            case Skip => assert LowEquiv(ctx, s1, s2); // trivial
            case Assn(x, e) => // assignment
                assert ctx[x] == High; 
            case If(e, c1, c2) => // if-then-else
                assert HasCmdType(ctx, c1) == CmdType(High);
                assert HasCmdType(ctx, c2) == CmdType(High);
                var s', c' := SmallStepTermination(s1, s2, c, k);
                if c' == c1 {
                    Confinement(ctx, s', s2, c1, k-1);
                } else {
                    Confinement(ctx, s', s2, c2, k-1);
                }
            case While(e, c1) => // while-loop
                var s', c' := SmallStepTermination(s1, s2, c, k);
                if c' == Skip {
                    assert LowEquiv(ctx, s1, s2);
                } else {
                    assert LowEquiv(ctx, s1, s');
                    Confinement(ctx, s', s2, Seq(c1, c), k-1);
                }
            case Seq(c1, c2) => // sequential composition
                var s', k' := Sequencing(s1, s2, c1, c2, k);
                Confinement(ctx, s1, s', c1, k');
                Confinement(ctx, s', s2, c2, k-k'-1);
        }
    }

    // Finally, the Noninterference property is proved in the following lemma
    // ctx |- c /\ ctx |- s1 =Low= s2 /\ s1 ==>* s1' /\ s2 ==>* s2'
    // then ctx |- s1' =Low= s2'
    // (Theorem 1 in the paper)
    lemma Noninterference(ctx: Context, s1: MState, s2: MState, c: Cmd, 
            s1': MState, s2': MState, k1: int, k2: int)
    requires ctx.Keys == s1.Keys == s2.Keys == s1'.Keys == s2'.Keys
    requires typeOK(s1) && typeOK(s2) && typeOK(s1') && typeOK(s2')
    requires VariablesInCmd(c) <= ctx.Keys
    requires forall x :: x in ctx.Keys ==> ctx[x] != InvalidBase
    requires HasCmdType(ctx, c) != Invalid // c is well typed under ctx
    requires LowEquiv(ctx, s1, s2)
    requires k1 >= 0 && Terminates(c, s1, s1', k1)
    requires k2 >= 0 && Terminates(c, s2, s2', k2)
    ensures LowEquiv(ctx, s1', s2')
    decreases k1, k2, c
    {
        match c {
            case Skip => assert LowEquiv(ctx, s1', s2'); // trivial
            case Assn(x, e) => // assignment
                if HasCmdType(ctx, c) == CmdType(High) {
                    Confinement(ctx, s1, s1', c, k1);
                    Confinement(ctx, s2, s2', c, k2);
                } else { // CmdType(Low)
                    LowEquivExpr(ctx, s1, s2, e); 
                }
            case If(e, c1, c2) => // if-then-else
                if HasCmdType(ctx, c) == CmdType(High) {
                    Confinement(ctx, s1, s1', c, k1); // Dafny identifies transitivity of Low-equiv
                    Confinement(ctx, s2, s2', c, k2);
                } else { // CmdType(Low)
                    assert HasExprType(ctx, e) == ExprType(Low);
                    LowEquivExpr(ctx, s1, s2, e); 
                    var res := Evaluate(s1, e); 
                    if res != 0 {
                        Noninterference(ctx, s1, s2, c1, s1', s2', k1-1, k2-1);
                    } else {
                        Noninterference(ctx, s1, s2, c2, s1', s2', k1-1, k2-1);
                    }
                }
            case While(e, c1) => // while-loop
                if HasCmdType(ctx, c) == CmdType(High) {
                    Confinement(ctx, s1, s1', c, k1);
                    Confinement(ctx, s2, s2', c, k2);
                } else { // CmdType(Low)
                    LowEquivExpr(ctx, s1, s2, e); 
                    var res := Evaluate(s1, e);
                    if res == 0 {
                        assert (s1, Skip) == TransitionSmallStep(s1, c); // trivial
                    } else {
                        Noninterference(ctx, s1, s2, Seq(c1, c), s1', s2', k1-1, k2-1);
                    }
                }
            case Seq(c1, c2) => // sequential composition
                var s12, k12 := Sequencing(s1, s1', c1, c2, k1);
                var s22, k22 := Sequencing(s2, s2', c1, c2, k2);
                Noninterference(ctx, s1, s2, c1, s12, s22, k12, k22);
                Noninterference(ctx, s12, s22, c2, s1', s2', k1-k12-1, k2-k22-1);
        }
    }
}