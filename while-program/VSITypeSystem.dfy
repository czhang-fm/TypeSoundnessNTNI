include "WhileProgram.dfy"

/** This file defines the Volpano Smith Irvine secure type system
 *  which is proved to be sound for secure informaiton flow in 
 *  a While-loop programming language */

module VolpanoSmithIrvine{
    import opened WhileProgram

    // the type language
    datatype BaseType = High | Low | InvalidBase
    datatype PhraseType = ExprType(t: BaseType) | CmdType(t: BaseType) | Invalid

    // the type context
    type Context = map<Variable, BaseType>

    // Dafny does not support operator overloading, thus we define the
    // following subtype relation for Low <= High
    predicate SubType(t1: BaseType, t2: BaseType){
        && t1 != InvalidBase 
        && t2 != InvalidBase
        && (t1 == Low || (t1 == t2 == High))
    }
    // the join operator on security types: used for expression types
    function Join(t1: BaseType, t2: BaseType) : BaseType
    requires t1 != InvalidBase && t2 != InvalidBase
    {
        if t1 == High then t1 else t2
    }
    // the meet operator on security types: used for command types
    function Meet(t1: BaseType, t2: BaseType) : BaseType
    requires t1 != InvalidBase && t2 != InvalidBase
    {
        if t1 == Low then t1 else t2
    }
    // unwrap the based type from an expression type or a command type
    function GetBaseType(t: PhraseType) : BaseType
    {
        match t {
            case ExprType(t') => t'
            case CmdType(t') => t'
            case Invalid => InvalidBase
        }
    }
    // Join makes a subtype; Meet makes a supertype.
    lemma SubTypeJoin(t1: BaseType, t2: BaseType)
    requires t1 != InvalidBase && t2 != InvalidBase
    ensures SubType(t1, Join(t1, t2)) && SubType(t2, Join(t1, t2))
    {}

    // the subtype relation for expressions and commands
    predicate ExprSubType(t1: PhraseType, t2: PhraseType)
    requires exists t1', t2' :: t1 == ExprType(t1') && t2 == ExprType(t2')
    {
        var t1', t2' := GetBaseType(t1), GetBaseType(t2); SubType(t1', t2')
    }
    predicate CmdSubType(t1: PhraseType, t2: PhraseType)
    requires exists t1', t2' :: t1 == CmdType(t1') && t2 == CmdType(t2')
    {
        var t1', t2' := GetBaseType(t1), GetBaseType(t2); SubType(t2', t1')
    }
    // both the above subtype relations are transitive
    lemma ExprSubTypeTransitive(t1: PhraseType, t2: PhraseType, t3: PhraseType)
    requires exists t1', t2', t3' :: t1 == ExprType(t1') && t2 == ExprType(t2') && t3 == ExprType(t3')
    requires ExprSubType(t1, t2) && ExprSubType(t2, t3)
    ensures ExprSubType(t1, t3)
    {}
    lemma CmdSubTypeTransitive(t1: PhraseType, t2: PhraseType, t3: PhraseType)
    requires exists t1', t2', t3' :: t1 == CmdType(t1') && t2 == CmdType(t2') && t3 == CmdType(t3')
    requires CmdSubType(t1, t2) && CmdSubType(t2, t3)
    ensures CmdSubType(t1, t3)
    {}

    // The following defines a type system for the while programming language
    // We start with the expression types
    // This function never produces Invalid, which is left for a proof in the soundness file ....
    function HasExprType(ctx: Context, e: Expr): PhraseType
    requires VariablesInExpr(e) <= ctx.Keys
    decreases e
    {
        match e {
            case Num(n) => 
                ExprType(Low) 
            case Var(x) => 
                ExprType(ctx[x])
            case Plus(e1, e2) => 
                var t1, t2 := HasExprType(ctx, e1), HasExprType(ctx, e2); 
                var t1, t2 := GetBaseType(t1), GetBaseType(t2);
                if t1 == InvalidBase || t2 == InvalidBase then Invalid else ExprType(Join(t1, t2))
        }
    }
    // We then work with the command types: if type checking fails, the return type will be Invalid
    // Invalid type will propagate to the final return type
    function HasCmdType(ctx: Context, c: Cmd): PhraseType
    requires VariablesInCmd(c) <= ctx.Keys
    {
        match c {
            case Skip => CmdType(High)
            case Assn(x, e) => 
                var t1, t2 := GetBaseType(HasExprType(ctx, Var(x))), GetBaseType(HasExprType(ctx, e)); 
                if SubType(t2, t1) then CmdType(Join(t1, t2)) else Invalid
            case If(e, c1, c2) =>
                var t1, t2, t3 := GetBaseType(HasExprType(ctx, e)), GetBaseType(HasCmdType(ctx, c1)), GetBaseType(HasCmdType(ctx, c2));
                if SubType(t1, t2) && SubType(t1, t3) then CmdType(Meet(t2, t3))
                else Invalid
            case While(e, c1) => 
                var t1, t2 := GetBaseType(HasExprType(ctx, e)), GetBaseType(HasCmdType(ctx, c1));
                if SubType(t1, t2) then CmdType(t2)
                else Invalid
            case Seq(c1, c2) => 
                var t1, t2 := GetBaseType(HasCmdType(ctx, c1)), GetBaseType(HasCmdType(ctx, c2));
                if t1 == InvalidBase || t2 == InvalidBase then Invalid
                else CmdType(Meet(t1, t2))
        }
    }

    /** We prove the information flow property in another file named "VSITypeSoundness.dfy" */

}
