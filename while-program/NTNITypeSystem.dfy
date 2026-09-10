include "WhileProgram.dfy"

/** This file defines the Nontransitive Noninterference type system
 *  which is proved to be sound for secure informaiton flow in 
 *  the while-loop programming language */

module NontransitiveFlow{
    import opened WhileProgram

    // The security labels
    type Label(==)
    const labels: set<Label>
    // The reflexive flow relation on Labels, which is a global policy
    const flow: set<(Label, Label)>
    
    // An initial labelling on variables
    // Intuitively, an "unimportant" variable may be labelled by \top 
    // which may (1) influence any other labels, and may (2) accept information in-flow from any other labels
    const coarse_label: map<Variable, Label>
    predicate policyTypeOK(){
        && coarse_label.Keys == variables
        && (forall l :: l in labels ==> (l, l) in flow) // the flow relation is reflexive !!!
        && forall x :: x in variables ==> coarse_label[x] in labels
    }

    // Defines the set of labels that can interfere with a label
    function CanFlow(l: Label): set<Label>
    requires l in labels
    ensures forall l':: l' in labels ==> ((l',l) in flow <==> l' in CanFlow(l))
    ensures CanFlow(l) <= labels
    {
        (set l' | l' in labels && (l', l) in flow :: l')
    }

    // The type language: 
    // A base type t is a set of variables, from which a set of labels can be derived by applying the coarse_label function
    // to each element in set t, which is just (set l, x | l in labels && x in t && l == coarse_label[x] :: l)
    type BaseType = set<Variable> 
    datatype PhraseType = ExprType(t: BaseType) | CmdType(t: BaseType) | Invalid
    // A context that stores a set of variables that may influence a variable
    type VContext = map<Variable, BaseType>
    predicate validContext(vctx: VContext){
        // extending the domain of ctx.Keys to any variable(s)
        // ensuring that vctx is reflexive and transitive 
        && vctx.Keys == variables 
        && policyTypeOK()
        && (forall x :: x in vctx.Keys ==> vctx[x] <= variables)
        && (forall x :: x in vctx.Keys ==> x in vctx[x])
        && (forall x, y :: x in vctx.Keys && y in vctx[x] ==> vctx[y] <= vctx[x])
        && (forall x, y :: x in vctx.Keys && y in vctx[x] ==> coarse_label[y] in CanFlow(coarse_label[x]))
    }
    function GetBaseType(t: PhraseType) : BaseType
    requires t != Invalid
    {
        match t {
            case ExprType(t') => t'
            case CmdType(t') => t'
        }
    }
    // The meet and join are now set based operators: set unionism for Join, and set intersection for Meet. 
    function Join(t1: BaseType, t2: BaseType) : BaseType
    {
        t1 + t2
    }
    function Meet(t1: BaseType, t2: BaseType) : BaseType
    {
        t1 * t2
    }

    // Test cases: 
    // (1) for all labels l, l is in the set of labels in CanFlow(l)
    // (2) the set of labels generated from a BaseType (a set of variables)
    method TestSelfFlow(l: Label, t: BaseType)
    requires l in labels
    requires t <= variables
    requires policyTypeOK()
    {
        var lset := CanFlow(l);
        // CanFlow is reflexive;
        assert l in lset;
        var t_labels := (set l, x | l in labels && x in t && l == coarse_label[x] :: l);
        assert t_labels <= labels; 
    }

    // The following defines a type system for the while programming language
    // We start with the expression types
    // In principle, this function should never produce Invalid from an Expr
    function HasExprType(vctx: VContext, e: Expr): PhraseType
    requires policyTypeOK() && vctx.Keys == variables
    requires VariablesInExpr(e) <= vctx.Keys
    requires validContext(vctx)
    ensures HasExprType(vctx, e) != Invalid
    ensures GetBaseType(HasExprType(vctx, e)) <= variables
    ensures forall x :: x in VariablesInExpr(e) ==> (vctx[x] + {x} <= GetBaseType(HasExprType(vctx, e)))
    ensures forall y :: y in GetBaseType(HasExprType(vctx, e)) ==> vctx[y] <= GetBaseType(HasExprType(vctx, e))
    decreases e
    {
        match e {
            case Num(n) => 
                ExprType({})
            case Var(x) => 
                ExprType(vctx[x]+{x}) // !!!
            case Plus(e1, e2) => 
                var t1 := HasExprType(vctx, e1); 
                var t2 := HasExprType(vctx, e2); 
                ExprType(Join(GetBaseType(t1), GetBaseType(t2)))
        }
    }
    // The type checking process for a command/statement
    // If type checking fails the return type will be Invalid
    // If type checking succeeds, it will return the set of variables (wrapped in a CmdType) that may be updated (modified) if cmd is run
    function HasCmdType(vctx: VContext, vpc: set<Variable>, c:Cmd): PhraseType
    requires policyTypeOK() && validContext(vctx)
    requires vpc <= variables
    requires VariablesInCmd(c) <= vctx.Keys 
    requires forall x :: x in vctx.Keys ==> vctx[x] <= variables
    ensures HasCmdType(vctx, vpc, c) != Invalid ==> GetBaseType(HasCmdType(vctx, vpc, c)) <= VariablesInCmd(c)
    ensures HasCmdType(vctx, vpc, c) != Invalid ==> (forall x :: x in GetBaseType(HasCmdType(vctx, vpc, c)) ==> vpc <= vctx[x])
    decreases c
    {
        match c {
            case Skip => CmdType({})
            case Assn(x, e) =>  
                // t1 is the policy label of x
                // t2 represents information from the RHS of assn
                var t1, t2 := coarse_label[x], HasExprType(vctx, e); 
                
                // get the set of labels allowed to influence label(x)
                var flowsFrom := CanFlow(t1);
                var pc_labels := (set x | x in vpc :: coarse_label[x]);
                var e_labels := (set x | x in GetBaseType(t2) :: coarse_label[x]);
                if (GetBaseType(t2) + vpc + {x}) <= vctx[x] 
                    && (e_labels + pc_labels) <= flowsFrom
                then CmdType({x}) 
                else Invalid
            case If(e, c1, c2) => 
                var te := HasExprType(vctx, e);
                var t1 := HasCmdType(vctx, vpc + GetBaseType(te), c1); 
                var t2 := HasCmdType(vctx, vpc + GetBaseType(te), c2);
                if t1 == Invalid || t2 == Invalid then Invalid
                else (CmdType(Join(GetBaseType(t1), GetBaseType(t2))))
            case While(e, c1) => 
                var te := HasExprType(vctx, e);
                var t1 := HasCmdType(vctx, vpc + GetBaseType(te), c1); 
                if t1 == Invalid then Invalid
                else t1
            case Seq(c1, c2) =>
                var t1, t2 := HasCmdType(vctx, vpc, c1), HasCmdType(vctx, vpc, c2);
                if t1 == Invalid || t2 == Invalid then Invalid
                else CmdType(Join(GetBaseType(t1), GetBaseType(t2)))
        }
    }

    /// reflexivity and transitivity in an assignment: x := e
    // (1) All information contained in e must also be contained in x, in the way that
    //     if y appears in e, then vctx[y] <= vctx[x]
    // (2) All information contained in the environment (vpc) must also be contained in x
    //     such as x is updated in an if-then-else or a while-loop structure, and the guard information is stored in vpc
    lemma AssnTransitivity(vctx: VContext, vpc: set<Variable>, x: Variable, e: Expr)
    requires policyTypeOK() && validContext(vctx)
    requires vpc <= variables
    requires VariablesInExpr(e)+{x} <= vctx.Keys <= variables
    requires forall x :: x in vctx.Keys ==> vctx[x] <= variables
    requires HasCmdType(vctx, vpc, Assn(x, e)) != Invalid
    ensures forall y :: y in VariablesInExpr(e) ==> vctx[y] <= vctx[x]
    ensures vpc <= vctx[x]
    {}
    /// The following lemma is a particular case for the inversion of the typing relation: 
    /// during the type checking for If(e,c1,c2), as an example
    lemma HasCmdIf(vctx: VContext, vpc: set<Variable>, e: Expr, c1: Cmd, c2: Cmd)
    requires policyTypeOK() && validContext(vctx)
    requires vpc <= variables
    requires VariablesInCmd(c1) + VariablesInCmd(c2) + VariablesInExpr(e) <= vctx.Keys 
    requires forall x :: x in vctx.Keys ==> vctx[x] <= variables
    requires HasCmdType(vctx, vpc, If(e, c1, c2)) != Invalid
    ensures HasCmdType(vctx, vpc + GetBaseType(HasExprType(vctx, e)), c1) != Invalid
    {}
}