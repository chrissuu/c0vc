import C0VC.Ast.TypedAst

namespace C0VC.LowerAnnotations

private def invariantAssert (e : C0VC.TypedAst.TypedExpr) : C0VC.TypedAst.Stm :=
  .assert e

private partial def appendStm (stm extra : C0VC.TypedAst.Stm) : C0VC.TypedAst.Stm :=
  match stm with
  | .nop => extra
  | .seq first rest => .seq first (appendStm rest extra)
  | .declare varName type init body => .declare varName type init (appendStm body extra)
  | _ => .seq stm extra

mutual
private partial def lowerStm : C0VC.TypedAst.Stm → C0VC.TypedAst.Stm
  | .ifLit test thenBranch elseBranch =>
      .ifLit test (lowerStm thenBranch) (lowerStm elseBranch)
  | .whileLit test body =>
      .whileLit test (lowerStm body)
  | .declare varName type init body =>
      .declare varName type init (lowerStm body)
  | .seq first rest =>
      let first' := lowerStm first
      let rest' := lowerStm rest
      match first' with
      | .annotation (.loopInvariant inv) =>
          lowerInvariantBefore inv rest'
      | _ =>
          .seq first' rest'
  | stm => stm

private partial def lowerInvariantBefore
    (inv : C0VC.TypedAst.TypedExpr) (stm : C0VC.TypedAst.Stm) : C0VC.TypedAst.Stm :=
  match stm with
  | .whileLit test body =>
      let check := invariantAssert inv
      .seq check (.whileLit test (appendStm body check))
  | .seq first rest =>
      match first with
      | .whileLit test body =>
          let check := invariantAssert inv
          .seq check (.seq (.whileLit test (appendStm body check)) rest)
      | _ =>
          .seq (.annotation (.loopInvariant inv)) stm
  | _ =>
      .seq (.annotation (.loopInvariant inv)) stm
end

def lowerFunctionDef (fdefn : C0VC.TypedAst.FunctionDef) : C0VC.TypedAst.FunctionDef :=
  { fdefn with body := fdefn.body.map lowerStm }

def run (program : C0VC.TypedAst.Program) : C0VC.TypedAst.Program :=
  program.map lowerFunctionDef

end C0VC.LowerAnnotations
