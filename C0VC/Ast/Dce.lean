/-
DCE (Dead Code Elimination)

Using initialized variables after control flow removes it from context is valid
via the typechecker but not valid by downstream passes. By implementing a
DCE pass right after typechecking and using this AST to lower to Tree,
we allow for downstream passes to not panic.

This means that if you care about program to look roughly 1-1 between C0/C1 and Boole,
the lowering should happen on the AST before elaboration and not on this DCE AST.

Author(s):
  ~ Chris Su <chrjs@cmu.edu>
-/

import C0VC.Ast.TypedAst

namespace C0VC.Dce

partial def dceMStm (mstm : C0VC.TypedAst.Stm) : C0VC.TypedAst.Stm × Bool :=
  match mstm with
  | .ret _ => (mstm, true)
  | .seq first rest =>
      let (first', firstReturns) := dceMStm first
      if firstReturns then
        (first', true)
      else
        let (rest', restReturns) := dceMStm rest
        (.seq first' rest', restReturns)
  | .ifLit test thenBranch elseBranch =>
      let (thenBranch', thenReturns) := dceMStm thenBranch
      let (elseBranch', elseReturns) := dceMStm elseBranch
      (.ifLit test thenBranch' elseBranch', thenReturns && elseReturns)
  | .whileLit test body =>
      let (body', _) := dceMStm body
      (.whileLit test body', false)
  | .declare varName type init value =>
      let (value', valueReturns) := dceMStm value
      (.declare varName type init value', valueReturns)
  | _ => (mstm, false)

def dceBody (body : List C0VC.TypedAst.Stm) : List C0VC.TypedAst.Stm :=
  match body with
  | [] => []
  | stm :: rest =>
      let (stm', stmReturns) := dceMStm stm
      if stmReturns then
        [stm']
      else
        stm' :: dceBody rest

def dceFunctionDef (fdefn : C0VC.TypedAst.FunctionDef) : C0VC.TypedAst.FunctionDef :=
  { fdefn with body := dceBody fdefn.body }

def removeAfterReturns (program : C0VC.TypedAst.Program) : C0VC.TypedAst.Program :=
  List.map dceFunctionDef program

def run (program : C0VC.TypedAst.Program) : C0VC.TypedAst.Program :=
  removeAfterReturns program

end C0VC.Dce
