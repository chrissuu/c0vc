import C0VC.LLVM.Tree
import C0VC.LLVM.IR
import C0VC.LLVM.Runtime
import C0VC.Utils.Temp
import C0VC.Utils.Label
import Std.Data.HashMap

open C0VC.LLVM.Tree
open C0VC.LLVM.IR
open C0VC.Utils.Temp
open C0VC.Utils.Label
open Std.HashMap
open C0VC.LLVM.Runtime

namespace C0VC.LLVM.Codegen

structure FunctionInfo where
  retTau : IR.Tau
  argsTau : List IR.Tau
  external : Bool
deriving Inhabited

abbrev FEnv := Std.HashMap String FunctionInfo
abbrev SEnv := Std.HashMap String (List Tree.Tau)

structure Config where
  safetyChecks : Bool := true
deriving Inhabited

structure TempInfo where
  temp : Temp
  tau : IR.Tau
  isPtr : Bool
deriving Inhabited

abbrev TEnv := Std.HashMap String TempInfo

def ppTempInfo (tInfo : TempInfo) : String :=
  s!"{tInfo.temp.name} : {IR.Print.ppTau tInfo.tau}"

def translateBinOp : Tree.BinOp → IR.BinOp
  | .plus => .add
  | .sub => .sub
  | .mul => .mul
  | .div => .sdiv
  | .mod => .srem
  | .bitAnd => .and
  | .xor => .xor
  | .bitOr => .or
  | .shl => .shl
  | .shr => .ashr
  | .lt => .slt
  | .lte => .sle
  | .gt => .sgt
  | .gte => .sge
  | .eq => .eq
  | .neq => .ne

def isCmpOp : Tree.BinOp → Bool
  | .plus
  | .sub
  | .mul
  | .div
  | .mod
  | .bitAnd
  | .xor
  | .bitOr
  | .shl
  | .shr => false
  | .lt
  | .lte
  | .gt
  | .gte
  | .eq
  | .neq => true

def tauOfBinOp : Tree.BinOp → IR.Tau
  | .plus
  | .sub
  | .mul
  | .div
  | .mod
  | .bitAnd
  | .xor
  | .bitOr
  | .shl
  | .shr => .i32
  | .lt
  | .lte
  | .gt
  | .gte
  | .eq
  | .neq => .i1

def runtimeFunctionInfo (fn : Runtime.Fn) : FunctionInfo :=
  { retTau := Runtime.retTau fn, argsTau := Runtime.argsTau fn, external := true }

def alignTo (offset align : Int) : Int :=
  if align <= 1 then
    offset
  else
    let rem := offset % align
    if rem == 0 then offset else offset + (align - rem)

mutual
partial def treeTauAlign (senv : SEnv) : Tree.Tau → Int
  | .int => 4
  | .bool => 1
  | .void => 1
  | .ptr _ | .array _ | .null => 8
  | .struct name =>
      match senv.get? name with
      | some fields =>
          fields.foldl (fun acc tau => max acc (treeTauAlign senv tau)) 1
      | none => 8

partial def treeTauSize (senv : SEnv) : Tree.Tau → Int
  | .int => 4
  | .bool => 1
  | .void => 0
  | .ptr _ | .array _ | .null => 8
  | .struct name =>
      match senv.get? name with
      | some fields =>
          let (size, structAlign) :=
            fields.foldl
              (fun (offset, maxAlign) tau =>
                let fieldAlign := treeTauAlign senv tau
                let offset' := alignTo offset fieldAlign
                (offset' + treeTauSize senv tau, max maxAlign fieldAlign))
              (0, 1)
          alignTo size structAlign
      | none => 8
end

def calleeOfName (fenv : FEnv) (fname : String) : IR.Callee :=
  match fenv.get? fname with
  | some fInfo =>
      if fInfo.external then
        .external fname
      else
        .source fname
  | none => .source fname

def isAtom : Tree.Expr → Bool
  | .const _ _ | .temp _ => true
  | _ => false

def translateTau : Tree.Tau → IR.Tau
  | .int => .i32
  | .bool => .i1
  | .void => .void
  | .ptr _ | .array _ | .null => .ptr
  | .struct name => .struct name

def checkedPtrIfNeeded (cfg : Config) (ptr : IR.Val) (tc : TempCounter) :
    List IR.Stm × IR.Val × TempCounter :=
  if cfg.safetyChecks then
    let (temp, tc') := Temp.bumpAndCreate tc
    ( [ .assign (.var temp) (.call .ptr (.runtime (Runtime.name .checkPtr)) [(.ptr, ptr)]) ]
    , .var temp
    , tc')
  else
    ([], ptr, tc)

def checkedArrayAccessIfNeeded (cfg : Config) (arr index : IR.Val) (tc : TempCounter) :
    List IR.Stm × IR.Val × TempCounter :=
  if cfg.safetyChecks then
    let (temp, tc') := Temp.bumpAndCreate tc
    ( [ .assign (.var temp) (.call .ptr (.runtime (Runtime.name .checkArrayAccess)) [(.ptr, arr), (.i32, index)]) ]
    , .var temp
    , tc')
  else
    ([], arr, tc)

mutual
partial def translateAddr (cfg : Config) (senv : SEnv) (expr : Tree.Expr) (tc : TempCounter) (fenv : FEnv) (tenv : TEnv): List IR.Stm × IR.Val × IR.Tau × TempCounter × TEnv :=
  match expr with
  | .temp var =>
    match tenv.get? var.name with
    | some tempInfo =>
      if tempInfo.isPtr then
        ([], .ptr tempInfo.temp, tempInfo.tau, tc, tenv)
      else
        let (ptr, tc') := Temp.bumpAndCreate tc
        ( [ .alloca (.ptr ptr) tempInfo.tau
          , .store tempInfo.tau (.var tempInfo.temp) (.ptr ptr) ]
        , .ptr ptr
        , tempInfo.tau
        , tc'
        , tenv)
    | none => panic! s!"[Error] saw a var ({var.name}) used before being defined"

  | .deref ptr tau =>
    let (stmsPtr, transPtr, _, tc', tenv') := translateExpr cfg senv ptr tc fenv tenv
    let (checkStms, checkedPtr, tc'') := checkedPtrIfNeeded cfg transPtr tc'
    (stmsPtr ++ checkStms, checkedPtr, translateTau tau, tc'', tenv')

  | .dot struct structName fieldIndex fieldTau =>
    let (stmsStruct, structPtr, _, tc', tenv') := translateAddr cfg senv struct tc fenv tenv
    let (gepTemp, tc'') := Temp.bumpAndCreate tc'
    let fieldIndexVal : IR.Val := .bitVec (BitVec.ofInt 32 fieldIndex)
    ( stmsStruct ++ [ .gep (.ptr gepTemp) (.struct structName) structPtr [(.i32, .bitVec 0), (.i32, fieldIndexVal)] ]
    , .ptr gepTemp
    , translateTau fieldTau
    , tc''
    , tenv')

  | .arrow structPtr structName fieldIndex fieldTau =>
    let (stmsStructPtr, transStructPtr, _, tc', tenv') := translateExpr cfg senv structPtr tc fenv tenv
    let (checkStms, checkedStructPtr, tc'') := checkedPtrIfNeeded cfg transStructPtr tc'
    let (gepTemp, tc''') := Temp.bumpAndCreate tc''
    let fieldIndexVal : IR.Val := .bitVec (BitVec.ofInt 32 fieldIndex)
    ( stmsStructPtr ++ checkStms ++ [ .gep (.ptr gepTemp) (.struct structName) checkedStructPtr [(.i32, .bitVec 0), (.i32, fieldIndexVal)] ]
    , .ptr gepTemp
    , translateTau fieldTau
    , tc'''
    , tenv')

  | .arrAccess arr index elemTau =>
    let (stmsArr, transArr, _, tc', tenv') := translateExpr cfg senv arr tc fenv tenv
    let (stmsIndex, transIndex, _, tc'', tenv'') := translateExpr cfg senv index tc' fenv tenv'
    let (checkStms, checkedArr, tc''') := checkedArrayAccessIfNeeded cfg transArr transIndex tc''
    let (gepTemp, tc'''') := Temp.bumpAndCreate tc'''
    ( stmsArr ++ stmsIndex ++ checkStms ++ [ .gep (.ptr gepTemp) (translateTau elemTau) checkedArr [(.i32, transIndex)] ]
    , .ptr gepTemp
    , translateTau elemTau
    , tc''''
    , tenv'')

  | _ =>
    let (stms, transVal, tau, tc', tenv') := translateExpr cfg senv expr tc fenv tenv
    let (ptr, tc'') := Temp.bumpAndCreate tc'
    ( stms ++ [ .alloca (.ptr ptr) tau, .store tau transVal (.ptr ptr) ]
    , .ptr ptr
    , tau
    , tc''
    , tenv')

partial def translateExpr (cfg : Config) (senv : SEnv) (expr : Tree.Expr) (tc : TempCounter) (fenv : FEnv) (tenv : TEnv): List IR.Stm × IR.Val × IR.Tau × TempCounter × TEnv :=
  match expr with
  | .const tau val =>
    ( []
    , .bitVec (BitVec.ofInt 32 (Int32.toInt val))
    , translateTau tau
    , tc
    , tenv)

  | .temp var =>
    -- Look-up var in env and if it exists, use it.
    -- Not existing in the env is an impossible case, since this implies it is used before
    -- being defined.
    match tenv.get? var.name with
    | some tempInfo =>
      match tempInfo.isPtr with
      | true =>
        let (temp, tc') := Temp.bumpAndCreate tc
        ( [ .load (.var temp) tempInfo.tau (.ptr tempInfo.temp) ]
        , .var temp
        , tempInfo.tau
        , tc'
        , tenv)

      | false =>
        ( []
        , .var tempInfo.temp
        , tempInfo.tau
        , tc
        , tenv)

    | none => panic! s!"[Error] saw a var ({var.name}) used before being defined"

  | .binop op tau lhs rhs =>
    -- let tau : IR.Tau := if isCmpOp op then .i1 else .i32
    let (stmsLhs, transLhs, _, tc', tenv') := translateExpr cfg senv lhs tc fenv tenv
    let (stmsRhs, transRhs, _, tc'', tenv'') := translateExpr cfg senv rhs tc' fenv tenv'
    let (temp, tc''') := Temp.bumpAndCreate tc''
    ( stmsLhs ++ stmsRhs ++ [ .assign (.var temp) (.binop (translateBinOp op) (translateTau tau) transLhs transRhs) ]
    , .var temp
    , tauOfBinOp op
    , tc'''
    , tenv''
    )

  | .call fname args =>
    let (stms, transArgs, tc', tenv') :=
      List.foldr
      (λ expr (stmsAcc, argsAcc, tcAcc, tenvAcc) =>
        let (stms', expr', _, tc', tenv') := translateExpr cfg senv expr tcAcc fenv tenvAcc
        (stms' ++ stmsAcc, expr' :: argsAcc, tc', tenv')
      )
      ([], [], tc, tenv)
      args
    let fInfo := fenv.get! fname
    let (retTau, argsTau) := (fInfo.retTau, fInfo.argsTau)
    let callee := calleeOfName fenv fname
    match retTau with
    | .void =>
      ( stms ++ [.callVoid callee (List.zip argsTau transArgs)]
      , .void
      , retTau
      , tc'
      , tenv'
      )
    | _ =>
      let (temp, tc'') := Temp.bumpAndCreate tc'
      ( stms ++ [ .assign (.var temp) (.call retTau callee (List.zip argsTau transArgs)) ]
      , .var temp
      , retTau
      , tc''
      , tenv'
      )

  | .runtimeCall fn args =>
    let (stms, transArgs, tc', tenv') :=
      List.foldr
      (λ expr (stmsAcc, argsAcc, tcAcc, tenvAcc) =>
        let (stms', expr', _, tc', tenv') := translateExpr cfg senv expr tcAcc fenv tenvAcc
        (stms' ++ stmsAcc, expr' :: argsAcc, tc', tenv')
      )
      ([], [], tc, tenv)
      args
    let callee := IR.Callee.runtime (Runtime.name fn)
    let fInfo := runtimeFunctionInfo fn
    let (retTau, argsTau) := (fInfo.retTau, fInfo.argsTau)
    match retTau with
    | .void =>
      ( stms ++ [.callVoid callee (List.zip argsTau transArgs)]
      , .void
      , retTau
      , tc'
      , tenv'
      )
    | _ =>
      let (temp, tc'') := Temp.bumpAndCreate tc'
      ( stms ++ [ .assign (.var temp) (.call retTau callee (List.zip argsTau transArgs)) ]
      , .var temp
      , retTau
      , tc''
      , tenv'
      )

  | .null =>
    ([], .null, .ptr, tc, tenv)

  | .alloc tau =>
    let (temp, tc') := Temp.bumpAndCreate tc
    let sizeVal : IR.Val := .bitVec (BitVec.ofInt 32 (treeTauSize senv tau))
    ( [ .assign (.var temp) (.call .ptr (.runtime (Runtime.name .alloc)) [(.i32, sizeVal)]) ]
    , .var temp
    , .ptr
    , tc'
    , tenv)

  | .allocArray tau size =>
    let (stmsSize, transSize, _, tc', tenv') := translateExpr cfg senv size tc fenv tenv
    let (temp, tc'') := Temp.bumpAndCreate tc'
    let elemSizeVal : IR.Val := .bitVec (BitVec.ofInt 32 (treeTauSize senv tau))
    ( stmsSize ++ [ .assign (.var temp) (.call .ptr (.runtime (Runtime.name .allocArray)) [(.i32, transSize), (.i32, elemSizeVal)]) ]
    , .var temp
    , .ptr
    , tc''
    , tenv')

  | .deref _ tau
  | .dot _ _ _ tau
  | .arrow _ _ _ tau
  | .arrAccess _ _ tau =>
    let (stmsAddr, addr, _, tc', tenv') := translateAddr cfg senv expr tc fenv tenv
    let (temp, tc'') := Temp.bumpAndCreate tc'
    let tau' := translateTau tau
    ( stmsAddr ++ [ .load (.var temp) tau' addr ]
    , .var temp
    , tau'
    , tc''
    , tenv')

end

def mkFenv (program : Tree.Program) : FEnv :=
  List.foldl
  (λ env fdefn =>
    let info :=
      { retTau := translateTau fdefn.tau
      , argsTau := List.map (λ (tau, _) => translateTau tau) fdefn.args
      , external := fdefn.external }
    match env.get? fdefn.fname with
    | some existing =>
      if existing.external && !fdefn.external then
        env.insert fdefn.fname info
      else
        env
    | none =>
      env.insert fdefn.fname info
  )
  {}
  program

-- MOVE CONVENTIONS:
-- If dest exists in env:
--    if it's a ptr type, update ptr type, don't do anything else
--    if it's not a ptr type, update env with the temp which stores the src
-- If dest doesn't exist in env:
--    bind register values directly and only allocate storage for immediates.

-- USAGE RULES:
-- When consuming a temp:
--    if it's a ptr, then we must create a new temp, load from ptr, and then use this new temp
--    if it's not a ptr, then ensure that we're only reading reg/value, and consume it

def isOfPtr (temp : Temp) (tenv : TEnv) : Bool :=
  match tenv.get? temp.name with
  | some tInfo => tInfo.isPtr
  | _ => false

def translateCmd
  (cfg : Config)
  (senv : SEnv)
  (cmd : Tree.Command)
  (tc : TempCounter)
  (lc : LabelCounter)
  (fenv : FEnv)
  (tenv : TEnv)
: List IR.Stm × TempCounter × LabelCounter × TEnv :=
  match cmd with
  | .declare dest tau =>
    let (ptr, tc') := Temp.bumpAndCreate tc
    let tau' := translateTau tau
    ( [ .alloca (.ptr ptr) tau' ]
    , tc'
    , lc
    , tenv.insert dest.name (TempInfo.mk ptr tau' true)
    )

  | .move dest src =>
    -- transVal will be an atom (i.e., reg, imm) at this point
    let (stms, transVal, tau, tc', tenv') := translateExpr cfg senv src tc fenv tenv
    let bindDestToPtr (tcBase : TempCounter) (tenvBase : TEnv) :=
      let (ptr, tcNext) := Temp.bumpAndCreate tcBase
      let destTempInfo := TempInfo.mk ptr tau true
      ( stms ++ [ Stm.alloca (.ptr ptr) tau ]
      , some ptr
      , tcNext
      , tenvBase.insert dest.name destTempInfo)
    let bindDestToValue (value : IR.Val) (tcBase : TempCounter) (tenvBase : TEnv) :=
      match value with
      | .var t =>
        let destTempInfo := TempInfo.mk t tau false
        ( stms
        , none
        , tcBase
        , tenvBase.insert dest.name destTempInfo)

      | .bitVec _ =>
        bindDestToPtr tcBase tenvBase

      | .null =>
        bindDestToPtr tcBase tenvBase

      | _ => panic! "[Error] after translating expr type, expect REG/IMM but found something else"
    let (stms', ptrOpt, tc'', tenv'') :=
      match tenv'.get? dest.name with
      | some destTempInfo =>
        match destTempInfo.isPtr with
        | true =>
          ( stms
          , some destTempInfo.temp
          , tc'
          , tenv')

        | false =>
          -- since dest is not a pointer type, update tenv to carry this src's value
          bindDestToValue transVal tc' tenv'

      | none =>
        -- dest is a new temp. If the source is already a register, keep it in
        -- the value environment; allocating here inside loops grows the stack
        -- for compiler-generated temporaries that never need an address.
        bindDestToValue transVal tc' tenv'

    let destIsPtr := Option.isSome ptrOpt

    ( stms' ++
      if destIsPtr then [ .store tau transVal (.ptr ptrOpt.get!) ] else []
    , tc''
    , lc
    , tenv'')

  | .store dest src =>
    let (stmsDest, destAddr, tau, tc', tenv') := translateAddr cfg senv dest tc fenv tenv
    let (stmsSrc, transVal, _, tc'', tenv'') := translateExpr cfg senv src tc' fenv tenv'
    ( stmsDest ++ stmsSrc ++ [ .store tau transVal destAddr ]
    , tc''
    , lc
    , tenv'')

  | .call fname args =>
    let (stms, transArgs, tc', tenv') :=
      List.foldr
      (λ expr (stmsAcc, argsAcc, tcAcc, tenvAcc) =>
        let (stms', expr', _, tc', tenv') := translateExpr cfg senv expr tcAcc fenv tenvAcc
        (stms' ++ stmsAcc, expr' :: argsAcc, tc', tenv')
      )
      ([], [], tc, tenv)
      args
    let fInfo := fenv.get! fname
    let callee := calleeOfName fenv fname
    match fInfo.retTau with
    | .void =>
      ( stms ++ [.callVoid callee (List.zip fInfo.argsTau transArgs)]
      , tc'
      , lc
      , tenv')
    | retTau =>
      let (temp, tc'') := Temp.bumpAndCreate tc'
      ( stms ++ [.assign (.var temp) (.call retTau callee (List.zip fInfo.argsTau transArgs))]
      , tc''
      , lc
      , tenv')

  | .runtimeCall fn args =>
    let (stms, transArgs, tc', tenv') :=
      List.foldr
      (λ expr (stmsAcc, argsAcc, tcAcc, tenvAcc) =>
        let (stms', expr', _, tc', tenv') := translateExpr cfg senv expr tcAcc fenv tenvAcc
        (stms' ++ stmsAcc, expr' :: argsAcc, tc', tenv')
      )
      ([], [], tc, tenv)
      args
    let callee := IR.Callee.runtime (Runtime.name fn)
    let argsTau := Runtime.argsTau fn
    let retTau := Runtime.retTau fn
    match retTau with
    | .void =>
      ( stms ++ [.callVoid callee (List.zip argsTau transArgs)]
      , tc'
      , lc
      , tenv')
    | _ =>
      let (temp, tc'') := Temp.bumpAndCreate tc'
      ( stms ++ [.assign (.var temp) (.call retTau callee (List.zip argsTau transArgs))]
      , tc''
      , lc
      , tenv')

  | .ite test thenBranch elseBranch =>
    let (stms, transTest, _, tc', tenv') := translateExpr cfg senv test tc fenv tenv

    ( stms ++ [ .brIte transTest thenBranch elseBranch]
    , tc'
    , lc
    , tenv'
    )

  | .goto l =>

    ( [.brJump l]
    , tc
    , lc
    , tenv
    )

  | .label l =>

    ( [.label l]
    , tc
    , lc
    , tenv
    )

  | .ret valOpt =>
    match valOpt with
    | some expr =>
      let (stms, transExpr, _, tc', tenv') := translateExpr cfg senv expr tc fenv tenv

      ( stms ++ [ .ret transExpr ]
      , tc'
      , lc
      , tenv'
      )

    | none =>

      ( [.ret .void ]
      , tc
      , lc
      , tenv
      )

def translateArg (arg : Tree.Arg) : IR.Arg :=
  let (tau, temp) := arg
  (translateTau tau, temp.name)

def translateArgs (args : List Tree.Arg) : List IR.Arg := List.map translateArg args

def translateFdefn (cfg : Config) (fdefn : Tree.FunctionDef) (fenv : FEnv) : IR.FunctionDef :=
  let structs := fdefn.structs.map (fun (name, fields) => (name, fields.map (fun (tau, _) => translateTau tau)))
  let senv : SEnv := fdefn.structs.foldl (fun env (name, fields) => env.insert name (fields.map (fun (tau, _) => tau))) {}
  if fdefn.external then
    { fname := fdefn.fname
    , tau := translateTau fdefn.tau
    , args := translateArgs fdefn.args
    , stms := []
    , structs := structs
    , external := true }
  else

    let seededTc := fdefn.args.length
    let (stms, seededTEnv', tc') := List.foldl
      (λ (stmsAcc, tenvAcc, tcAcc) (tau, temp) =>
        let tau' := translateTau tau
        let (ptr, tc') := Temp.bumpAndCreate tcAcc
        let alloca : IR.Stm := .alloca (.ptr ptr) tau'
        let store : IR.Stm := .store tau' (.var temp) (.ptr ptr)
        ( stmsAcc ++ [alloca, store]
        , tenvAcc.insert temp.name (TempInfo.mk ptr tau' true)
        , tc'))
      ([], {}, seededTc)
      fdefn.args

    let (transCmds, _, _, _) :=
      List.foldl
      (λ (stmsAcc, tcAcc, lcAcc, tenvAcc) cmd =>
        let (stms, tc', lc', tenv') := translateCmd cfg senv cmd tcAcc lcAcc fenv tenvAcc
        (stmsAcc ++ stms, tc', lc', tenv')
      )
      (stms, tc', 0, seededTEnv')
      fdefn.commands

    { fname := fdefn.fname
    , tau := translateTau fdefn.tau
    , args := translateArgs fdefn.args
    , stms := transCmds
    , structs := structs
    , external := false }

/-
Void returns may not have an explicit return, but this
is not allowed in llvm. Hence, we must make returns explicit
for void functions
-/
def fillVoidReturns (stms : List IR.Stm) : List IR.Stm :=
  let fillReturn s :=
    match s with
    | .ret _ | .brJump _ | .brIte .. => [s]
    | _ => [s, .ret .void ]

  match stms with
  | [] => [ .ret .void ]
  | s::[] => fillReturn s
  | s1::s2::ss =>
    match s2 with
    | .label _ =>
      fillReturn s1 ++
      s2 :: fillVoidReturns ss
    | _ => s1::fillVoidReturns (s2::ss)

def runWithConfig (cfg : Config) (program : Tree.Program) : IR.Program :=
  let fenvInit := mkFenv program

  List.foldl
  (λ fdefnAcc fdefn =>
    let transFdefn := translateFdefn cfg fdefn fenvInit
    let transFdefnVoids := { transFdefn with stms := fillVoidReturns transFdefn.stms }

    (fdefnAcc ++ [transFdefnVoids])
  )
  []
  program

def run (program : Tree.Program) : IR.Program :=
  runWithConfig {} program

end C0VC.LLVM.Codegen
