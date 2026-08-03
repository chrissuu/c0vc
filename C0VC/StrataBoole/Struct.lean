import C0VC.Ast.TypedAst
import Std.Data.HashMap

namespace C0VC.StrataBoole.Struct

/--
StrataBoole.Struct

Recall that StrataBoole does not have a direct struct
type / datatype. This module stores the translation unit
between TypedAst's struct type (which is of List Fields)
into the array-based flattened struct representation.

Author(s):
  ~ Chris Su <chrjs@cmu.edu>
-/

structure FieldPath where
  root : String
  fields : List String
deriving BEq, Hashable, Repr

abbrev SEnv := Std.HashMap String (List TypedAst.Field)

structure FieldInfo where
  index : Nat
  tau : TypedAst.Tau

abbrev FieldIndexMap := Std.HashMap FieldPath FieldInfo
abbrev StructWidthMap := Std.HashMap String Nat

structure Layout where
  fields : FieldIndexMap
  widths : StructWidthMap

private def collectSEnv (structs : List TypedAst.Struct) : SEnv :=
  structs.foldl
    (fun env (name, fields) => env.insert name fields)
    {}

private def fieldPathText (root : String) (fields : List String) : String :=
  String.intercalate "." (root :: fields)

partial def computeFields
  (senv : SEnv)
  (root : String)
  (path : List String)
  (fields : List TypedAst.Field)
  (map : FieldIndexMap)
  (start : Nat)
  : Except String (FieldIndexMap × Nat) := do
  match fields with
  | [] => .ok (map, start)
  | (tau, fieldName) :: rest =>
      match tau with
      | .int | .char | .bool | .ptr _ | .array _ =>
          let map' := map.insert { root, fields := path ++ [fieldName] } { index := start, tau }
          computeFields senv root path rest map' (start + 1)
      | .struct name =>
          let nestedFields ← match senv.get? name with
            | some fields => .ok fields
            | none => .error s!"struct {name} used before declaration"
          let (map', start') ← computeFields senv root (path ++ [fieldName]) nestedFields map start
          computeFields senv root path rest map' start'
      | .string =>
          .error s!"StrataBoole backend does not support string field {fieldPathText root (path ++ [fieldName])}"
      | .null =>
          .error s!"invalid null-typed field {fieldPathText root (path ++ [fieldName])}"
      | .void =>
          .error s!"invalid void-typed field {fieldPathText root (path ++ [fieldName])}"

def computeLayout (structs : List TypedAst.Struct) : Except String Layout := do
  let senv := collectSEnv structs
  let (fields, widths) ← structs.foldlM
    (fun (fieldAcc, widthAcc) (name, structFields) => do
      let (fieldAcc', width) ← computeFields senv name [] structFields fieldAcc 0
      .ok (fieldAcc', widthAcc.insert name width))
    ({}, {})
  .ok { fields, widths }

def computeFieldLayout (structs : List TypedAst.Struct) : Except String FieldIndexMap := do
  .ok (← computeLayout structs).fields

def lookupFieldInfo (layout : FieldIndexMap) (root : String) (fields : List String) : Except String FieldInfo :=
  match layout.get? { root, fields } with
  | some info => .ok info
  | none => .error s!"struct field {fieldPathText root fields} has no Boole heap slot"

def lookupFieldIndex (layout : FieldIndexMap) (root : String) (fields : List String) : Except String Nat := do
  .ok (← lookupFieldInfo layout root fields).index

def lookupStructWidth (widths : StructWidthMap) (name : String) : Except String Nat :=
  match widths.get? name with
  | some width => .ok width
  | none => .error s!"struct {name} has no Boole layout width"

end C0VC.StrataBoole.Struct
