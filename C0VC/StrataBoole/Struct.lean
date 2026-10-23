import C0VC.Ast.TypedAst
import Std.Data.HashMap

namespace C0VC.StrataBoole.Struct

/--
StrataBoole.Struct

Boole has no struct values, so a C0 struct is laid out as a run of flattened
slots inside the object that stores it. Every scalar leaf field gets one slot;
nested value structs are flattened recursively. Fields of different types share
the slot numbering but live in different typed heaps.

Author(s):
  ~ Chris Su <chrjs@cmu.edu>
-/

abbrev SEnv := Std.HashMap String (List TypedAst.Field)

structure FieldInfo where
  /-- Slot offset of the field relative to the start of its struct. -/
  offset : Nat
  tau : TypedAst.Tau

structure Layout where
  /-- Keyed by (struct name, field name). -/
  fields : Std.HashMap (String × String) FieldInfo := {}
  /-- Number of flattened slots in each struct. -/
  widths : Std.HashMap String Nat := {}
  /--
  Scalar leaf fields of each struct in slot order, as (path, type). A nested
  field `in.a` has path `["in", "a"]`; its slot is its position in the list.
  -/
  leaves : Std.HashMap String (List (List String × TypedAst.Tau)) := {}

instance : Inhabited Layout := ⟨{}⟩

private partial def layoutStruct (senv : SEnv) (layout : Layout) (name : String) : Except String Layout := do
  if layout.widths.contains name then
    return layout
  let fields ← match senv.get? name with
    | some fields => pure fields
    | none => throw s!"struct {name} used before declaration"
  let (layout, width, leaves) ← fields.foldlM
    (fun (layout, offset, leaves) (tau, fieldName) => do
      let layout := layout
      match tau with
      | .struct inner =>
          let layout ← layoutStruct senv layout inner
          let innerWidth := layout.widths.getD inner 0
          let layout := { layout with fields := layout.fields.insert (name, fieldName) { offset, tau } }
          let innerLeaves := (layout.leaves.getD inner []).map fun (path, t) => (fieldName :: path, t)
          pure (layout, offset + innerWidth, leaves ++ innerLeaves)
      | .void => throw s!"invalid void-typed field {name}.{fieldName}"
      | .null => throw s!"invalid null-typed field {name}.{fieldName}"
      | _ =>
          let layout := { layout with fields := layout.fields.insert (name, fieldName) { offset, tau } }
          pure (layout, offset + 1, leaves ++ [([fieldName], tau)]))
    (layout, 0, [])
  pure { layout with
    widths := layout.widths.insert name width
    leaves := layout.leaves.insert name leaves }

def computeLayout (structs : List TypedAst.Struct) : Except String Layout := do
  let senv : SEnv := structs.foldl (fun env (name, fields) => env.insert name fields) {}
  structs.foldlM (fun layout (name, _) => layoutStruct senv layout name) {}

def lookupField (layout : Layout) (structName fieldName : String) : Except String FieldInfo :=
  match layout.fields.get? (structName, fieldName) with
  | some info => .ok info
  | none => .error s!"struct {structName} has no field {fieldName}"

def lookupWidth (layout : Layout) (structName : String) : Except String Nat :=
  match layout.widths.get? structName with
  | some width => .ok width
  | none => .error s!"struct {structName} has no layout"

end C0VC.StrataBoole.Struct
