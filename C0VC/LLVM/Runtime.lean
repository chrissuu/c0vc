import C0VC.LLVM.IR

namespace C0VC.LLVM.Runtime

inductive Fn where
  | checkedDiv
  | checkedMod
  | checkedShl
  | checkedShr
  | assert
  | alloc
  | allocArray
  | checkPtr
  | checkArrayAccess
  | arrayLength
deriving Inhabited, BEq

def name : Fn → String
  | .checkedDiv => "__c0vc_checked_div"
  | .checkedMod => "__c0vc_checked_mod"
  | .checkedShl => "__c0vc_checked_shl"
  | .checkedShr => "__c0vc_checked_shr"
  | .assert => "_c0_assert"
  | .alloc => "__c0vc_alloc"
  | .allocArray => "__c0vc_alloc_array"
  | .checkPtr => "__c0vc_check_ptr"
  | .checkArrayAccess => "__c0vc_check_array_access"
  | .arrayLength => "__c0vc_array_length"

def retTau : Fn → IR.Tau
  | .checkedDiv
  | .checkedMod
  | .checkedShl
  | .checkedShr => .i32
  | .assert => .void
  | .alloc
  | .allocArray => .ptr
  | .checkPtr
  | .checkArrayAccess => .ptr
  | .arrayLength => .i32

def argsTau : Fn → List IR.Tau
  | .checkedDiv
  | .checkedMod
  | .checkedShl
  | .checkedShr => [.i32, .i32]
  | .assert => [.i1]
  | .alloc => [.i32]
  | .allocArray => [.i32, .i32]
  | .checkPtr => [.ptr]
  | .checkArrayAccess => [.ptr, .i32]
  | .arrayLength => [.ptr]

def all : List Fn :=
  [ .checkedDiv
  , .checkedMod
  , .checkedShl
  , .checkedShr
  , .assert
  , .alloc
  , .allocArray
  , .checkPtr
  , .checkArrayAccess
  , .arrayLength
  ]

end C0VC.LLVM.Runtime
