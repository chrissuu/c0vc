import C0VC.Lexer
import C0VC.Parse
import C0VC.Ast.Elab
import C0VC.Ast.Type
import C0VC.Ast.Dce
import C0VC.StrataBoole.Trans
import C0VC.StrataBoole.Codegen

namespace C0VC.Embed

def compileC0ToBooleStringWithHeaders
    (fileName : String)
    (headers : C0VC.Ast.Program)
    (source : String)
    : Except String String := do
  let tokens ← C0VC.Lexer.munch fileName source
  let parsed ← C0VC.Parse.parseProgramFromTokens tokens
  let elabbed ← C0VC.Elab.run headers parsed
  let typed ← C0VC.Typechecker.run elabbed
  let booleIR ← C0VC.StrataBoole.Trans.run (C0VC.Dce.run typed)
  pure (C0VC.StrataBoole.Codegen.run booleIR)

def compileC0ToBooleString (source : String) : Except String String :=
  compileC0ToBooleStringWithHeaders "<embedded-c0>" [] source

end C0VC.Embed
