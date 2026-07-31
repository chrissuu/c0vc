-- This module serves as the root of the `C0VC` library.
-- Import modules here that should be built as part of the library.
import C0VC.Ast.ParsedAst
import C0VC.Token
import C0VC.Parse
import C0VC.Lexer
import C0VC.Ast.ElabbedAst
import C0VC.Ast.TypedAst
import C0VC.Ast.Trans
import C0VC.Ast.Elab
import C0VC.Ast.Type
import C0VC.Ast.LowerAnnotations
import C0VC.Ast.Dce

import C0VC.LLVM
