import C0VC.Embed.Lean
import StrataBoole

def c0Main : StrataDDM.SourcedProgram :=
#c0
int main() {
  return 0;
}
#end

#guard c0Main.source.contains "int main"

#guard
  match Strata.Boole.getProgram c0Main with
  | .ok _ => true
  | .error _ => false
