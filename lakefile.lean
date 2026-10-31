import Lake
open Lake DSL

package «PnPProof» {
  name := "PnPProof"
  version := "0.1.0"
  keywords := ["complexity", "PvsNP", "formal-proof"]
  description := "Lean4 formalization for the proof of P = NP"
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.34.1"

@[default_target]
lean_lib «PnPProof» {
  srcDir := "."
}