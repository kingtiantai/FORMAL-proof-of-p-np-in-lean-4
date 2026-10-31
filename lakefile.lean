import Lake
open Lake DSL

package «PnPProof» {
  name := "PnPProof"
  version := "0.1.0"
  keywords := ["complexity", "PvsNP", "formal-proof"]
  description := "Lean4 formalization for P = NP, no cache, local build"
}

require mathlib from git
  "https://mirror.sjtu.edu.cn/git/lean4-packages/mathlib4.git"@"v4.34.1"

@[default_target]
lean_lib «PnPProof» {
  srcDir := "."
}