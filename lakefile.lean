import Lake
open Lake DSL

package «PnPProof» {
  name := "PnPProof"
  version := "0.1.0"
  keywords := ["complexity", "PvsNP", "formal-proof"]
  description := "Lean4 formalization for the proof of P = NP"
}

@[default_target]
lean_lib «PnPProof» {
  srcDir := "."
}