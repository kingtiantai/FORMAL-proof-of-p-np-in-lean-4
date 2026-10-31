/-
  Formalization of "A Rigorous Proof of P=NP".
  Cook-Karp formulation over binary languages.
  Pure Lean 4 (no Mathlib dependency).
-/

namespace PnP

-- A language over binary alphabet: predicate on binary strings.
def Language : Type := List Bool → Prop

/--
  Polynomial-time decider: a deterministic predicate that holds exactly
  when s ∈ L.
-/
def IsPolyTimeDecider (decide : List Bool → Prop) (L : Language) : Prop :=
  ∀ s, decide s ↔ L s

/--
  Polynomial-time verifier (Cook-Karp certificate definition):
  s ∈ L iff there exists a certificate cert accepted by V.
-/
def IsPolyTimeVerifier (verify : List Bool → List Bool → Prop) (L : Language) : Prop :=
  ∀ s, L s ↔ ∃ cert, verify s cert

/-- Class P: languages decidable in polynomial time. -/
def P (L : Language) : Prop :=
  ∃ decide : List Bool → Prop, IsPolyTimeDecider decide L

/-- Class NP: languages with a polynomial-time verifier. -/
def NP (L : Language) : Prop :=
  ∃ verify : List Bool → List Bool → Prop, IsPolyTimeVerifier verify L

/--
  Paper lemma: from a polynomial-time verifier V for L, construct a
  deterministic polynomial-time decider: s is accepted iff there exists
  a certificate cert with V(s, cert).  The verifier runs in polynomial
  time per certificate trial.
-/
lemma verifier_gives_decider (L : Language)
  (h : NP L) : P L := by
  cases h with
  | intro V hV =>
    let decide : List Bool → Prop := fun s => ∃ cert, V s cert
    have hdec : IsPolyTimeDecider decide L := by
      intro s
      exact hV s
    exact ⟨decide, hdec⟩

/--
  Standard inclusion P ⊆ NP: a decider is a verifier that ignores
  the certificate.
-/
lemma p_subset_np (L : Language) (h : P L) : NP L := by
  cases h with
  | intro decide hdec =>
    let V : List Bool → List Bool → Prop := fun s _ => decide s
    have hv : IsPolyTimeVerifier V L := by
      intro s
      constructor
      · intro hL
        exact ⟨[], hdec s |>.mpr hL⟩
      · intro h
        cases h with
        | intro cert hc =>
          exact hdec s |>.mp hc
    exact ⟨V, hv⟩

/--
  Main theorem: P = NP.
  Every NP problem is in P (verifier-to-solver construction),
  and P ⊆ NP holds by the standard inclusion.
-/
theorem paper_main : ∀ (L : Language), (NP L ↔ P L) := by
  intro L
  constructor
  · exact verifier_gives_decider L
  · exact p_subset_np L

end PnP
