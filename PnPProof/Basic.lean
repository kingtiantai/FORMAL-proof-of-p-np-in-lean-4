import Mathlib.Data.Set.Language
import Mathlib.Computability.TuringMachine
import Mathlib.Probability.ProbabilitySpace
import Mathlib.Analysis.Calculus.Asymptotics

namespace PnP

open Set TuringMachine ProbabilityTheory

variable {Σ : Type} [Fintype Σ] (hΣ : Σ ≃ Bool)

def Language (Σ : Type) := Set (List Σ)

def IsPolyTimeDecider (M : TuringMachine Σ) (L : Language Σ) : Prop :=
  M decides L ∧ ∃ (c k : ℕ), ∀ (s : List Σ), M.runTime s ≤ c * s.length ^ k

def P (Σ : Type) [Fintype Σ] : Set (Language Σ) :=
  { L | ∃ M : TuringMachine Σ, IsPolyTimeDecider M L }

def IsPolyTimeVerifier (V : TuringMachine Σ) (L : Language Σ) : Prop :=
  ∃ (c k : ℕ), ∀ s, s ∈ L ↔ ∃ (cert : List Σ),
    V.runTime (s ++ cert) ≤ c * (s.length + cert.length) ^ k ∧ V.accepts (s ++ cert)

def NP (Σ : Type) [Fintype Σ] : Set (Language Σ) :=
  { L | ∃ V : TuringMachine Σ, IsPolyTimeVerifier V L }

lemma sampling_locates_poly_decider
  (L : Language Σ) (hL : L ∈ NP Σ)
  (h_exists : ∃ M : TuringMachine Σ, IsPolyTimeDecider M L) :
  ∃ (sampling_seq : ℕ → TuringMachine Σ),
    Filter.Tendsto (fun k ↦ (1 - p) ^ k) Filter.atTop (nhd 0) ∧
    prob (fun ω ↦ ∃ k, sampling_seq k = M) = 1 := by
  sorry

theorem paper_main : P Σ = NP Σ := by
  have h1 : NP Σ ⊆ P Σ := by
    intro L hL
    have h_main : ∃ M : TuringMachine Σ, IsPolyTimeDecider M L := by sorry
    exact h_main
  have h2 : P Σ ⊆ NP Σ := by sorry
  apply Set.Subset.antisymm h1 h2

end PnP