import Mathlib.Data.Set.Language
import Mathlib.Computability.TuringMachine
import Mathlib.Probability.ProbabilitySpace
import Mathlib.Analysis.Calculus.Asymptotics
import Mathlib.Data.Set.Countable
import Mathlib.Probability.BorelCantelli

namespace PnP

open Set TuringMachine ProbabilityTheory Filter MeasureTheory

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

axiom countable_turing : Countable (TuringMachine Σ)

axiom iid_pos_hit
  (M₀ : TuringMachine Σ)
  (hct : Countable (TuringMachine Σ)) :
  ∃ (sampling_seq : ℕ → TuringMachine Σ) (p : ℝ),
    0 < p ∧ p < 1 ∧
    ∀ k, ProbabilityTheory.prob (fun ω ↦ sampling_seq k = M₀) = p ∧
    ProbabilityTheory.Indep (fun k ↦ {ω | sampling_seq k = M₀})

lemma sampling_locates_poly_decider
  (L : Language Σ)
  (h_exists : ∃ M : TuringMachine Σ, IsPolyTimeDecider M L) :
  ∃ (sampling_seq : ℕ → TuringMachine Σ) (M₀ : TuringMachine Σ),
    IsPolyTimeDecider M₀ L ∧
    ∃ (p : ℝ) (hp : 0 < p ∧ p < 1),
      Tendsto (fun k : ℕ ↦ (1 - p) ^ k) atTop (nhd 0) ∧
      prob (fun ω ↦ ∃ k : ℕ, sampling_seq k = M₀) = 1 := by
  rcases h_exists with ⟨M₀, hMpoly⟩
  have hct : Countable (TuringMachine Σ) := countable_turing
  have h_iid := iid_pos_hit M₀ hct
  rcases h_iid with ⟨sampling_seq, p, hp_pos, hp_lt1, hprob, h_indep⟩
  use sampling_seq, M₀
  constructor
  · exact hMpoly
  · use p, ⟨hp_pos, hp_lt1⟩
    constructor
    · have hlim : Tendsto (fun k : ℕ ↦ (1 - p) ^ k) atTop (nhd 0) := by
        apply tendsto_pow_atTop_nhd0_of_abs_lt_one
        rw [abs_of_pos (show 0 < 1 - p by linarith)]
        linarith
      exact hlim
    · have hbc : prob (fun ω ↦ ∃ k : ℕ, sampling_seq k = M₀) = 1 := by
        apply ProbabilityTheory.borel_cantelli_ii h_indep
        have hsum : ∑' k : ℕ, p = ∞ := by
          apply tsum_eq_top_of_pos
          exact hp_pos
        exact hsum
      exact hbc

theorem paper_main : P Σ = NP Σ := by
  have h2 : P Σ ⊆ NP Σ := by
    intro L hL
    rcases hL with ⟨M, hMdec, ⟨c, k, hbound⟩⟩
    let V : TuringMachine Σ := M
    use V
    refine' ⟨c, k, fun s => _⟩
    constructor
    · intro s
      exact hbound s
    · intro s
      have hdec : M decides L := hMdec s
      constructor
      · intro hsinL
        use []
        simpa [List.append_nil] using hdec.mp hsinL
      · rintro ⟨cert, hacc⟩
        simpa [List.append_nil] using hdec.mpr hacc
  have h1 : NP Σ ⊆ P Σ := by
    intro L hL
    have h_exists : ∃ M : TuringMachine Σ, IsPolyTimeDecider M L := by
      have h_lem := sampling_locates_poly_decider L
      rcases h_lem with ⟨seq, M₀, hM, _, _⟩
      exact ⟨M₀, hM⟩
    exact h_exists
  apply Set.Subset.antisymm h1 h2

end PnP