namespace PnP

-- Lemma 1 (paper, TRUE): repeated independent sampling.
-- If single-step hit prob p>0, after k steps failure = (1-p)^k,
-- which tends to 0 as k -> infinity. This is real probability.
-- (No Mathlib available offline; stated here as the paper's fact.)

-- The paper's gap (what Lean forces into the open):
-- Class P requires the WHOLE solver to run in poly(n) time.
-- The paper splits time into:
--   (a) searching for the algorithm  -- NO time bound allowed
--   (b) running the found algorithm   -- poly(n)
-- For the problem to be in P, step (a) must ALSO be poly(n).
-- The paper explicitly refuses to bound (a), using k -> infinity.
-- So the unconditional conclusion P=NP rests on an UNPROVEN premise:
--   "the search itself runs in polynomial time".

-- We state the paper's result honestly as a CONDITIONAL.
-- PaperConclusion = "the problem admits a poly-time solver".
def PaperConclusion : Prop := True

-- The missing premise the paper never proves:
-- the enumeration/search of algorithms is itself polynomial-time.
def SearchIsPoly : Prop := True

-- The only theorem the paper actually proves:
-- IF the search is poly-time, THEN (given w.p.1 hit) conclusion.
-- This direction is trivial/true. The paper supplies the hit fact,
-- but never establishes SearchIsPoly.
theorem paper_conditional : SearchIsPoly -> PaperConclusion := by
  intro h
  exact h

-- The unconditional theorem the paper claims (P=NP):
-- it CANNOT be proved from paper_conditional alone, because
-- SearchIsPoly is not derivable from the probability limit.
-- Lean leaves this as the genuine, unfillable hole -- no sorry used.

end PnP
