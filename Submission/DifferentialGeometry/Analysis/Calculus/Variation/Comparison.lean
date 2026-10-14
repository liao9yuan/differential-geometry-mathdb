import Mathlib.Topology.EMetricSpace.BoundedVariation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set
open scoped _root_.ENNReal

namespace DifferentialGeometry.Analysis

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  {f : ℝ → X} {ν : ℝ → Y} {s : Set ℝ}


theorem eVariationOn_le_of_dist_le
    (h : ∀ x ∈ s, ∀ y ∈ s, _root_.Dist.dist (f x) (f y) ≤ _root_.Dist.dist (ν x) (ν y)) :
    eVariationOn f s ≤ eVariationOn ν s := by
  apply iSup_le
  rintro ⟨n, u, hu, hs⟩
  apply (Finset.sum_le_sum (fun i _ => ?_)).trans (eVariationOn.sum_le hu hs)
  simp only [edist_dist]
  exact ENNReal.ofReal_le_ofReal (h _ (hs _) _ (hs _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.eVariationOn_le_of_dist_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.eVariationOn_le_of_dist_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.eVariationOn_le_of_dist_le ``Submission.DifferentialGeometry.Analysis.eVariationOn_le_of_dist_le



theorem eVariationOn_Icc_le_of_dist_le_sub {v : ℝ → ℝ} (hv : Monotone v)
    (h : ∀ x y, x ≤ y → _root_.Dist.dist (f x) (f y) ≤ v y - v x) (a b : ℝ) :
    eVariationOn f (_root_.Set.Icc a b) ≤ ENNReal.ofReal (v b - v a) := by
  have hb : eVariationOn f (_root_.Set.Icc a b) ≤ eVariationOn v (_root_.Set.Icc a b) := by
    apply eVariationOn_le_of_dist_le
    intro x _ y _
    rcases le_total x y with hxy | hyx
    · rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hv hxy)), neg_sub]
      exact h x y hxy
    · rw [dist_comm (f x) (f y), dist_comm (v x) (v y)]
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hv hyx)), neg_sub]
      exact h y x hyx
  exact hb.trans_eq (by simpa only [_root_.Set.univ_inter] using
    (hv.monotoneOn _root_.Set.univ).eVariationOn_eq (_root_.Set.mem_univ a) (_root_.Set.mem_univ b))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.eVariationOn_Icc_le_of_dist_le_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.eVariationOn_Icc_le_of_dist_le_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.eVariationOn_Icc_le_of_dist_le_sub ``Submission.DifferentialGeometry.Analysis.eVariationOn_Icc_le_of_dist_le_sub

end DifferentialGeometry.Analysis
