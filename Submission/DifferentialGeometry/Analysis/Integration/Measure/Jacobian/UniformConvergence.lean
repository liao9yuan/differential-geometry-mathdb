import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Filter
open scoped _root_.Matrix.Norms.Elementwise

open _root_.TendstoUniformly in
theorem TendstoUniformly.sqrt_det
    {n Q ι : Type*} [Fintype n] [DecidableEq n]
    {l : Filter ι} {A : ι → Q → Matrix n n ℝ} {B : Q → Matrix n n ℝ}
    (h : TendstoUniformly A B l) (hB : Bornology.IsBounded (_root_.Set.range B)) :
    TendstoUniformly (fun k q => Real.sqrt (A k q).det)
      (fun q => Real.sqrt (B q).det) l := by
  obtain ⟨C, hC⟩ := hB.exists_norm_le
  let S : Set (Matrix n n ℝ) := Metric.closedBall 0 (C + 1)
  have hlim : ∀ q, B q ∈ S := by
    intro q
    change _root_.Dist.dist (B q) 0 ≤ C + 1
    rw [dist_zero_right]
    exact (hC (B q) (_root_.Set.mem_range_self q)).trans (le_add_of_nonneg_right zero_le_one)
  have hseq : ∀ᶠ k in l, ∀ q, A k q ∈ S := by
    filter_upwards [(Metric.tendstoUniformly_iff.mp h) 1 zero_lt_one] with k hk
    intro q
    change _root_.Dist.dist (A k q) 0 ≤ C + 1
    calc
      dist (A k q) 0 ≤ _root_.Dist.dist (A k q) (B q) + _root_.Dist.dist (B q) 0 := dist_triangle _ _ _
      _ ≤ 1 + C := add_le_add (by simpa only [dist_comm] using (hk q).le)
        (by simpa only [dist_zero_right] using hC (B q) (_root_.Set.mem_range_self q))
      _ = C + 1 := add_comm _ _
  have hc : Continuous (fun M : Matrix n n ℝ => Real.sqrt M.det) :=
    Real.continuous_sqrt.comp continuous_id.matrix_det
  have huc : UniformContinuousOn (fun M : Matrix n n ℝ => Real.sqrt M.det) S :=
    (_root_.ProperSpace.isCompact_closedBall (0 : Matrix n n ℝ) (C + 1)).uniformContinuousOn_of_continuous
      hc.continuousOn
  exact huc.comp_tendstoUniformly_eventually (g := fun M : Matrix n n ℝ => Real.sqrt M.det)
    hseq hlim h

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.TendstoUniformly
  let env ← Lean.getEnv
  if env.contains `TendstoUniformly.sqrt_det then
    throwError "Refusing to shadow existing declaration TendstoUniformly.sqrt_det"
  Lean.modifyEnv fun env => Lean.addAlias env `TendstoUniformly.sqrt_det ``Submission.TendstoUniformly.sqrt_det
