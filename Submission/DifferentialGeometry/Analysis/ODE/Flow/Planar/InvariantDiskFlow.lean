import Submission.DifferentialGeometry.Analysis.Calculus.Inverse.UniformCurveInjectivity
import Submission.DifferentialGeometry.Topology.FixedPoint.PlanarDisk
import Mathlib.Dynamics.Flow

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric

namespace DifferentialGeometry.Analysis

theorem exists_zero_of_forward_invariant_disk
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E} (e : _root_.Metric.closedBall (0 : ℂ) 1 ≃ₜ K) (φ : _root_.Flow ℝ E)
    {v : E → E} (hv : ContinuousOn v K) (hK : IsForwardInvariant φ K)
    (hderiv : ∀ x ∈ K, ∀ t ∈ _root_.Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun s ↦ φ s x) (v (φ t x)) (_root_.Set.Ici 0) t) :
    ∃ x ∈ K, v x = 0 := by
  by_contra h
  push Not at h
  let : CompactSpace K := e.compactSpace
  have hd : ContinuousOn (fun q : K × ℝ ↦ v (φ q.2 q.1)) (_root_.Set.univ ×ˢ _root_.Set.Icc 0 1) :=
    hv.comp (φ.continuous continuous_snd
      (continuous_subtype_val.comp continuous_fst)).continuousOn
      (fun q hq ↦ hK hq.2.1 q.1.property)
  obtain ⟨ε, hε, _, hinj⟩ := exists_uniform_injOn_of_continuous_deriv_on_Icc
    (K := (_root_.Set.univ : Set K)) isCompact_univ
    (γ := fun x t ↦ φ t x) (dγ := fun x t ↦ v (φ t x)) zero_lt_one hd
    (fun x _ t ht ↦ (hderiv x x.property t ht.1).mono _root_.Set.Icc_subset_Ici_self)
    (fun x _ ↦ by simpa only [φ.map_zero_apply] using h x x.property)
  let t := ε / 2
  have ht : 0 ≤ t := (half_pos hε).le
  let f : C(K, K) :=
    ⟨fun x ↦ ⟨φ t x, hK ht x.property⟩,
      (φ.continuous continuous_const continuous_subtype_val).subtype_mk _⟩
  let a : C(_root_.Metric.closedBall (0 : ℂ) 1, K) := ⟨e, e.continuous⟩
  let b : C(K, _root_.Metric.closedBall (0 : ℂ) 1) := ⟨e.symm, e.symm.continuous⟩
  obtain ⟨z, hz⟩ := DifferentialGeometry.Topology.FixedPoint.exists_fixedPoint_closed_unitDisk
    (b.comp (f.comp a))
  have hfix : f (e z) = e z := by
    have he := congrArg e hz
    simpa only [a, b, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      e.apply_symm_apply] using he
  have heq : φ t (e z) = φ 0 (e z) := by
    rw [φ.map_zero_apply]
    exact congrArg Subtype.val hfix
  have htzero : t = 0 := hinj (e z) (_root_.Set.mem_univ _)
    (by constructor <;> dsimp [t] <;> linarith)
    (by constructor <;> linarith) heq
  exact (half_pos hε).ne' htzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_zero_of_forward_invariant_disk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_zero_of_forward_invariant_disk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_zero_of_forward_invariant_disk ``Submission.DifferentialGeometry.Analysis.exists_zero_of_forward_invariant_disk

end DifferentialGeometry.Analysis
