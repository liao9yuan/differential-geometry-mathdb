import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.IntermediateValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter _root_.Topology
open scoped _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem det_fderiv_ne_zero_of_partialDiffeomorph
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) {x : E} (hx : x ∈ e.source) :
    (fderiv ℝ e x).toLinearMap.det ≠ 0 := by
  let A := fderiv ℝ e x
  let B := fderiv ℝ e.symm (e x)
  have hA : HasFDerivAt e A x :=
    ((e.contMDiffOn.contDiffOn.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt
      (by simp)).hasFDerivAt
  have hB : HasFDerivAt e.symm B (e x) :=
    ((e.symm.contMDiffOn.contDiffOn.contDiffAt
      (e.open_target.mem_nhds (e.map_source hx))).differentiableAt (by simp)).hasFDerivAt
  have heq : (e.symm ∘ e) =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact e.left_inv hy
  have hBA : B.comp A = ContinuousLinearMap.id ℝ E :=
    ((hB.comp x hA).congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_id x)
  have hprod : B.toLinearMap.det * A.toLinearMap.det = 1 := by
    rw [← LinearMap.det_comp]
    change (B.comp A).toLinearMap.det = 1
    rw [hBA]
    simp
  intro h
  change A.toLinearMap.det = 0 at h
  rw [h, _root_.MulZeroClass.mul_zero] at hprod
  exact zero_ne_one hprod

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.det_fderiv_ne_zero_of_partialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.det_fderiv_ne_zero_of_partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.det_fderiv_ne_zero_of_partialDiffeomorph ``Submission.DifferentialGeometry.Analysis.det_fderiv_ne_zero_of_partialDiffeomorph

theorem det_fderiv_pos_iff_of_preconnected
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    (hconn : IsPreconnected e.source) {x y : E} (hx : x ∈ e.source) (hy : y ∈ e.source) :
    0 < (fderiv ℝ e x).toLinearMap.det ↔ 0 < (fderiv ℝ e y).toLinearMap.det := by
  have hc : ContinuousOn (fun z ↦ (fderiv ℝ e z).toLinearMap.det) e.source :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (e.contMDiffOn.contDiffOn.continuousOn_fderiv_of_isOpen e.open_source (by simp))
  have hprop (a b : E) (ha : a ∈ e.source) (hb : b ∈ e.source)
      (hpos : 0 < (fderiv ℝ e a).toLinearMap.det) :
      0 < (fderiv ℝ e b).toLinearMap.det := by
    by_contra hn
    obtain ⟨z, hz, hzero⟩ := hconn.intermediate_value hb ha hc
      (show (0 : ℝ) ∈ _root_.Set.Icc (fderiv ℝ e b).toLinearMap.det (fderiv ℝ e a).toLinearMap.det from
        ⟨le_of_not_gt hn, hpos.le⟩)
    exact det_fderiv_ne_zero_of_partialDiffeomorph e hz hzero
  exact ⟨hprop x y hx hy, hprop y x hy hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.det_fderiv_pos_iff_of_preconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.det_fderiv_pos_iff_of_preconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.det_fderiv_pos_iff_of_preconnected ``Submission.DifferentialGeometry.Analysis.det_fderiv_pos_iff_of_preconnected

end DifferentialGeometry.Analysis

namespace Diffeomorph
open _root_.Diffeomorph

open _root_.Diffeomorph in
theorem det_fderiv_pos_of_eqOn_compl_isCompact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E ≃ₘ[ℝ] E) {K : Set E} (hK : IsCompact K)
    (hfix : _root_.Set.EqOn F id Kᶜ) (x : E) :
    0 < (fderiv ℝ F x).toLinearMap.det := by
  cases subsingleton_or_nontrivial E with
  | inl h =>
    let _ := h
    rw [LinearMap.det_eq_one_of_subsingleton]
    exact zero_lt_one
  | inr h =>
    let _ := h
    obtain ⟨y, hy⟩ := Set.nonempty_compl.mpr hK.ne_univ
    have hnear : (F : E → E) =ᶠ[𝓝 y] id :=
      Filter.Eventually.mono (hK.isClosed.isOpen_compl.mem_nhds hy) hfix
    have hypos : 0 < (fderiv ℝ F y).toLinearMap.det := by
      rw [hnear.fderiv_eq, fderiv_id]
      simp
    exact (DifferentialGeometry.Analysis.det_fderiv_pos_iff_of_preconnected F.toPartialDiffeomorph
      _root_.PreconnectedSpace.isPreconnected_univ (_root_.Set.mem_univ y) (_root_.Set.mem_univ x)).mp hypos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.det_fderiv_pos_of_eqOn_compl_isCompact then
    throwError "Refusing to shadow existing declaration Diffeomorph.det_fderiv_pos_of_eqOn_compl_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.det_fderiv_pos_of_eqOn_compl_isCompact ``Submission.Diffeomorph.det_fderiv_pos_of_eqOn_compl_isCompact

end Diffeomorph
