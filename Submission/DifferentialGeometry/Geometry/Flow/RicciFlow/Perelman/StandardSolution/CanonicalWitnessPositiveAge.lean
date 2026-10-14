import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.HighCurvatureModels
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureControl
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedBufferedCanonical
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

private theorem nonempty_positiveAge_tangentOrientation :
    Nonempty (Surgery.Topology.TangentOrientationSection (EuclideanSpace ℝ (Fin 3))) := by
  let e := (finCongr (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)).symm
  let o := DifferentialGeometry.Topology.Manifold.euclideanSmoothOrientation
    (EuclideanSpace ℝ (Fin 3))
    (Orientation.reindex ℝ (EuclideanSpace ℝ (Fin 3)) e
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation))
  obtain ⟨O, _⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_smoothOrientation
      (𝓡 3) o
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  let O₃ : DifferentialGeometry.ManifoldOrientation (𝓡 3) (EuclideanSpace ℝ (Fin 3)) 3 :=
    cast (congrArg (fun n =>
      DifferentialGeometry.ManifoldOrientation (𝓡 3) (EuclideanSpace ℝ (Fin 3)) n) hdim) O
  exact ⟨{ orientation := O₃.orientation, locally_constant := O₃.locally_constant }⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.nonempty_positiveAge_tangentOrientation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.nonempty_positiveAge_tangentOrientation target :: scope.openDecls } }

private theorem positiveAge_regular_window (S : PartialStandardSolution) {a b : ℝ}
    (h : _root_.Set.Icc a b ⊆ S.domain) :
    Ioo a b ⊆ (lifetimeInterval S.lifetime S.lifetime_pos).regular := by
  intro t ht
  have hpoint := h ⟨ht.1.le, ht.2.le⟩
  have hleft := h ⟨le_rfl, (ht.1.trans ht.2).le⟩
  exact (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos t).mpr
    ⟨((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos a).mp hleft).1.trans_lt ht.1,
      ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mp hpoint).2⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.positiveAge_regular_window
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.positiveAge_regular_window target :: scope.openDecls } }

theorem PartialStandardSolution.exists_canonicalWitness_with_cap_neck_charts_of_high_scalar
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) {τ : ℝ} (hτ : 0 < τ) :
    ∃ C Q₀ : ℝ, 1 ≤ C ∧ 0 < Q₀ ∧ ∀ (S : PartialStandardSolution)
      (x : EuclideanSpace ℝ (Fin 3)) (t : ℝ), t ∈ S.domain → τ ≤ t → t < 1 →
        Q₀ ≤ S.toSolutionOn.scalar t x →
          ∃ K : CanonicalWitness S.toSolutionOn eps C C x t, K.capTubeHasNeckChart eps := by
  obtain ⟨C, delta, hC, hd, hd1, htransfer⟩ :=
    exists_uniform_windowed_bufferedCanonical_with_cap_neck_charts.{0} heps hsmall 1
  obtain ⟨Q₀, hQ₀, hmodel⟩ := exists_standard_high_scalar_model_threshold hd hd1 hτ
  obtain ⟨o⟩ := nonempty_positiveAge_tangentOrientation
  refine ⟨C, Q₀, hC, hQ₀, ?_⟩
  intro S x t ht hτt ht1 hQ
  have hw := hmodel S o x t ht hτt ht1 hQ
  have hreg : _root_.Set.Ioo (t - (delta * S.toSolutionOn.scalar t x)⁻¹) t ⊆
      (lifetimeInterval S.lifetime S.lifetime_pos).regular := by
    obtain ⟨W, _⟩ := hw
    exact positiveAge_regular_window S W.window_mem
  obtain ⟨B, hB⟩ := htransfer _ (EuclideanSpace ℝ (Fin 3)) _ S.toSolutionOn S.isSolutionOn
    delta o x t le_rfl hreg hw
  exact ⟨B.canonicalWitness_mono B.tolerance_lt.le hsmall,
    hB.mono_eps B.tolerance_lt.le hsmall⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.exists_canonicalWitness_with_cap_neck_charts_of_high_scalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.exists_canonicalWitness_with_cap_neck_charts_of_high_scalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.exists_canonicalWitness_with_cap_neck_charts_of_high_scalar ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.exists_canonicalWitness_with_cap_neck_charts_of_high_scalar

theorem PartialStandardSolution.exists_canonicalWitness_with_cap_neck_charts_of_age
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) :
    ∃ C τmin : ℝ, 1 ≤ C ∧ 0 < τmin ∧ ∀ (S : PartialStandardSolution)
      (x : EuclideanSpace ℝ (Fin 3)) (t : ℝ), t ∈ S.domain → t < 1 →
        τmin ≤ t * S.toSolutionOn.scalar t x →
          ∃ K : CanonicalWitness S.toSolutionOn eps C C x t, K.capTubeHasNeckChart eps := by
  obtain ⟨α, hα, K, hK, hcurv⟩ := standard_uniform_initial_curvature_control
  obtain ⟨C, Q₀, hC, hQ₀, hlate⟩ :=
    exists_canonicalWitness_with_cap_neck_charts_of_high_scalar heps hsmall hα
  have hmin : 0 < _root_.Max.max Q₀ (α * (9 * K)) + 1 := by
    linarith [le_max_left Q₀ (α * (9 * K))]
  refine ⟨C, _root_.Max.max Q₀ (α * (9 * K)) + 1, hC, hmin, ?_⟩
  intro S x t ht ht1 hage
  have hmem := (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mp ht
  have ht0 : 0 ≤ t := hmem.1
  have hαt : α ≤ t := by
    by_contra hlt
    have hlt' : t < α := lt_of_not_ge hlt
    have hR : S.toSolutionOn.scalar t x ≤ 9 * K := by
      have hrm := hcurv S t ht0 hlt'.le hmem.2 t ⟨ht0, le_rfl⟩ x
      rw [metricRm04_apply] at hrm
      have habs := scalar_abs_le_rm (S.metric t) x
      have hdim : (Module.finrank ℝ (TangentSpace (𝓡 3) x) : ℝ) = 3 := by
        rw [show Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 from finrank_euclideanSpace_fin]
        norm_num
      rw [hdim] at habs
      change metricScalarAt (S.metric t) x ≤ 9 * K
      have hle : (3 : ℝ) ^ 2 *
          Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04At (S.metric t) x)) ≤ 9 * K := by
        nlinarith
      exact (le_abs_self _).trans (habs.trans hle)
    have h1 := mul_le_mul_of_nonneg_left hR ht0
    have h2 := mul_le_mul_of_nonneg_right hlt'.le (by positivity : (0 : ℝ) ≤ 9 * K)
    linarith [le_max_right Q₀ (α * (9 * K))]
  refine hlate S x t ht hαt ht1 ?_
  rcases le_or_gt 0 (S.toSolutionOn.scalar t x) with hR0 | hR0
  · have h1 := mul_le_mul_of_nonneg_right ht1.le hR0
    linarith [le_max_left Q₀ (α * (9 * K))]
  · have h1 := mul_nonpos_of_nonneg_of_nonpos ht0 hR0.le
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.exists_canonicalWitness_with_cap_neck_charts_of_age then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.exists_canonicalWitness_with_cap_neck_charts_of_age"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.exists_canonicalWitness_with_cap_neck_charts_of_age ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.exists_canonicalWitness_with_cap_neck_charts_of_age

end DifferentialGeometry.PDE.RicciFlow
