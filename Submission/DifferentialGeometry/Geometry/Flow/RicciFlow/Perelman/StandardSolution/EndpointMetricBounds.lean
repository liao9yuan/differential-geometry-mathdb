import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.EndpointMetricRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Tower
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Solution.TimeRegularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.PDE.RicciFlow

private theorem affine_bound_closed (u : ℝ → ℝ) (T α β : ℝ) (hT : 0 ≤ T)
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hc : ContinuousOn u (_root_.Set.Icc 0 T)) (h0 : 0 ≤ u 0)
    (hd : ∀ s ∈ _root_.Set.Ioo 0 T, ∃ d, HasDerivAt u d s ∧ d ≤ α * u s + β)
    (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 T) :
    u t ≤ Real.exp (α * T) * (u 0 + β / α) := by
  let F := fun s => Real.exp (-α * s) * (u s + β / α)
  have hFc : ContinuousOn F (_root_.Set.Icc 0 T) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      (hc.add continuousOn_const)
  have hFd (s : ℝ) (hs : s ∈ _root_.Set.Ioo 0 T) : ∃ d, HasDerivAt F d s ∧ d ≤ 0 := by
    obtain ⟨d, hd, hb⟩ := hd s hs
    refine ⟨Real.exp (-α * s) * (-α) * (u s + β / α) + Real.exp (-α * s) * d, ?_, ?_⟩
    · have hh := (((hasDerivAt_id s).const_mul (-α)).exp.mul (hd.add_const (β / α)))
      convert hh using 1 <;> first | rfl | simp only [mul_one, id_eq]
    · have heq : Real.exp (-α * s) * (-α) * (u s + β / α) + Real.exp (-α * s) * d =
          Real.exp (-α * s) * (d - α * u s - β) := by
        field_simp
        ring
      rw [heq]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)
  have hanti : AntitoneOn F (_root_.Set.Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hFc
    · intro s hs
      obtain ⟨d, hd, _⟩ := hFd s (by simpa only [interior_Icc] using hs)
      exact hd.differentiableAt.differentiableWithinAt
    · intro s hs
      obtain ⟨d, hd, hb⟩ := hFd s (by simpa only [interior_Icc] using hs)
      simpa only [hd.deriv] using hb
  have hh := hanti ⟨le_rfl, hT⟩ ht ht.1
  have hmul := mul_le_mul_of_nonneg_left hh (Real.exp_pos (α * t)).le
  have he : Real.exp (α * t) * F t = u t + β / α := by
    dsimp only [F]
    rw [← mul_assoc, ← Real.exp_add]
    simp only [neg_mul, add_neg_cancel, Real.exp_zero, one_mul]
  rw [he] at hmul
  have hF0 : F 0 = u 0 + β / α := by simp only [F, _root_.MulZeroClass.mul_zero, Real.exp_zero, one_mul]
  rw [hF0] at hmul
  have hb0 : 0 ≤ β / α := div_nonneg hβ hα.le
  exact (by linarith : u t ≤ Real.exp (α * t) * (u 0 + β / α)).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hα.le))
      (add_nonneg h0 hb0))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.affine_bound_closed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.affine_bound_closed target :: scope.openDecls } }

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem metricCovOrderBound_stage_closed {D : RealTimeInterval} [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hT : 0 ≤ T) (hreg : _root_.Set.Ioo 0 T ⊆ D.regular)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
        (_root_.Set.Icc 0 T ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet))
    (gRef : SmoothRiemannianMetric I M) (U : Set M) (hU : IsOpen U)
    (N : ℕ) (hN : 1 ≤ N) (Bmax : ℝ) (hBmax : 1 ≤ Bmax)
    (hequiv : ∀ t ∈ _root_.Set.Icc 0 T, MetricUniformEquivalentOn U gRef (S.base.metric t) Bmax)
    (Cg : ℕ → ℝ)
    (hprev : ∀ r : ℕ, 1 ≤ r → r < N → ∀ t ∈ _root_.Set.Icc 0 T, ∀ x ∈ U,
      metricCovDerivNorm r (S.base.metric t) gRef x ≤ Cg r)
    (KShi : ℝ) (hKShi : 0 ≤ KShi)
    (hShi : MovingShiBoundOn U 0 T (fun _ t => S.base.metric t) N KShi)
    (A : ℝ) (hA : 0 ≤ A)
    (hinit : ∀ x ∈ U, metricCovDerivNorm N (S.base.metric 0) gRef x ≤ A) :
    ∀ t ∈ _root_.Set.Icc 0 T, ∀ x ∈ U,
      metricCovDerivNorm N (S.base.metric t) gRef x ≤
        metricCovOrderEvolutionConstant
          (ricTowerCoeffs (Module.finrank ℝ E) N Bmax Cg KShi).slope
          (ricTowerCoeffs (Module.finrank ℝ E) N Bmax Cg KShi).offset T A := by
  let C := (ricTowerCoeffs (Module.finrank ℝ E) N Bmax Cg KShi).slope
  let B := (ricTowerCoeffs (Module.finrank ℝ E) N Bmax Cg KShi).offset
  have hCB := ricCoeffs_nonneg (Module.finrank ℝ E) N Bmax Cg KShi hBmax hKShi
  have hric := ric_bound_field_on (I := I) hU N hN Bmax hBmax (fun _ => hequiv)
    Cg (fun r h1 hr _ => hprev r h1 hr) KShi hKShi hShi
  intro t ht x hx
  let u := fun s => metricCovDerivNorm N (S.base.metric s) gRef x ^ 2
  have hu : ContinuousOn u (_root_.Set.Icc 0 T) := by
    have hh := metricCovDerivNorm_joint_continuousOn S.base.metric (_root_.Set.Icc 0 T) hgram gRef N
    exact (hh.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hs => ⟨hs, _root_.Set.mem_univ x⟩)).pow 2
  have hα : 0 < metricCovOrderEvolutionAlpha C := by
    unfold metricCovOrderEvolutionAlpha
    nlinarith [sq_nonneg C]
  have hβ : 0 ≤ metricCovOrderEvolutionBeta B := by
    unfold metricCovOrderEvolutionBeta
    positivity
  have hd : ∀ s ∈ _root_.Set.Ioo 0 T, ∃ d, HasDerivAt u d s ∧
      d ≤ metricCovOrderEvolutionAlpha C * u s + metricCovOrderEvolutionBeta B := by
    intro s hs
    have hwin : ∀ _i : ℕ, _root_.Set.Icc s s ⊆ D.regular := by
      intro _ r hr
      have hr' : r = s := le_antisymm hr.2 hr.1
      exact hr' ▸ hreg hs
    have hev := hevComp_of_solutions (I := I) (N := N) (gRef := gRef)
      (fun _ => D) (fun _ => S) (fun _ => hS) (fun _ _ => rfl) hwin
      (fun _ => solutionTowerSwap_regularity gRef S hS N (fun {r} hr => D.regular_isOpen.mem_nhds hr))
    have hnorm := normsq_evolution_of_comp (I := I) (K := U)
      (fun i y _ r hr v => hev i y r hr v)
    obtain ⟨d, hd, hb⟩ := hnorm 0 x hx s ⟨le_rfl, le_rfl⟩
    refine ⟨d, hd, ?_⟩
    have hq := hric 0 s (_root_.Set.Ioo_subset_Icc_self hs) x hx
    let q := Real.sqrt (normSq0S gRef x (N + 2)
      (nablaRicReal (fun _ t => S.base.metric t) gRef N 0 s x))
    let y := metricCovDerivNorm N (S.base.metric s) gRef x
    have hq0 : 0 ≤ q := Real.sqrt_nonneg _
    have hy0 : 0 ≤ y := Real.sqrt_nonneg _
    have hqle : q ≤ C * y + B := hq
    have hqsq : q ^ 2 ≤ (C * y + B) ^ 2 :=
      (sq_le_sq₀ hq0 (add_nonneg (mul_nonneg hCB.1 hy0) hCB.2)).mpr hqle
    have hYoung : (C * y + B) ^ 2 ≤ 2 * (C * y) ^ 2 + 2 * B ^ 2 := by
      nlinarith [sq_nonneg (C * y - B)]
    have hbd : d ≤ y ^ 2 + (2 * q) ^ 2 := (le_abs_self d).trans hb
    change d ≤ (1 + 8 * C ^ 2) * y ^ 2 + (8 * B ^ 2 + 1)
    nlinarith [hqsq, hYoung]
  have hh := affine_bound_closed u T (metricCovOrderEvolutionAlpha C)
    (metricCovOrderEvolutionBeta B) hT hα hβ hu (sq_nonneg _) hd t ht
  have hinitSq : u 0 ≤ A ^ 2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) hA).mpr (hinit x hx)
  have hsq := hh.trans (mul_le_mul_of_nonneg_left
    (show u 0 + metricCovOrderEvolutionBeta B / metricCovOrderEvolutionAlpha C ≤
      A ^ 2 + metricCovOrderEvolutionBeta B / metricCovOrderEvolutionAlpha C by linarith)
      (Real.exp_pos _).le)
  change metricCovDerivNorm N (S.base.metric t) gRef x ≤
    Real.sqrt (Real.exp (metricCovOrderEvolutionAlpha C * T) *
      (A ^ 2 + metricCovOrderEvolutionBeta B / metricCovOrderEvolutionAlpha C))
  exact (Real.le_sqrt (Real.sqrt_nonneg _) (by positivity)).mpr hsq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricCovOrderBound_stage_closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricCovOrderBound_stage_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricCovOrderBound_stage_closed ``Submission.DifferentialGeometry.PDE.RicciFlow.metricCovOrderBound_stage_closed
end DifferentialGeometry.PDE.RicciFlow
