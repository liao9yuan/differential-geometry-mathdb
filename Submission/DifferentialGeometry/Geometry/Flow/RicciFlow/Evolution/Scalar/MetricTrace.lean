import Submission.DifferentialGeometry.Geometry.Operator.MetricTraceTimeDerivative
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem scalar_hasDerivWithinAt_of_ricci_deriv
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {x : M} {t : ℝ} {J : Set ℝ} (B : Tensor0SSpace (I := I) 2 x)
    (hg : ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun r => (S.base.metric r).inner x v w)
        (-2 * S.ricciAt t x (vec2 v w)) J t)
    (hRic : ∀ v : Fin 2 → TangentSpace I x,
      HasDerivWithinAt (fun r => S.ricciAt r x v) (- (1 / 2 : ℝ) * B v) J t) :
    HasDerivWithinAt (fun r => S.scalar r x)
      (2 * normSq0S (S.base.metric t) x 2 (S.ricciAt t x) -
        (1 / 2 : ℝ) * metricTracePair0SAt (S.base.metric t) B) J t := by
  have hh := hasDerivWithinAt_metricTracePair0SAt S.base.metric
    ((-2 : ℝ) • S.ricciAt t x) (fun r => S.ricciAt r x) ((-(1 / 2 : ℝ)) • B)
    (by simpa only [smul_apply, smul_eq_mul] using hg)
    (by simpa only [smul_apply, smul_eq_mul] using hRic)
  change HasDerivWithinAt (fun r => S.scalar r x) _ J t at hh
  convert hh using 1
  rw [_root_.Submission.Tensor0SBundle.inner0S_smul_left, metricTracePair0SAt_smul]
  change 2 * normSq0S (S.base.metric t) x 2 (S.ricciAt t x) -
      1 / 2 * metricTracePair0SAt (S.base.metric t) B =
    - (-2 * normSq0S (S.base.metric t) x 2 (S.ricciAt t x)) +
      -(1 / 2) * metricTracePair0SAt (S.base.metric t) B
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalar_hasDerivWithinAt_of_ricci_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalar_hasDerivWithinAt_of_ricci_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalar_hasDerivWithinAt_of_ricci_deriv ``Submission.DifferentialGeometry.PDE.RicciFlow.scalar_hasDerivWithinAt_of_ricci_deriv

theorem scalar_derivWithin_Iic_ge_of_ricci_deriv
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {x : M} {t a β : ℝ} (hat : a < t) (B : Tensor0SSpace (I := I) 2 x)
    (hg : ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun r => (S.base.metric r).inner x v w)
        (-2 * S.ricciAt t x (vec2 v w)) (_root_.Set.Icc a t) t)
    (hRic : ∀ v : Fin 2 → TangentSpace I x,
      HasDerivWithinAt (fun r => S.ricciAt r x v)
        (- (1 / 2 : ℝ) * B v) (_root_.Set.Icc a t) t)
    (htrace : |metricTracePair0SAt (S.base.metric t) B| ≤ β) :
    (2 : ℝ) * (S.scalar t x) ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        (derivWithin (fun r => S.scalar r x) (_root_.Set.Iic t) t + β / 2) := by
  have hd := scalar_hasDerivWithinAt_of_ricci_deriv S B hg hRic
  have hnear : _root_.Set.Icc a t ∈ 𝓝[≤] t :=
    Icc_mem_nhdsLE hat
  have hderiv := (hd.mono_of_mem_nhdsWithin hnear).derivWithin (uniqueDiffWithinAt_Iic t)
  classical
  let b := Module.finBasis ℝ (TangentSpace I x)
  have htr := metricTracePair0SAt_sq_le_card_mul_normSq0S (S.base.metric t) b
    (basisInvMetric (S.base.metric t) x b) (basisInvMetric_isInverse (S.base.metric t) x b)
    (S.ricciAt t x)
  simp only [Fintype.card_fin] at htr
  change S.scalar t x ^ 2 ≤ (Module.finrank ℝ E : ℝ) *
    normSq0S (S.base.metric t) x 2 (S.ricciAt t x) at htr
  have hdim : 0 ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have he := mul_le_mul_of_nonneg_left (le_abs_self
    (metricTracePair0SAt (S.base.metric t) B) |>.trans htrace) hdim
  rw [hderiv]
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalar_derivWithin_Iic_ge_of_ricci_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalar_derivWithin_Iic_ge_of_ricci_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalar_derivWithin_Iic_ge_of_ricci_deriv ``Submission.DifferentialGeometry.PDE.RicciFlow.scalar_derivWithin_Iic_ge_of_ricci_deriv

end DifferentialGeometry.PDE.RicciFlow
