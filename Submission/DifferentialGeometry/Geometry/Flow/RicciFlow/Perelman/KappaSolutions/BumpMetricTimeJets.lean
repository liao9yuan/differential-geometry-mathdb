import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorBumpTimeJets
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.OrdinaryMetricTimeJets

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance bumpMetricC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bumpMetricC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bumpMetricC1 target :: scope.openDecls } }


theorem exists_bump_metric_time_jets
    (R : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := U) D) (hS : IsSolutionOn S)
    {b : ℝ} (hcarrier : D.carrier = _root_.Set.Iic b) (hregular : D.regular = _root_.Set.Iio b)
    (χ : M → ℝ) (hχ : ContMDiff I 𝓘(ℝ) ∞ χ) (hχ01 : ∀ x, χ x ∈ _root_.Set.Icc (0 : ℝ) 1)
    (hsupp : tsupport χ ⊆ (U : Set M)) :
    ∃ B : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2,
      (∀ t, B 0 t = metricTensorField
        (R.bumpExtendOpen U (S.base.metric t) χ hχ hχ01 hsupp)) ∧
      ∀ q t, t ≤ b → ∀ x : M,
        HasDerivWithinAt (fun s => B q s x) (B (q + 1) t x) (_root_.Set.Iic b) t := by
  classical
  obtain ⟨A, hzero, hA⟩ := exists_ancient_ordinary_metric_time_jets S hS hcarrier hregular
  obtain ⟨C, hCvalue, hCout, hCderiv⟩ := exists_tensor_bump_time_tower U 2 A χ hχ hsupp (_root_.Set.Iic b)
    (fun q t ht x => (hA q t ht x).2)
  let G : ℝ → SmoothRiemannianMetric I M :=
    fun t => R.bumpExtendOpen U (S.base.metric t) χ hχ hχ01 hsupp
  have hmetric (t : ℝ) (x : M) : metricTensorField (G t) x =
      C 0 t x + (1 - χ x) • metricTensorField R x := by
    apply tensor0SSpace_ext 2 x
    intro v
    simp only [metricTensorField_apply, Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply, smul_eq_mul]
    by_cases hx : x ∈ U
    · rw [bumpExtendOpen_inner_of_mem R U (S.base.metric t) χ hχ hχ01 hsupp x hx,
        hCvalue 0 t x hx v, hzero t]
      erw [metricTensorField_apply (I := I) (M := U) (S.base.metric t) ⟨x, hx⟩ v]
      rfl
    · have hxSupp : x ∉ tsupport χ := fun h => hx (hsupp h)
      have hχzero : χ x = 0 := image_eq_zero_of_notMem_tsupport hxSupp
      rw [bumpExtendOpen_inner_of_notMem_tsupport R U (S.base.metric t) χ hχ hχ01 hsupp x hxSupp,
        hCout 0 t x hx]
      simp only [hχzero, Tensor0SSpace.zero_apply, sub_zero, one_mul, zero_add]
  let B : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2 := fun q t =>
    match q with
    | 0 => metricTensorField (G t)
    | q + 1 => C (q + 1) t
  refine ⟨B, fun _ => rfl, ?_⟩
  intro q t ht x
  cases q with
  | zero =>
    have hd := (hCderiv 0 t ht x).add_const ((1 - χ x) • metricTensorField R x)
    exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => hmetric s x) (hmetric t x)
  | succ q => exact hCderiv (q + 1) t ht x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_bump_metric_time_jets then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_bump_metric_time_jets"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_bump_metric_time_jets ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_bump_metric_time_jets

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
