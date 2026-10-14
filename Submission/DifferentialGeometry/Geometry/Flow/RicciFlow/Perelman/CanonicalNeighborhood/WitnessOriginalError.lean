import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessNormalizedTimeJets
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessClosedBallJets

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

private local instance originalErrorC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.originalErrorC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.originalErrorC1 target :: scope.openDecls } }


theorem WindowedModelWitness.strict_original_error_of_time_towers
    {eps kappa : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness eps kappa S x t)
    (A B : ℕ → ℝ → Tensor0SField (I := I3) (M := W.model.M) (n := ∞) 2)
    (U : Set W.model.M)
    (hball : riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps) ⊆ U)
    (hA₀ : ∀ s, ∀ y ∈ U, ∀ v : Fin 2 → TangentSpace I3 y,
      A 0 s y v = (S.base.metric s).inner (W.embedding y)
        (mfderiv I3 I3 W.embedding y (v 0)) (mfderiv I3 I3 W.embedding y (v 1)))
    (hB₀ : ∀ s, B 0 s = metricTensorField (W.model.S.base.metric s))
    (J L : Set ℝ)
    (hA : ∀ q s, s ∈ J → ∀ y,
      HasDerivWithinAt (fun r => A q r y) (A (q + 1) s y) J s)
    (hB : ∀ q s, s ∈ L → ∀ y,
      HasDerivWithinAt (fun r => B q r y) (B (q + 1) s y) L s)
    (hsourceMap : _root_.Set.MapsTo (parabolicTime t (S.scalar t x)) (_root_.Set.Icc (-modelDepth eps) 0) J)
    (hmodelSub : _root_.Set.Icc (-modelDepth eps) 0 ⊆ L)
    (hstrict : ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ _root_.Set.Icc (-modelDepth eps) 0,
      ∀ y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps),
        tensor02CovDerivNormWith a (W.comparison.jet b s)
          (W.model.S.base.metric s) (W.model.S.base.metric s) y < eps) :
    ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ _root_.Set.Icc (-modelDepth eps) 0,
      ∀ y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps),
        tensor02CovDerivNormWith a
          ((S.scalar t x * (S.scalar t x)⁻¹ ^ b) • A b (t + s / S.scalar t x) - B b s)
          (W.model.S.base.metric s) (W.model.S.base.metric s) y < eps := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let A' := rescaledTensorTimeTower A t (S.scalar t x)
  have hJ : UniqueDiffOn ℝ (_root_.Set.Icc (-modelDepth eps) 0) :=
    uniqueDiffOn_Icc (neg_lt_zero.mpr (inv_pos.mpr W.eps_pos))
  have hA' (q : ℕ) (s : ℝ) (hs : s ∈ _root_.Set.Icc (-modelDepth eps) 0) (y : W.model.M) :
      HasDerivWithinAt (fun r => A' q r y) (A' (q + 1) s y) (_root_.Set.Icc (-modelDepth eps) 0) s :=
    hasDerivWithinAt_rescaledTensorTimeTower A t _ hsourceMap hA q s hs y
  have hB' (q : ℕ) (s : ℝ) (hs : s ∈ _root_.Set.Icc (-modelDepth eps) 0) (y : W.model.M) :
      HasDerivWithinAt (fun r => B q r y) (B (q + 1) s y) (_root_.Set.Icc (-modelDepth eps) 0) s :=
    (hB q s (hmodelSub hs) y).mono hmodelSub
  have hzero (s : ℝ) (_hs : s ∈ _root_.Set.Icc (-modelDepth eps) 0) (y : W.model.M)
      (hy : y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps))
      (v : Fin 2 → TangentSpace I3 y) :
      W.comparison.pullback s y v - (W.model.S.base.metric s).inner y (v 0) (v 1) =
        A' 0 s y v - B 0 s y v := by
    rw [W.comparison.pullback_eq s y hy v]
    simp only [A', rescaledTensorTimeTower, pow_zero, mul_one, ContMDiffSection.coe_smul,
      Pi.smul_apply, Tensor0SSpace.smul_apply, smul_eq_mul, hA₀ _ y (hball hy) v,
      hB₀, metricTensorField_apply, rescaledMetric, scaleMetric_inner]
  have hjet := W.comparison.jet_eq_of_genuine_towers hJ A' B
    (fun q s hs y _hy => hA' q s hs y) (fun q s hs y _hy => hB' q s hs y) hzero
  have hcomplete : RiemannianMetricComplete (I := I3) (W.model.S.base.metric 0) := by
    refine ⟨?_⟩
    exact MetricComplete.complete (W.model.atTime 0)
      (W.model_ancient.complete 0 (by change (0 : ℝ) ≤ 0; exact le_rfl))
  intro a b hab s hs y hy
  have heq := tensor02CovDerivNormWith_eq_on_riemannianClosedBall
    (W.model.S.base.metric 0) hcomplete W.model.basepoint
    (inv_pos.mpr (Real.sqrt_pos.mpr W.eps_pos))
    (W.model.S.base.metric s) (W.model.S.base.metric s)
    (W.comparison.jet b s) (A' b s - B b s) (fun z hz => hjet b s hs z hz) a hy
  change tensor02CovDerivNormWith a (A' b s - B b s)
    (W.model.S.base.metric s) (W.model.S.base.metric s) y < eps
  rw [← heq]
  exact hstrict a b hab s hs y hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.strict_original_error_of_time_towers then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.strict_original_error_of_time_towers"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.strict_original_error_of_time_towers ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.strict_original_error_of_time_towers

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
