import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompleteMetricMinimizingCurve
import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.CompleteShortening
import Submission.DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Comparison.Toponogov
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance completeUnitArmC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.completeUnitArmC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.completeUnitArmC1 target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun q : N => TangentSpace I q)]
  [IsContinuousRiemannianBundle E (fun q : N => TangentSpace I q)]

theorem completeMetric_compatible_completeSpace
    [IsRiemannianManifold I N]
    (g : SmoothRiemannianMetric I N) (hEnorm : IsMetricNorm (I := I) g)
    (hcomplete : RiemannianMetricComplete (I := I) g) : CompleteSpace N := by
  let m : PseudoEMetricSpace N := inferInstance
  have hdist (x y : N) : riemannianEDistOf (I := I) g x y = @_root_.EDist.edist N m.toEDist x y :=
    (riemannianEDistOf_eq_riemannianEDist g hEnorm x y).trans
      (IsRiemannianManifold.out (I := I) x y).symm
  let _ : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace I N
  let _ : T3Space N := inferInstance
  let _ : _root_.Bundle.RiemannianBundle (fun x : N => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let mG : EMetricSpace N := EMetricSpace.ofRiemannianMetric I N
  have hcanonical : @CompleteSpace N mG.toPseudoEMetricSpace.toUniformSpace := hcomplete.complete
  have heq : mG.toPseudoEMetricSpace = m := by
    apply PseudoEMetricSpace.ext
    ext x y
    change riemannianEDistOf (I := I) g x y = @_root_.EDist.edist N m.toEDist x y
    exact hdist x y
  change @CompleteSpace N m.toUniformSpace
  rw [← heq]
  exact hcanonical

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.completeMetric_compatible_completeSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.completeMetric_compatible_completeSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.completeMetric_compatible_completeSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.completeMetric_compatible_completeSpace

theorem completeMetric_compatible_properSpace [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [IsRiemannianManifold I N]
    (g : SmoothRiemannianMetric I N) (hEnorm : IsMetricNorm (I := I) g)
    (hcomplete : RiemannianMetricComplete (I := I) g) : ProperSpace N := by
  refine ProperSpace.of_isCompact_closedBall_of_le (α := N) 0 ?_
  intro x R hR
  have hc := hcomplete.closedEBall_isCompact x R
  have heq : {y : N | riemannianEDistOf (I := I) g x y ≤ ENNReal.ofReal R} =
      Metric.closedBall x R := by
    ext y
    simp only [_root_.Set.mem_ofPred_eq, riemannianEDistOf_eq_riemannianEDist g hEnorm,
      ← IsRiemannianManifold.out (I := I), edist_le_ofReal hR, Metric.mem_closedBall,
      dist_comm y x]
  rwa [heq] at hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.completeMetric_compatible_properSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.completeMetric_compatible_properSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.completeMetric_compatible_properSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.completeMetric_compatible_properSpace

theorem completeMetric_exists_unit_arm [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [IsRiemannianManifold I N] [CompleteSpace N]
    (g : SmoothRiemannianMetric I N) (hEnorm : IsMetricNorm (I := I) g)
    (x y : N) (hxy : x ≠ y) :
    ∃ u : TangentSpace I x, g.inner x u u = 1 ∧
      intrinsicGeodesic (I := I) g hEnorm x u (_root_.Dist.dist x y) = y ∧
      ∀ t ∈ _root_.Set.Icc (0 : ℝ) (_root_.Dist.dist x y),
        (_root_.Manifold.riemannianEDist I x (intrinsicGeodesic (I := I) g hEnorm x u t)).toReal = t := by
  have hfin : _root_.Manifold.riemannianEDist I x y ≠ ⊤ := by
    rw [← IsRiemannianManifold.out (I := I)]
    exact edist_ne_top x y
  have hdist : (_root_.Manifold.riemannianEDist I x y).toReal = _root_.Dist.dist x y := by
    rw [← IsRiemannianManifold.out (I := I), ← dist_edist]
  obtain ⟨v, hvexp, hvnorm⟩ := minExp_of_ne_top g hEnorm x y hfin
  have hdpos : 0 < _root_.Dist.dist x y := dist_pos.mpr hxy
  let u : TangentSpace I x := (_root_.Dist.dist x y)⁻¹ • v
  have hvinner : g.inner x v v = (_root_.Dist.dist x y) ^ 2 := by
    rw [← Real.sq_sqrt (gInner_self_nonneg (I := I) g x v), hvnorm, hdist]
  have hu : g.inner x u u = 1 := by
    dsimp only [u]
    rw [gInner_smul_self (I := I) g x (_root_.Dist.dist x y)⁻¹ v, hvinner,
      ← mul_pow, inv_mul_cancel₀ hdpos.ne', one_pow]
  have hsmul : _root_.Dist.dist x y • u = v := by
    dsimp only [u]
    rw [smul_smul, mul_inv_cancel₀ hdpos.ne', one_smul]
  have hend : intrinsicGeodesic (I := I) g hEnorm x u (_root_.Dist.dist x y) = y := by
    calc
      _ = expMapIntrinsic (I := I) g hEnorm x (_root_.Dist.dist x y • u) :=
        (intrinsicGeodesic_smul (I := I) g hEnorm x u (_root_.Dist.dist x y)).symm
      _ = y := by rw [hsmul]; exact hvexp
  have hmin :
      (_root_.Manifold.riemannianEDist I x (intrinsicGeodesic (I := I) g hEnorm x u (_root_.Dist.dist x y))).toReal =
        dist x y := by rw [hend]; exact hdist
  refine ⟨u, hu, hend, ?_⟩
  intro t ht
  exact unit_intrinsic_subsegment_dist g hEnorm x u hu (_root_.Dist.dist x y) t hdpos ht.1 ht.2 hmin

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.completeMetric_exists_unit_arm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.completeMetric_exists_unit_arm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.completeMetric_exists_unit_arm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.completeMetric_exists_unit_arm

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
