import Submission.DifferentialGeometry.Geometry.Comparison.Soul.SbrGradient
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.MetricSpace.IsometricSMul

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.NNReal
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

@[simp] theorem intrinsicRightDerivative_add_const
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (F : M → ℝ) (p : M) (v : TangentSpace I p) (c : ℝ) :
    intrinsicRightDerivative g hEnorm (fun q => F q + c) p v =
      intrinsicRightDerivative g hEnorm F p v := by
  change derivWithin (fun t => F (intrinsicGeodesic g hEnorm p v t) + c) (_root_.Set.Ioi 0) 0 =
    derivWithin (fun t => F (intrinsicGeodesic g hEnorm p v t)) (_root_.Set.Ioi 0) 0
  exact derivWithin_add_const c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.intrinsicRightDerivative_add_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.intrinsicRightDerivative_add_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.intrinsicRightDerivative_add_const ``Submission.DifferentialGeometry.Geometry.Topology.intrinsicRightDerivative_add_const

variable [T2Space (TangentBundle I M)]

@[simp] theorem intrinsicGeneralizedGradient_add_const
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hconc : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ _root_.Set.univ (fun t => F (intrinsicGeodesic g hEnorm q u t)))
    (c : ℝ) (p : M) :
    intrinsicGeneralizedGradient g hEnorm
        ((Isometry.lipschitzWith_iff L (isometry_add_right c)).mpr hF)
        (fun q u => (hconc q u).add_const c) p =
      intrinsicGeneralizedGradient g hEnorm hF hconc p := by
  have hFshift : LipschitzWith L (fun q => F q + c) :=
    (Isometry.lipschitzWith_iff L (isometry_add_right c)).mpr hF
  have hconcshift : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ _root_.Set.univ (fun t => F (intrinsicGeodesic g hEnorm q u t) + c) :=
    fun q u => (hconc q u).add_const c
  apply (intrinsicGeneralizedGradient_eq_iff g hEnorm hF hconc p _).mpr
  have hspec := intrinsicGeneralizedGradient_spec g hEnorm hFshift hconcshift p
  constructor
  · intro v
    simpa only [intrinsicRightDerivative_add_const] using hspec.1 v
  · simpa only [intrinsicRightDerivative_add_const] using hspec.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_add_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_add_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_add_const ``Submission.DifferentialGeometry.Geometry.Topology.intrinsicGeneralizedGradient_add_const

theorem normalized_intrinsicGeneralizedGradient_add_const
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hconc : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ _root_.Set.univ (fun t => F (intrinsicGeodesic g hEnorm q u t)))
    (c : ℝ) (p : M) :
    let Gc := intrinsicGeneralizedGradient g hEnorm
      ((Isometry.lipschitzWith_iff L (isometry_add_right c)).mpr hF)
      (fun q u => (hconc q u).add_const c) p
    let G := intrinsicGeneralizedGradient g hEnorm hF hconc p
    (g.inner p Gc Gc)⁻¹ • Gc = (g.inner p G G)⁻¹ • G := by
  dsimp only
  rw [intrinsicGeneralizedGradient_add_const g hEnorm hF hconc c p]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.normalized_intrinsicGeneralizedGradient_add_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.normalized_intrinsicGeneralizedGradient_add_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.normalized_intrinsicGeneralizedGradient_add_const ``Submission.DifferentialGeometry.Geometry.Topology.normalized_intrinsicGeneralizedGradient_add_const

end DifferentialGeometry.Geometry.Topology
