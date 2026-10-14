import Submission.DifferentialGeometry.Geometry.Comparison.Soul.SbrGradient
import Submission.DifferentialGeometry.Geometry.Comparison.Soul.SbrGradientContraction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
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
  [T2Space (TangentBundle I M)]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
  {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
  (hconc : ∀ (p : M) (v : TangentSpace I p),
    ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t)))

theorem antitoneOn_dist_normalized_intrinsicGeneralizedGradient
    (xi zeta : ℝ → M) {a b : ℝ}
    (hxi : ContinuousOn xi (_root_.Set.Icc a b)) (hzeta : ContinuousOn zeta (_root_.Set.Icc a b))
    (hX : ∀ t ∈ _root_.Set.Ico a b,
      let G := intrinsicGeneralizedGradient g hEnorm hF hconc (xi t)
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I xi (_root_.Set.Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (xi t) G G)⁻¹ • G)))
    (hY : ∀ t ∈ _root_.Set.Ico a b,
      let G := intrinsicGeneralizedGradient g hEnorm hF hconc (zeta t)
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I zeta (_root_.Set.Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (zeta t) G G)⁻¹ • G)))
    (hlevel : ∀ t ∈ _root_.Set.Ico a b, F (xi t) = F (zeta t)) :
    AntitoneOn (fun t => _root_.Dist.dist (xi t) (zeta t)) (_root_.Set.Icc a b) := by
  apply antitoneOn_dist_of_normalized_gradient_right_derivatives g hEnorm F hconc
    (intrinsicGeneralizedGradient g hEnorm hF hconc)
    (fun p => (intrinsicGeneralizedGradient_spec g hEnorm hF hconc p).1)
    xi zeta hxi hzeta ?_ ?_ hlevel
  · intro t ht
    exact (hX t ht).congr_mfderiv
      (ContinuousLinearMap.smulRight_one_eq_toSpanSingleton ℝ _).symm
  · intro t ht
    exact (hY t ht).congr_mfderiv
      (ContinuousLinearMap.smulRight_one_eq_toSpanSingleton ℝ _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.antitoneOn_dist_normalized_intrinsicGeneralizedGradient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.antitoneOn_dist_normalized_intrinsicGeneralizedGradient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.antitoneOn_dist_normalized_intrinsicGeneralizedGradient ``Submission.DifferentialGeometry.Geometry.Topology.antitoneOn_dist_normalized_intrinsicGeneralizedGradient

theorem antitoneOn_dist_fixed_normalized_intrinsicGeneralizedGradient
    (xi : ℝ → M) {a b : ℝ} (hxi : ContinuousOn xi (_root_.Set.Icc a b))
    (hX : ∀ t ∈ _root_.Set.Ico a b,
      let G := intrinsicGeneralizedGradient g hEnorm hF hconc (xi t)
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I xi (_root_.Set.Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (xi t) G G)⁻¹ • G)))
    (q : M) (hlevel : ∀ t ∈ _root_.Set.Ico a b, F (xi t) ≤ F q) :
    AntitoneOn (fun t => _root_.Dist.dist (xi t) q) (_root_.Set.Icc a b) := by
  apply antitoneOn_dist_fixed_of_normalized_gradient_right_derivative g hEnorm F hconc
    (intrinsicGeneralizedGradient g hEnorm hF hconc)
    (fun p => (intrinsicGeneralizedGradient_spec g hEnorm hF hconc p).1)
    xi hxi ?_ q hlevel
  intro t ht
  exact (hX t ht).congr_mfderiv
    (ContinuousLinearMap.smulRight_one_eq_toSpanSingleton ℝ _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.antitoneOn_dist_fixed_normalized_intrinsicGeneralizedGradient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.antitoneOn_dist_fixed_normalized_intrinsicGeneralizedGradient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.antitoneOn_dist_fixed_normalized_intrinsicGeneralizedGradient ``Submission.DifferentialGeometry.Geometry.Topology.antitoneOn_dist_fixed_normalized_intrinsicGeneralizedGradient

theorem eqOn_normalized_intrinsicGeneralizedGradient_curves
    (xi zeta : ℝ → M) {a b : ℝ}
    (hxi : ContinuousOn xi (_root_.Set.Icc a b)) (hzeta : ContinuousOn zeta (_root_.Set.Icc a b))
    (hX : ∀ t ∈ _root_.Set.Ico a b,
      let G := intrinsicGeneralizedGradient g hEnorm hF hconc (xi t)
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I xi (_root_.Set.Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (xi t) G G)⁻¹ • G)))
    (hY : ∀ t ∈ _root_.Set.Ico a b,
      let G := intrinsicGeneralizedGradient g hEnorm hF hconc (zeta t)
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I zeta (_root_.Set.Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (zeta t) G G)⁻¹ • G)))
    (hlevel : ∀ t ∈ _root_.Set.Ico a b, F (xi t) = F (zeta t))
    (hinitial : xi a = zeta a) : _root_.Set.EqOn xi zeta (_root_.Set.Icc a b) := by
  have hdist := antitoneOn_dist_normalized_intrinsicGeneralizedGradient g hEnorm hF hconc
    xi zeta hxi hzeta hX hY hlevel
  intro t ht
  have ha : a ∈ _root_.Set.Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have hd := hdist ha ht ht.1
  change _root_.Dist.dist (xi t) (zeta t) ≤ _root_.Dist.dist (xi a) (zeta a) at hd
  rw [hinitial, dist_self] at hd
  exact dist_eq_zero.mp (le_antisymm hd dist_nonneg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.eqOn_normalized_intrinsicGeneralizedGradient_curves then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.eqOn_normalized_intrinsicGeneralizedGradient_curves"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.eqOn_normalized_intrinsicGeneralizedGradient_curves ``Submission.DifferentialGeometry.Geometry.Topology.eqOn_normalized_intrinsicGeneralizedGradient_curves

theorem eqOn_normalized_intrinsicGeneralizedGradient_overlap
    (xi zeta : ℝ → M) {a b₁ b₂ : ℝ}
    (hxi : ContinuousOn xi (_root_.Set.Icc a b₁)) (hzeta : ContinuousOn zeta (_root_.Set.Icc a b₂))
    (hX : ∀ t ∈ _root_.Set.Ico a b₁,
      let G := intrinsicGeneralizedGradient g hEnorm hF hconc (xi t)
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I xi (_root_.Set.Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (xi t) G G)⁻¹ • G)))
    (hY : ∀ t ∈ _root_.Set.Ico a b₂,
      let G := intrinsicGeneralizedGradient g hEnorm hF hconc (zeta t)
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I zeta (_root_.Set.Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (zeta t) G G)⁻¹ • G)))
    (hxiLevel : ∀ t ∈ _root_.Set.Ico a b₁, F (xi t) = t)
    (hzetaLevel : ∀ t ∈ _root_.Set.Ico a b₂, F (zeta t) = t)
    (hinitial : xi a = zeta a) : _root_.Set.EqOn xi zeta (_root_.Set.Icc a (_root_.Min.min b₁ b₂)) := by
  apply eqOn_normalized_intrinsicGeneralizedGradient_curves g hEnorm hF hconc xi zeta
    (hxi.mono (fun _ ht => ⟨ht.1, ht.2.trans (min_le_left b₁ b₂)⟩))
    (hzeta.mono (fun _ ht => ⟨ht.1, ht.2.trans (min_le_right b₁ b₂)⟩))
    (fun t ht => hX t ⟨ht.1, ht.2.trans_le (min_le_left b₁ b₂)⟩)
    (fun t ht => hY t ⟨ht.1, ht.2.trans_le (min_le_right b₁ b₂)⟩)
    ?_ hinitial
  intro t ht
  exact (hxiLevel t ⟨ht.1, ht.2.trans_le (min_le_left b₁ b₂)⟩).trans
    (hzetaLevel t ⟨ht.1, ht.2.trans_le (min_le_right b₁ b₂)⟩).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.eqOn_normalized_intrinsicGeneralizedGradient_overlap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.eqOn_normalized_intrinsicGeneralizedGradient_overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.eqOn_normalized_intrinsicGeneralizedGradient_overlap ``Submission.DifferentialGeometry.Geometry.Topology.eqOn_normalized_intrinsicGeneralizedGradient_overlap

end DifferentialGeometry.Geometry.Topology
