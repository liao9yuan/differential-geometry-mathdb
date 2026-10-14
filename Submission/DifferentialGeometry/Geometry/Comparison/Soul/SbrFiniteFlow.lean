import Submission.DifferentialGeometry.Geometry.Comparison.Soul.SbrGradientSpeed
import Submission.DifferentialGeometry.Geometry.Comparison.Soul.SbrMetricVelocity

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

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
set_option backward.isDefEq.respectTransparency false in
private theorem hasMFDerivWithinAt_of_time_shift
    (eta : ℝ → M) (s : ℝ) (V : TangentSpace I (eta s))
    (hshift : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun h => eta (s + h)) (_root_.Set.Ici 0) 0
      (ContinuousLinearMap.toSpanSingleton ℝ V)) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I eta (_root_.Set.Ici s) s
      (ContinuousLinearMap.toSpanSingleton ℝ V) := by
  have htime : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun t : ℝ => t - s) (_root_.Set.Ici s) s (ContinuousLinearMap.id ℝ ℝ) :=
    ((hasFDerivAt_id s).sub_const s).hasMFDerivAt.hasMFDerivWithinAt
  have houter : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
      (fun h => eta (s + h)) (_root_.Set.Ici 0) (s - s)
      (ContinuousLinearMap.toSpanSingleton ℝ V) := by
    convert! hshift using 1
    simp only [sub_self]
  have hcomp := houter.comp (f := fun t : ℝ => t - s) s htime (by
    intro t ht
    change s ≤ t at ht
    change 0 ≤ t - s
    exact sub_nonneg.mpr ht)
  have hfun : (fun h => eta (s + h)) ∘ (fun t : ℝ => t - s) = eta := by
    funext t
    change eta (s + (t - s)) = eta t
    congr 1
    ring
  rw [hfun] at hcomp
  convert! hcomp using 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.hasMFDerivWithinAt_of_time_shift
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.hasMFDerivWithinAt_of_time_shift target :: scope.openDecls } }

set_option backward.isDefEq.respectTransparency false in
theorem exists_finite_normalized_ascent_curve
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (F : M → ℝ) (L : ℝ≥0) (hF : LipschitzWith L F)
    (hconc : ∀ (p : M) (v : TangentSpace I p),
      ConcaveOn ℝ _root_.Set.univ (fun t => F (intrinsicGeodesic g hEnorm p v t)))
    (hC : IsCompact {z : M | 0 ≤ F z})
    {a T m : ℝ} (ha : 0 ≤ a) (haT : a < T) (hTm : T < m)
    (hmax : ∃ q : M, F q = m ∧ ∀ z : M, F z ≤ m)
    (x : M) (hx : F x = a) :
    ∃ eta : ℝ → M,
      LipschitzWith (Real.toNNReal (Metric.diam {z : M | 0 ≤ F z} / (m - T))) eta ∧
      eta a = x ∧ _root_.Set.MapsTo eta (_root_.Set.Icc a T) {z : M | 0 ≤ F z} ∧
      (∀ t ∈ _root_.Set.Icc a T, F (eta t) = t) ∧
      ∀ s ∈ _root_.Set.Ico a T,
        let G := intrinsicGeneralizedGradient g hEnorm hF hconc (eta s)
        G ≠ 0 ∧ HasMFDerivWithinAt 𝓘(ℝ, ℝ) I eta (_root_.Set.Ici s) s
          (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (eta s) G G)⁻¹ • G)) := by
  obtain ⟨eta, hetaLip, hetaStart, hetaMaps, hetaLevel, hetaSpeed⟩ :=
    exists_nearest_superlevel_limit_with_gradient_speed
      g hEnorm F L hF hconc hC ha haT hTm hmax x hx
  refine ⟨eta, hetaLip, hetaStart, hetaMaps, hetaLevel, ?_⟩
  intro s hs
  obtain ⟨hG, _hGnorm, hspeed⟩ := hetaSpeed s hs
  refine ⟨hG, ?_⟩
  have hlevel : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      F ((fun r => eta (s + r)) h) = F ((fun r => eta (s + r)) 0) + h := by
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hs.2)] with h hh
    simp only [add_zero]
    rw [hetaLevel (s + h) ⟨by linarith [hs.1, hh.1], by linarith [hh.2]⟩,
      hetaLevel s ⟨hs.1, hs.2.le⟩]
  have hzero := hasMFDerivWithinAt_normalized_intrinsicGeneralizedGradient
    g hEnorm hF hconc (fun h => eta (s + h))
    (by rw [add_zero]; exact hG) hlevel
    (by rw [add_zero]; simpa only [dist_comm] using hspeed)
  let G := intrinsicGeneralizedGradient g hEnorm hF hconc (eta s)
  have hzero' : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
      (fun h => eta (s + h)) (_root_.Set.Ici 0) 0
      (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (eta s) G G)⁻¹ • G)) := by
    rw [add_zero] at hzero
    exact hzero
  exact hasMFDerivWithinAt_of_time_shift eta s ((g.inner (eta s) G G)⁻¹ • G) hzero'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.exists_finite_normalized_ascent_curve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.exists_finite_normalized_ascent_curve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.exists_finite_normalized_ascent_curve ``Submission.DifferentialGeometry.Geometry.Topology.exists_finite_normalized_ascent_curve

end DifferentialGeometry.Geometry.Topology

end
