import Submission.DifferentialGeometry.Geometry.Comparison.Soul.SbrDirectional
import Submission.DifferentialGeometry.Geometry.Comparison.Busemann.Ray.CalibratedCoray
import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.PrescribedDistanceSupport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.NNReal
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Variation
open _root_.Submission.DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

private theorem intrinsicGeodesic_reverse_velocity
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (p : M) (u : TangentSpace I p) (t s : ℝ) :
    intrinsicGeodesic g hEnorm (intrinsicGeodesic g hEnorm p u t)
      (-curveVelocity (I := I) (intrinsicGeodesic g hEnorm p u) t) s =
        intrinsicGeodesic g hEnorm p u (t - s) := by
  let gamma := intrinsicGeodesic g hEnorm p u
  calc
    _ = intrinsicGeodesic g hEnorm (gamma t)
        (curveVelocity (I := I) gamma t) (-s) := by
      simpa only [neg_one_smul, neg_one_mul] using
        intrinsicGeo_smul_apply g hEnorm (gamma t)
          (curveVelocity (I := I) gamma t) (-1) s
    _ = gamma (-s + t) :=
      (congrFun (intrinsicGeodesic_continuation g hEnorm p u t) (-s)).symm
    _ = _ := by congr 1; ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.intrinsicGeodesic_reverse_velocity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.intrinsicGeodesic_reverse_velocity target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [CompleteSpace M]
  [IsRiemannianManifold I M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem hasMFDerivWithinAt_curveVelocity
    {eta : ℝ → M} {s : ℝ} (heta : MDifferentiableAt 𝓘(ℝ, ℝ) I eta s) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I eta (_root_.Set.Ici s) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight (curveVelocity (I := I) eta s)) := by
  have hlin : mfderiv 𝓘(ℝ, ℝ) I eta s =
      (1 : ℝ →L[ℝ] ℝ).smulRight (curveVelocity (I := I) eta s) := by
    apply ContinuousLinearMap.ext
    intro v
    change ℝ at v
    calc
      mfderiv 𝓘(ℝ, ℝ) I eta s v =
          mfderiv 𝓘(ℝ, ℝ) I eta s (v • (1 : ℝ)) := by
        rw [smul_eq_mul, mul_one]
      _ = v • mfderiv 𝓘(ℝ, ℝ) I eta s 1 := map_smul _ _ _
      _ = _ := rfl
  exact heta.hasMFDerivAt.hasMFDerivWithinAt.congr_mfderiv hlin

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.hasMFDerivWithinAt_curveVelocity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.hasMFDerivWithinAt_curveVelocity target :: scope.openDecls } }

theorem calibrated_intrinsic_coray_reverse_direction
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (b : M → ℝ) (C : ℝ) (p : M) (u : TangentSpace I p)
    (hu : g.inner p u u = 1)
    (hcal : ∀ s : ℝ, 0 ≤ s →
      b (intrinsicGeodesic g hEnorm p u s) = b p + s)
    (t : ℝ) (ht : 0 < t) :
    let gamma := intrinsicGeodesic g hEnorm p u
    g.inner (gamma t) (-curveVelocity (I := I) gamma t)
        (-curveVelocity (I := I) gamma t) = 1 ∧
      intrinsicRightDerivative g hEnorm (fun q => C - b q) (gamma t)
        (-curveVelocity (I := I) gamma t) = 1 := by
  let gamma := intrinsicGeodesic g hEnorm p u
  have hunit : g.inner (gamma t) (curveVelocity (I := I) gamma t)
      (curveVelocity (I := I) gamma t) = 1 :=
    (intrinsicGeodesic_speedSq_eq g hEnorm p u t).trans hu
  refine ⟨by simpa only [map_neg, neg_apply, neg_neg] using hunit, ?_⟩
  let eta := intrinsicGeodesic g hEnorm (gamma t)
    (-curveVelocity (I := I) gamma t)
  have hreverse (s : ℝ) : eta s = gamma (t - s) :=
    intrinsicGeodesic_reverse_velocity g hEnorm p u t s
  have hlocal : (fun s => C - b (eta s)) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => C - b (gamma t) + s) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    rw [hreverse s, hcal (t - s) (sub_nonneg.mpr hs.le), hcal t ht.le]
    ring
  have hderiv : HasDerivAt (fun s => C - b (eta s)) 1 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_add (C - b (gamma t))).congr_of_eventuallyEq hlocal
  exact hderiv.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.calibrated_intrinsic_coray_reverse_direction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.calibrated_intrinsic_coray_reverse_direction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.calibrated_intrinsic_coray_reverse_direction ``Submission.DifferentialGeometry.Geometry.Topology.calibrated_intrinsic_coray_reverse_direction

theorem exists_busemann_reversed_coray
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (c : ℝ≥0 → M) (hc : Isometry c) (p : M) (C : ℝ)
    (hlevel : busemann c p ≤ C) :
    let T := C - busemann c p
    ∃ u : TangentSpace I p, g.inner p u u = 1 ∧
      let gamma := intrinsicGeodesic g hEnorm p u
      let delta := fun s => gamma (T - s)
      ContMDiff 𝓘(ℝ, ℝ) I ∞ delta ∧
      (∀ s : ℝ, (curveVelocity (I := I) delta s : E) =
        -(curveVelocity (I := I) gamma (T - s) : E)) ∧
      (∀ s : ℝ, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I delta (_root_.Set.Ici s) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (curveVelocity (I := I) delta s))) ∧
      busemann c (delta 0) = C ∧ delta T = p ∧
      (∀ s ∈ _root_.Set.Icc 0 T, C - busemann c (delta s) = s) ∧
      (∀ s ∈ _root_.Set.Icc 0 T, ∀ t ∈ _root_.Set.Icc 0 T, _root_.Dist.dist (delta s) (delta t) = _root_.Dist.dist s t) ∧
      (∀ s ∈ _root_.Set.Ico 0 T,
        g.inner (delta s) (curveVelocity (I := I) delta s)
          (curveVelocity (I := I) delta s) = 1 ∧
        intrinsicRightDerivative g hEnorm (fun q => C - busemann c q)
          (delta s) (curveVelocity (I := I) delta s) = 1) := by
  let T := C - busemann c p
  have hT : 0 ≤ T := sub_nonneg.mpr hlevel
  obtain ⟨u, hu, hiso, hcal⟩ := exists_calibrated_intrinsic_ray g hEnorm c hc p
  let gamma := intrinsicGeodesic g hEnorm p u
  let delta := fun s => gamma (T - s)
  have hgamma : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma :=
    intrinsicGeodesic_contMDiff g hEnorm p u
  have hdelta : ContMDiff 𝓘(ℝ, ℝ) I ∞ delta :=
    hgamma.comp (contMDiff_const.sub contMDiff_id)
  have hvel (s : ℝ) : (curveVelocity (I := I) delta s : E) =
      -(curveVelocity (I := I) gamma (T - s) : E) := by
    have h := curveVelocity_affine (I := I) gamma (-1) T s
      (hgamma.contMDiffAt.mdifferentiableAt (by simp))
    have hfun : (fun r : ℝ => gamma (-1 * r + T)) = delta := by
      funext r
      dsimp only [delta]
      congr 1
      ring
    have htime : -1 * s + T = T - s := by ring
    rw [hfun, htime] at h
    simpa only [neg_one_smul] using h
  refine ⟨u, hu, hdelta, hvel, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    exact hasMFDerivWithinAt_curveVelocity
      (hdelta.contMDiffAt.mdifferentiableAt (by simp))
  · change busemann c (gamma (T - 0)) = C
    rw [sub_zero, hcal T hT]
    dsimp only [T]
    ring
  · change gamma (T - T) = p
    simp only [sub_self, gamma, intrinsicGeodesic_zero]
  · intro s hs
    change C - busemann c (gamma (T - s)) = s
    rw [hcal (T - s) (sub_nonneg.mpr hs.2)]
    dsimp only [T]
    ring
  · intro s hs t ht
    have hd := hiso.dist_eq ⟨T - s, sub_nonneg.mpr hs.2⟩
      ⟨T - t, sub_nonneg.mpr ht.2⟩
    change _root_.Dist.dist (delta s) (delta t) = |(T - s) - (T - t)| at hd
    calc
      dist (delta s) (delta t) = |(T - s) - (T - t)| := hd
      _ = |-(s - t)| := by congr 1; ring
      _ = _root_.Dist.dist s t := by rw [abs_neg, Real.dist_eq]
  · intro s hs
    have h := calibrated_intrinsic_coray_reverse_direction g hEnorm
      (busemann c) C p u hu hcal (T - s) (sub_pos.mpr hs.2)
    rw [hvel s]
    exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.exists_busemann_reversed_coray then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.exists_busemann_reversed_coray"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.exists_busemann_reversed_coray ``Submission.DifferentialGeometry.Geometry.Topology.exists_busemann_reversed_coray

end DifferentialGeometry.Geometry.Topology
