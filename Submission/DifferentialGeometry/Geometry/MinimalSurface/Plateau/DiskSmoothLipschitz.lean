import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential
import Submission.DifferentialGeometry.Geometry.Metric.QuadraticBounds.Unit
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.Set _root_.ContinuousMap _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem diskClosedBall_uniqueMDiffWithinAt (z : closedDisk) :
    UniqueMDiffWithinAt 𝓘(ℝ, ℂ) (Metric.closedBall (0 : ℂ) 1) (z : ℂ) := by
  rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
  exact uniqueDiffOn_convex (convex_closedBall (0 : ℂ) 1) ⟨0, by
    rw [interior_closedBall (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    exact Metric.mem_ball_self (by norm_num)⟩ z z.property

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.diskClosedBall_uniqueMDiffWithinAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.diskClosedBall_uniqueMDiffWithinAt target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private theorem continuous_tangentMetricSpeed (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) :
    Continuous (fun v : TangentBundle 𝓘(ℝ, E) M =>
      Real.sqrt (g.inner v.proj v.2 v.2)) :=
  (DifferentialGeometry.metricQuad_cont (I := 𝓘(ℝ, E)) g).sqrt

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.continuous_tangentMetricSpeed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.continuous_tangentMetricSpeed target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem edist_le_of_within_speed_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (gamma : ℝ → M)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 gamma (_root_.Set.Icc (0 : ℝ) 1))
    (V : ℝ)
    (hV : ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, Real.sqrt (g.inner (gamma t)
      (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma (_root_.Set.Icc (0 : ℝ) 1) t (1 : ℝ))
      (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma (_root_.Set.Icc (0 : ℝ) 1) t (1 : ℝ))) ≤ V) :
    riemannianEDistOf g (gamma 0) (gamma 1) ≤ ENNReal.ofReal V := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  unfold riemannianEDistOf
  have hp := Manifold.riemannianEDist_le_pathELength (I := 𝓘(ℝ, E)) hgamma rfl rfl zero_le_one
  apply hp.trans
  calc
    _root_.Manifold.pathELength 𝓘(ℝ, E) gamma 0 1 = ∫⁻ t in _root_.Set.Icc (0 : ℝ) 1, ENNReal.ofReal
        (Real.sqrt (g.inner (gamma t)
          (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma (_root_.Set.Icc (0 : ℝ) 1) t 1)
          (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma (_root_.Set.Icc (0 : ℝ) 1) t 1))) := by
      rw [_root_.Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
      apply _root_.MeasureTheory.lintegral_congr
      intro t
      rw [← ofReal_norm, norm_eq_sqrt_real_inner]
      congr 2
    _ ≤ ∫⁻ _t in _root_.Set.Icc (0 : ℝ) 1, ENNReal.ofReal V :=
      _root_.MeasureTheory.setLIntegral_mono' measurableSet_Icc (fun t ht => ENNReal.ofReal_le_ofReal (hV t ht))
    _ = ENNReal.ofReal V := by
      rw [_root_.MeasureTheory.setLIntegral_const, Real.volume_Icc]
      simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.edist_le_of_within_speed_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.edist_le_of_within_speed_bound target :: scope.openDecls } }

theorem DiskSmoothUpToBoundary.exists_within_speed_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : C(closedDisk, M)}
    (hu : DiskSmoothUpToBoundary (E := E) u) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ v : ℂ,
      Real.sqrt (g.inner (diskExtension u z)
        (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u)
          (Metric.closedBall (0 : ℂ) 1) z (v : ℂ))
        (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u)
          (Metric.closedBall (0 : ℂ) 1) z (v : ℂ))) ≤ V * ‖v‖ := by
  have hud : UniqueMDiffOn 𝓘(ℝ, ℂ) (Metric.closedBall (0 : ℂ) 1) :=
    fun z hz => diskClosedBall_uniqueMDiffWithinAt ⟨z, hz⟩
  let j : closedDisk × closedDisk → TangentBundle 𝓘(ℝ, ℂ) ℂ := fun p =>
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)).symm ((p.1 : ℂ), (p.2 : ℂ))
  have hj : Continuous j :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)).symm.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  have hjet := hu.continuousOn_tangentMapWithin (by simp) hud
  have hc : Continuous (fun p : closedDisk × closedDisk =>
      tangentMapWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (Metric.closedBall (0 : ℂ) 1) (j p)) :=
    hjet.comp_continuous hj (fun p => p.1.property)
  have hs := (continuous_tangentMetricSpeed g).comp hc
  obtain ⟨V, hV⟩ := (isCompact_range hs).bddAbove
  have hunit (z v : closedDisk) :
      Real.sqrt (g.inner (diskExtension u z)
        (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (Metric.closedBall (0 : ℂ) 1) z (v : ℂ))
        (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (Metric.closedBall (0 : ℂ) 1) z (v : ℂ)))
        ≤ _root_.Max.max 0 V :=
    (hV ⟨(z, v), rfl⟩).trans (le_max_right _ _)
  refine ⟨max 0 V, le_max_left _ _, ?_⟩
  intro z hz v
  by_cases hv : v = 0
  · subst v
    let A : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, E) (diskExtension u z) :=
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (Metric.closedBall (0 : ℂ) 1) z
    change Real.sqrt (g.inner (diskExtension u z) (A 0) (A 0)) ≤ _root_.Max.max 0 V * ‖(0 : ℂ)‖
    simp
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    let w : ℂ := ‖v‖⁻¹ • v
    have hw : w ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      simp only [w, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
        inv_mul_cancel₀ hn, le_refl]
    have heq : ‖v‖ • w = v := by
      simp only [w, smul_smul, mul_inv_cancel₀ hn, one_smul]
    have hb := hunit ⟨z, hz⟩ ⟨w, hw⟩
    have hscale := DifferentialGeometry.Geometry.Riemannian.sqrt_inner_smul
      (I := 𝓘(ℝ, E)) g (diskExtension u z) ‖v‖
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (Metric.closedBall (0 : ℂ) 1) z w)
    rw [abs_of_nonneg (norm_nonneg v)] at hscale
    have hd : mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u)
        (Metric.closedBall (0 : ℂ) 1) z v =
      ‖v‖ • mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u)
        (Metric.closedBall (0 : ℂ) 1) z w := by
      let A : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, E) (diskExtension u z) :=
        mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (Metric.closedBall (0 : ℂ) 1) z
      change A v = ‖v‖ • A w
      calc
        A v = A (‖v‖ • w) := congrArg A heq.symm
        _ = ‖v‖ • A w := A.map_smul ‖v‖ w
    rw [hd, hscale]
    exact (mul_le_mul_of_nonneg_left hb (norm_nonneg v)).trans_eq (mul_comm _ _)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Geometry.DiskSmoothUpToBoundary
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.DiskSmoothUpToBoundary.exists_within_speed_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.DiskSmoothUpToBoundary.exists_within_speed_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.DiskSmoothUpToBoundary.exists_within_speed_bound ``Submission.DifferentialGeometry.Geometry.DiskSmoothUpToBoundary.exists_within_speed_bound

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem DiskSmoothUpToBoundary.exists_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : C(closedDisk, M)}
    (hu : DiskSmoothUpToBoundary (E := E) u) :
    ∃ L : ℝ≥0, ∀ z w : closedDisk,
      riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * _root_.EDist.edist z w := by
  obtain ⟨V, hV, hbound⟩ := hu.exists_within_speed_bound g
  refine ⟨NNReal.mk V hV, fun z w => ?_⟩
  let line : ℝ → ℂ := fun t => (z : ℂ) + t • ((w : ℂ) - (z : ℂ))
  have hmaps : _root_.Set.MapsTo line (_root_.Set.Icc (0 : ℝ) 1) (Metric.closedBall (0 : ℂ) 1) :=
    fun t ht => (convex_closedBall (0 : ℂ) 1).add_smul_sub_mem z.property w.property ht
  have hline : ContDiff ℝ ∞ line := contDiff_const.add (contDiff_id.smul contDiff_const)
  let gamma : ℝ → M := diskExtension u ∘ line
  have hgamma : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 gamma (_root_.Set.Icc (0 : ℝ) 1) :=
    (hu.comp hline.contMDiff.contMDiffOn hmaps).of_le (by simp)
  have hgamma0 : gamma 0 = u z := by simp [gamma, line, diskExtension_coe]
  have hgamma1 : gamma 1 = u w := by simp [gamma, line, diskExtension_coe]
  have hs : ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, Real.sqrt (g.inner (gamma t)
      (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma (_root_.Set.Icc (0 : ℝ) 1) t 1)
      (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma (_root_.Set.Icc (0 : ℝ) 1) t 1)) ≤
      V * ‖(w : ℂ) - (z : ℂ)‖ := by
    intro t ht
    have hud := (uniqueDiffOn_Icc_zero_one t ht).uniqueMDiffWithinAt
    have hdl : HasDerivAt line ((w : ℂ) - (z : ℂ)) t := by
      simpa only [line, id_eq, one_smul] using!
        ((hasDerivAt_id t).smul_const ((w : ℂ) - (z : ℂ))).const_add (z : ℂ)
    have hdu := (hu (line t) (hmaps ht)).mdifferentiableWithinAt (by simp)
    have hd := mfderivWithin_comp t hdu
      hdl.hasFDerivAt.hasMFDerivAt.mdifferentiableAt.mdifferentiableWithinAt hmaps hud
    have hdl' := hdl.hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt.mfderivWithin hud
    rw [hdl'] at hd
    have hd1 := congrArg (fun L : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, E) (gamma t) => L 1) hd
    have heq : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma (_root_.Set.Icc (0 : ℝ) 1) t 1 =
        mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (Metric.closedBall (0 : ℂ) 1)
          (line t) ((w : ℂ) - (z : ℂ)) := by
      change mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma (_root_.Set.Icc (0 : ℝ) 1) t (1 : ℝ) =
        (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u)
          (Metric.closedBall (0 : ℂ) 1) (line t) :
          ℂ →L[ℝ] TangentSpace 𝓘(ℝ, E) (gamma t)) ((1 : ℝ) • ((w : ℂ) - (z : ℂ))) at hd1
      simpa only [one_smul] using! hd1
    rw [heq]
    exact hbound (line t) (hmaps ht) ((w : ℂ) - (z : ℂ))
  have hp := edist_le_of_within_speed_bound g gamma hgamma
    (V * ‖(w : ℂ) - (z : ℂ)‖) hs
  rw [hgamma0, hgamma1, ENNReal.ofReal_mul hV] at hp
  have he : _root_.EDist.edist z w = ENNReal.ofReal ‖(w : ℂ) - (z : ℂ)‖ := by
    rw [edist_dist]
    change ENNReal.ofReal (_root_.Dist.dist (z : ℂ) (w : ℂ)) = _
    rw [dist_eq_norm, norm_sub_rev]
  simpa only [he, ENNReal.ofReal_eq_coe_nnreal hV] using hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.DiskSmoothUpToBoundary.exists_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.DiskSmoothUpToBoundary.exists_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.DiskSmoothUpToBoundary.exists_lipschitz ``Submission.DifferentialGeometry.Geometry.DiskSmoothUpToBoundary.exists_lipschitz

end DifferentialGeometry.Geometry
