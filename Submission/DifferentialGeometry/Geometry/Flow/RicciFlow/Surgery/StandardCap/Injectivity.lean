import Submission.DifferentialGeometry.Geometry.Metric.CompactInjectivity
import Submission.DifferentialGeometry.Geometry.Metric.LocalExponential
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Distance
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.EndTranslations
import Submission.DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private local instance capBundle : _root_.Bundle.RiemannianBundle (fun x : E3 => TangentSpace (𝓡 3) x) :=
  ⟨metric.toRiemannianMetric⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.capBundle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.capBundle target :: scope.openDecls } }

private local instance capContinuous :
    IsContinuousRiemannianBundle E3 (fun x : E3 => TangentSpace (𝓡 3) x) :=
  ⟨metric.inner, metric.contMDiff.continuous, fun _ _ _ => rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.capContinuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.capContinuous target :: scope.openDecls } }

private abbrev capSpace : EMetricSpace E3 := EMetricSpace.ofRiemannianMetric (𝓡 3) E3

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.capSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.capSpace target :: scope.openDecls } }

private local instance capPseudo : PseudoEMetricSpace E3 := capSpace.toPseudoEMetricSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.capPseudo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.capPseudo target :: scope.openDecls } }

private local instance capComplete : @CompleteSpace E3 capSpace.toUniformSpace :=
  metric_complete.complete

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.capComplete
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.capComplete target :: scope.openDecls } }

private theorem cap_enorm (p : E3) (v : TangentSpace (𝓡 3) p) :
    ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (metric.inner p v v)) := by
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.cap_enorm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.cap_enorm target :: scope.openDecls } }

private theorem intrinsicGeodesic_radial_bound (p z : E3) {t : ℝ}
    (ht : t ∈ _root_.Set.Icc (-1 : ℝ) 1) :
    |‖intrinsicGeodesic metric cap_enorm p (normalFrame metric p z) t‖ - ‖p‖| ≤ ‖z‖ := by
  have hdist : riemannianEDistOf metric p
      (intrinsicGeodesic metric cap_enorm p (normalFrame metric p z) t) ≤
      ENNReal.ofReal ‖z‖ := by
    by_cases ht0 : 0 ≤ t
    · have h := intrinsicGeodesic_riemannianEDist_le metric cap_enorm p
        (normalFrame metric p z) ht0
      rw [intrinsicGeodesic_zero metric cap_enorm p (normalFrame metric p z),
        normalFrame_sqrt metric p z, sub_zero] at h
      exact h.trans (ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (norm_nonneg z) ht.2))
    · have h := intrinsicGeodesic_riemannianEDist_le metric cap_enorm p
        (normalFrame metric p z) (le_of_lt (lt_of_not_ge ht0))
      rw [intrinsicGeodesic_zero metric cap_enorm p (normalFrame metric p z),
        normalFrame_sqrt metric p z, zero_sub] at h
      rw [_root_.Manifold.riemannianEDist_comm] at h
      exact h.trans (ENNReal.ofReal_le_ofReal
        (mul_le_of_le_one_right (norm_nonneg z) (by linarith [ht.1])))
  exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg z)).mp
    ((radial_difference_le_edist p _).trans hdist)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.intrinsicGeodesic_radial_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.intrinsicGeodesic_radial_bound target :: scope.openDecls } }

private theorem injectivityRadius_le_of_partialIso
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (U : _root_.TopologicalSpace.Opens E3) (hU : (U : Set E3) ⊆ Φ.source)
    (hpres : ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 3) x,
      metric.inner x v w = metric.inner (Φ x)
        (mfderiv (𝓡 3) (𝓡 3) Φ x v) (mfderiv (𝓡 3) (𝓡 3) Φ x w))
    (p : E3) (hp : p ∈ U) (ρ : ℝ)
    (hρ : ENNReal.ofReal ρ < intrinsicInjRadius metric cap_enorm (Φ p))
    (hstay : ∀ z : E3, ‖z‖ < ρ →
      _root_.Set.MapsTo (intrinsicGeodesic metric cap_enorm p (normalFrame metric p z))
        (_root_.Set.Icc (-1 : ℝ) 1) U) :
    ENNReal.ofReal ρ ≤ intrinsicInjRadius metric cap_enorm p := by
  let D := (Φ.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (hU hp)).mfderivToContinuousLinearEquiv
    (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  let T : E3 ≃L[ℝ] E3 :=
    ((normalFrame metric p).trans D).trans (normalFrame metric (Φ p)).symm
  have hT (z : E3) : normalFrame metric (Φ p) (T z) =
      mfderiv (𝓡 3) (𝓡 3) Φ p (normalFrame metric p z) := by
    exact (normalFrame metric (Φ p)).apply_symm_apply _
  have hnorm (z : E3) : ‖T z‖ = ‖z‖ := by
    have hsq : ‖T z‖ ^ 2 = ‖z‖ ^ 2 := calc
      ‖T z‖ ^ 2 = metric.inner (Φ p)
          (normalFrame metric (Φ p) (T z)) (normalFrame metric (Φ p) (T z)) :=
        (normalFrame_normSq metric (Φ p) (T z)).symm
      _ = metric.inner (Φ p) (mfderiv (𝓡 3) (𝓡 3) Φ p (normalFrame metric p z))
          (mfderiv (𝓡 3) (𝓡 3) Φ p (normalFrame metric p z)) := by rw [hT]
      _ = metric.inner p (normalFrame metric p z) (normalFrame metric p z) :=
        (hpres p hp _ _).symm
      _ = ‖z‖ ^ 2 := normalFrame_normSq metric p z
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  apply le_intrInjRadius metric cap_enorm p
  change Set.InjOn (intrinsicFramedExp metric cap_enorm p) _
  rw [Metric.eball_ofReal]
  intro v hv w hw heq
  have hvnorm : ‖v‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  have hwnorm : ‖w‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using hw
  have hmap (z : E3) (hz : ‖z‖ < ρ) :
      Φ (intrinsicFramedExp metric cap_enorm p z) =
        intrinsicFramedExp metric cap_enorm (Φ p) (T z) := by
    rw [intrinsicFrame_apply, intrinsicFrame_apply, hT]
    exact expMapIntrinsic_map_partialIso metric metric cap_enorm cap_enorm Φ U hU hpres
      p (normalFrame metric p z) (hstay z hz)
  apply T.injective
  apply intrinsicInjOn_ball metric cap_enorm (Φ p) hρ
  · simpa only [Metric.mem_ball, dist_zero_right, hnorm] using hvnorm
  · simpa only [Metric.mem_ball, dist_zero_right, hnorm] using hwnorm
  · exact (hmap v hvnorm).symm.trans ((congrArg (Φ : E3 → E3) heq).trans (hmap w hwnorm))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.injectivityRadius_le_of_partialIso
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.injectivityRadius_le_of_partialIso target :: scope.openDecls } }

theorem exists_pos_le_intrinsicInjectivityRadius :
    ∃ ι : ℝ, 0 < ι ∧ ∀ p : E3,
      ENNReal.ofReal ι ≤ intrinsicInjectivityRadius metric metric_complete p := by
  obtain ⟨σ, hσ, hcompact⟩ := exists_pos_le_intrinsicInjectivityRadius_on_compact
    metric metric_complete (_root_.ProperSpace.isCompact_closedBall (0 : E3) (transitionEnd + 2))
  let ι : ℝ := _root_.Min.min (σ / 2) (1 / 2)
  have hι : 0 < ι := lt_min (half_pos hσ) (by norm_num)
  have hισ : ι < σ := (min_le_left _ _).trans_lt (half_lt_self hσ)
  have hιhalf : ι ≤ 1 / 2 := min_le_right _ _
  have hbound (q : E3) (hq : ‖q‖ ≤ transitionEnd + 2) :
      ENNReal.ofReal σ ≤ intrinsicInjectivityRadius metric metric_complete q :=
    hcompact q (by simpa only [Metric.mem_closedBall, dist_zero_right] using hq)
  refine ⟨ι, hι, fun p => ?_⟩
  by_cases hp : ‖p‖ ≤ transitionEnd + 1
  · exact (ENNReal.ofReal_le_ofReal hισ.le).trans (hbound p (by linarith))
  · have hpend : transitionEnd < ‖p‖ := by linarith [lt_of_not_ge hp]
    let s : ℝ := transitionEnd + 2 - ‖p‖
    have hpin : p ∈ endTranslationDomain s := mem_endTranslationDomain_to_fixed_radius hpend
    have href : ‖radialTranslationDiffeomorph s p‖ = transitionEnd + 2 :=
      endTranslationDiffeomorph_norm_to_fixed_radius hpend
    have hrefInj : ENNReal.ofReal ι <
        intrinsicInjRadius metric cap_enorm (radialTranslationDiffeomorph s p) :=
      ((ENNReal.ofReal_lt_ofReal_iff hσ).mpr hισ).trans_le (hbound _ href.le)
    change ENNReal.ofReal ι ≤ intrinsicInjRadius metric cap_enorm p
    apply injectivityRadius_le_of_partialIso (radialTranslationDiffeomorph s)
      (endTranslationDomain s) (endTranslationDomain_subset_source s)
      (endTranslationDiffeomorph_metric_inner s) p hpin ι hrefInj
    intro z hz t ht
    have hrad := intrinsicGeodesic_radial_bound p z ht
    have hlower := (abs_le.mp hrad).1
    change transitionEnd < ‖intrinsicGeodesic metric cap_enorm p (normalFrame metric p z) t‖ ∧
      transitionEnd < ‖intrinsicGeodesic metric cap_enorm p (normalFrame metric p z) t‖ + s
    constructor
    · linarith [lt_of_not_ge hp]
    · dsimp only [s]
      linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_le_intrinsicInjectivityRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_le_intrinsicInjectivityRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_le_intrinsicInjectivityRadius ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_le_intrinsicInjectivityRadius

end DifferentialGeometry.PDE.RicciFlow.StandardCap
