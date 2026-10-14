import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornRayRegularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W]

private theorem endRay_cross_distance {E : UniformSpace.Completion W}
    (a b : EndRay E) {t s r : ℝ}
    (ht : t ∈ _root_.Set.Ioc 0 a.length) (htb : t ≤ b.length)
    (hcontact : a.point t = b.point t)
    (hs : s ∈ _root_.Set.Ioc 0 a.length) (hr : r ∈ _root_.Set.Ioc 0 b.length)
    (hrt : r ≤ t) (hts : t ≤ s) : _root_.Dist.dist (a.point s) (b.point r) = s - r := by
  have hupper := dist_triangle (a.point s) (a.point t) (b.point r)
  rw [a.minimizing s hs t ht, hcontact, b.minimizing t ⟨ht.1, htb⟩ r hr,
    abs_of_nonneg (sub_nonneg.mpr hts), abs_of_nonneg (sub_nonneg.mpr hrt)] at hupper
  have hlower := dist_triangle (a.point s : UniformSpace.Completion W)
    (b.point r : UniformSpace.Completion W) E
  rw [UniformSpace.Completion.dist_eq, a.radial s hs, b.radial r hr] at hlower
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRay_cross_distance
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.endRay_cross_distance target :: scope.openDecls } }

private def spliceEndRay {E : UniformSpace.Completion W}
    (a b : EndRay E) {t : ℝ} (ht : t ∈ _root_.Set.Ioc 0 a.length)
    (htb : t ≤ b.length) (hcontact : a.point t = b.point t) : EndRay E where
  length := a.length
  length_pos := a.length_pos
  point s := if s ≤ t then b.point s else a.point s
  radial := by
    intro s hs
    split_ifs with hst
    · exact b.radial s ⟨hs.1, hst.trans htb⟩
    · exact a.radial s hs
  minimizing := by
    intro s hs r hr
    by_cases hst : s ≤ t
    · by_cases hrt : r ≤ t
      · simp only [if_pos hst, if_pos hrt]
        exact b.minimizing s ⟨hs.1, hst.trans htb⟩ r ⟨hr.1, hrt.trans htb⟩
      · simp only [if_pos hst, if_neg hrt]
        rw [dist_comm, endRay_cross_distance a b ht htb hcontact hr
          ⟨hs.1, hst.trans htb⟩ hst (not_le.mp hrt).le,
          abs_of_nonpos (by linarith : s - r ≤ 0)]
        ring
    · by_cases hrt : r ≤ t
      · simp only [if_neg hst, if_pos hrt]
        rw [endRay_cross_distance a b ht htb hcontact hs
          ⟨hr.1, hrt.trans htb⟩ hrt (not_le.mp hst).le,
          abs_of_nonneg (by linarith : 0 ≤ s - r)]
      · simp only [if_neg hst, if_neg hrt]
        exact a.minimizing s hs r hr

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.spliceEndRay
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.spliceEndRay target :: scope.openDecls } }

variable [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem geodesics_eqOn_of_common_germ
    (g : SmoothRiemannianMetric I3 W) {f h : ℝ → W} {L q : ℝ}
    (hq : q ∈ _root_.Set.Ioo 0 L)
    (hf : Geodesic.IsGeodesicOn g f (_root_.Set.Ioo 0 L))
    (hh : Geodesic.IsGeodesicOn g h (_root_.Set.Ioo 0 L))
    (hfc : ContinuousOn f (_root_.Set.Ioo 0 L)) (hhc : ContinuousOn h (_root_.Set.Ioo 0 L))
    (hgerm : f =ᶠ[𝓝 q] h) : _root_.Set.EqOn f h (_root_.Set.Ioo 0 L) := by
  let O : Set ℝ := _root_.Set.Ioo (-q) (L - q)
  have hmap : _root_.Set.MapsTo (fun s : ℝ => s + q) O (_root_.Set.Ioo 0 L) := by
    intro s hs
    change -q < s ∧ s < L - q at hs
    constructor <;> linarith [hs.1, hs.2]
  have hshift (c : ℝ → W) (hc : Geodesic.IsGeodesicOn g c (_root_.Set.Ioo 0 L)) :
      Geodesic.IsGeodesicOn g (fun s => c (s + q)) O := by
    intro s hs
    have h := Geodesic.hasGeodesicEquationAt_comp_affine (c := (1 : ℝ)) (d := q)
      (t := s) (by simpa only [one_mul] using hc (s + q) (hmap hs))
    simpa only [one_mul] using h
  have hadd : _root_.Filter.Tendsto (fun s : ℝ => s + q) (𝓝 0) (𝓝 q) := by
    have h : _root_.Filter.Tendsto (fun s : ℝ => s + q) (𝓝 0) (𝓝 (0 + q)) :=
      (_root_.Filter.tendsto_id : _root_.Filter.Tendsto (fun s : ℝ => s) (𝓝 0) (𝓝 0)).add tendsto_const_nhds
    simpa only [zero_add] using h
  have hlocal : (fun s : ℝ => f (s + q)) =ᶠ[𝓝 0] (fun s => h (s + q)) :=
    hadd.eventually hgerm
  have hzero : (0 : ℝ) ∈ O := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have heq : _root_.Set.EqOn (fun s : ℝ => f (s + q)) (fun s => h (s + q)) O := by
    apply geo_eqOn_of_initial g isOpen_Ioo isPreconnected_Ioo hzero (hshift f hf) (hshift h hh)
      (hfc.comp (continuous_id.add continuous_const).continuousOn hmap)
      (hhc.comp (continuous_id.add continuous_const).continuousOn hmap) hlocal.eq_of_nhds
    have hmfd : mfderiv 𝓘(ℝ, ℝ) I3 (fun s : ℝ => f (s + q)) 0 =
        mfderiv 𝓘(ℝ, ℝ) I3 (fun s : ℝ => h (s + q)) 0 := hlocal.mfderiv_eq
    exact congrArg (fun A => (A (1 : ℝ) : ThreeSpace)) hmfd
  intro s hs
  have hsq : s - q ∈ O := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  simpa only [sub_add_cancel] using heq hsq

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.geodesics_eqOn_of_common_germ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.geodesics_eqOn_of_common_germ target :: scope.openDecls } }

variable [SigmaCompactSpace W]

theorem finiteHorn_endRay_unique_inward
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) :
    ∃ d : ℝ, 0 < d ∧ ∀ a b : EndRay H.endpoint, ∀ t : ℝ,
      0 < t → t < _root_.Min.min a.length d → t ≤ b.length → a.point t = b.point t →
      ∀ s ∈ _root_.Set.Ioc 0 t, a.point s = b.point s := by
  obtain ⟨d, hd, hregular⟩ := finiteHorn_endRay_smooth_geodesic g H
  refine ⟨d, hd, ?_⟩
  intro a b t ht htd htb hcontact
  have hta : t < a.length := htd.trans_le (min_le_left _ _)
  let c : EndRay H.endpoint := spliceEndRay a b ⟨ht, hta.le⟩ htb hcontact
  obtain ⟨haSmooth, haGeo⟩ := hregular a
  obtain ⟨hcSmooth, hcGeo⟩ := hregular c
  let L : ℝ := _root_.Min.min a.length d
  let q : ℝ := (t + L) / 2
  have htq : t < q := by dsimp only [q]; linarith
  have hqL : q < L := by dsimp only [q]; linarith
  have hq : q ∈ _root_.Set.Ioo 0 L := ⟨ht.trans htq, hqL⟩
  have hgerm : c.point =ᶠ[𝓝 q] a.point := by
    filter_upwards [isOpen_Ioi.mem_nhds htq] with s hs
    change (if s ≤ t then b.point s else a.point s) = a.point s
    exact if_neg (not_le_of_gt hs)
  have heq : _root_.Set.EqOn c.point a.point (_root_.Set.Ioo 0 L) :=
    geodesics_eqOn_of_common_germ g hq hcGeo haGeo hcSmooth.continuousOn haSmooth.continuousOn hgerm
  intro s hs
  have hsL : s ∈ _root_.Set.Ioo 0 L := ⟨hs.1, hs.2.trans_lt htd⟩
  have h := heq hsL
  change (if s ≤ t then b.point s else a.point s) = a.point s at h
  simpa only [if_pos hs.2] using h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_endRay_unique_inward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_endRay_unique_inward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_endRay_unique_inward ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_endRay_unique_inward

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
