import Submission.DifferentialGeometry.Geometry.Metric.ChartLipschitz
import Submission.DifferentialGeometry.Geometry.Comparison.Distance.Continuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Filter _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.NNReal

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContinuousRiemannianBundle F (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M]

open _root_.ContMDiffWithinAt in
theorem ContMDiffWithinAt.exists_lipschitzOnWith {f : E → M} {s : Set E} {x : E}
    (hf : ContMDiffWithinAt 𝓘(ℝ, E) I 1 f s x) (hs : Convex ℝ s) :
    ∃ K : ℝ≥0, ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t := by
  obtain ⟨C, _, R, hR, hchart⟩ :=
    DifferentialGeometry.Geometry.Riemannian.chart_symm_edist_le (I := I) (f x)
  let g := extChartAt I (f x) ∘ f
  have hg : ContDiffWithinAt ℝ 1 g s x := by
    apply ContMDiffWithinAt.contDiffWithinAt
    exact (contMDiffAt_extChartAt (I := I) (x := f x) (n := 1)).comp_contMDiffWithinAt x hf
  obtain ⟨K, v, hv, hKv⟩ := hg.exists_lipschitzOnWith hs
  have hsrc : f ⁻¹' (extChartAt I (f x)).source ∈ 𝓝[s] x :=
    hf.continuousWithinAt.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds (f x))
  have hball : g ⁻¹' Metric.ball (extChartAt I (f x) (f x)) R ∈ 𝓝[s] x :=
    hg.continuousWithinAt.preimage_mem_nhdsWithin (Metric.ball_mem_nhds _ hR)
  let t := v ∩ f ⁻¹' (extChartAt I (f x)).source ∩
    g ⁻¹' Metric.ball (extChartAt I (f x) (f x)) R
  have ht : t ∈ 𝓝[s] x := _root_.Filter.inter_mem (_root_.Filter.inter_mem hv hsrc) hball
  refine ⟨C * K, t, ht, ?_⟩
  intro y hy z hz
  rcases hy with ⟨⟨hyv, hysrc⟩, hyball⟩
  rcases hz with ⟨⟨hzv, hzsrc⟩, hzball⟩
  have hyRange : g y ∈ _root_.Set.range I :=
    extChartAt_target_subset_range (f x) ((extChartAt I (f x)).map_source hysrc)
  have hzRange : g z ∈ _root_.Set.range I :=
    extChartAt_target_subset_range (f x) ((extChartAt I (f x)).map_source hzsrc)
  have hyInv : (extChartAt I (f x)).symm (g y) = f y :=
    (extChartAt I (f x)).left_inv hysrc
  have hzInv : (extChartAt I (f x)).symm (g z) = f z :=
    (extChartAt I (f x)).left_inv hzsrc
  rw [IsRiemannianManifold.out (I := I), ← hyInv, ← hzInv]
  refine (hchart (g y) ⟨hyball, hyRange⟩ (g z) ⟨hzball, hzRange⟩).trans ?_
  calc
    (C : ENNReal) * _root_.EDist.edist (g y) (g z) ≤ C * (K * _root_.EDist.edist y z) :=
      mul_right_mono (hKv hyv hzv)
    _ = (C * K) * _root_.EDist.edist y z := by simp only [mul_assoc]

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiffWithinAt
  let env ← Lean.getEnv
  if env.contains `ContMDiffWithinAt.exists_lipschitzOnWith then
    throwError "Refusing to shadow existing declaration ContMDiffWithinAt.exists_lipschitzOnWith"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffWithinAt.exists_lipschitzOnWith ``Submission.ContMDiffWithinAt.exists_lipschitzOnWith

open _root_.ContMDiffOn in
theorem ContMDiffOn.locallyLipschitzOn {f : E → M} {s : Set E}
    (hf : ContMDiffOn 𝓘(ℝ, E) I 1 f s) (hs : Convex ℝ s) :
    LocallyLipschitzOn s f := fun x hx => (hf x hx).exists_lipschitzOnWith hs

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiffOn
  let env ← Lean.getEnv
  if env.contains `ContMDiffOn.locallyLipschitzOn then
    throwError "Refusing to shadow existing declaration ContMDiffOn.locallyLipschitzOn"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffOn.locallyLipschitzOn ``Submission.ContMDiffOn.locallyLipschitzOn


theorem DifferentialGeometry.Geometry.Riemannian.locallyLipschitzOn_extChartAt_symm (a : M) :
    LocallyLipschitzOn (extChartAt I a).target (extChartAt I a).symm := by
  intro x hx
  obtain ⟨K, V, hV, hK⟩ :=
    (contMDiffWithinAt_extChartAt_symm_range (n := 1) a hx).exists_lipschitzOnWith I.convex_range
  exact ⟨K, V, nhdsWithin_mono x (extChartAt_target_subset_range a) hV, hK⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.locallyLipschitzOn_extChartAt_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.locallyLipschitzOn_extChartAt_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.locallyLipschitzOn_extChartAt_symm ``Submission.DifferentialGeometry.Geometry.Riemannian.locallyLipschitzOn_extChartAt_symm

end

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {M N : Type*} [PseudoEMetricSpace M] [PseudoEMetricSpace N]
  [ChartedSpace H M] [ChartedSpace H' N] [IsManifold I 1 M] [IsManifold J 1 N]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [RiemannianBundle (fun x : N => TangentSpace J x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [IsContinuousRiemannianBundle F (fun x : N => TangentSpace J x)]
  [IsRiemannianManifold I M] [IsRiemannianManifold J N]

open _root_.ContMDiffAt in
theorem ContMDiffAt.exists_lipschitzOnWith {f : M → N} {x : M}
    (hf : ContMDiffAt I J 1 f x) :
    ∃ K : ℝ≥0, ∃ s ∈ 𝓝 x, LipschitzOnWith K f s := by
  obtain ⟨K, s, hs, hKs⟩ :=
    DifferentialGeometry.Geometry.Riemannian.exists_lipschitzOnWith_extChartAt (I := I) x
  have hcomp : ContMDiffWithinAt 𝓘(ℝ, E) J 1 (f ∘ (extChartAt I x).symm)
      (_root_.Set.range I) (extChartAt I x x) :=
    hf.comp_contMDiffWithinAt_of_eq (contMDiffWithinAt_extChartAt_symm_range_self x)
      ((extChartAt I x).left_inv (mem_extChartAt_source x))
  obtain ⟨L, t, ht, hLt⟩ := hcomp.exists_lipschitzOnWith I.convex_range
  have htpre : (extChartAt I x) ⁻¹' t ∈ 𝓝 x :=
    extChartAt_preimage_mem_nhds_of_mem_nhdsWithin (mem_extChartAt_source x) ht
  let u := s ∩ (extChartAt I x) ⁻¹' t ∩ (extChartAt I x).source
  have hu : u ∈ 𝓝 x := _root_.Filter.inter_mem (_root_.Filter.inter_mem hs htpre) (extChartAt_source_mem_nhds x)
  refine ⟨L * K, u, hu, ?_⟩
  intro y hy z hz
  rcases hy with ⟨⟨hys, hyt⟩, hysrc⟩
  rcases hz with ⟨⟨hzs, hzt⟩, hzsrc⟩
  have hcoord : _root_.EDist.edist (f y) (f z) ≤ L * _root_.EDist.edist (extChartAt I x y) (extChartAt I x z) := by
    simpa only [Function.comp_apply, (extChartAt I x).left_inv hysrc,
      (extChartAt I x).left_inv hzsrc] using hLt hyt hzt
  refine hcoord.trans ?_
  calc
    (L : ENNReal) * _root_.EDist.edist (extChartAt I x y) (extChartAt I x z) ≤
        L * (K * _root_.EDist.edist y z) := mul_right_mono (hKs hys hzs)
    _ = (L * K) * _root_.EDist.edist y z := by simp only [mul_assoc]

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiffAt
  let env ← Lean.getEnv
  if env.contains `ContMDiffAt.exists_lipschitzOnWith then
    throwError "Refusing to shadow existing declaration ContMDiffAt.exists_lipschitzOnWith"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffAt.exists_lipschitzOnWith ``Submission.ContMDiffAt.exists_lipschitzOnWith

open _root_.ContMDiff in
theorem ContMDiff.locallyLipschitz {f : M → N} (hf : ContMDiff I J 1 f) :
    LocallyLipschitz f := fun _ => hf.contMDiffAt.exists_lipschitzOnWith

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiff
  let env ← Lean.getEnv
  if env.contains `ContMDiff.locallyLipschitz then
    throwError "Refusing to shadow existing declaration ContMDiff.locallyLipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiff.locallyLipschitz ``Submission.ContMDiff.locallyLipschitz

end

namespace DifferentialGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

open _root_.MeasureTheory in
theorem riemannianEDist_le_of_mfderivWithin_le
    {ψ : F → M} {s U : Set F} {L : ℝ}
    (hψ : ContMDiffOn 𝓘(ℝ, F) I 1 ψ s)
    (hU : U ⊆ s)
    (hspd : ∀ w ∈ U, ∀ v : F,
      ‖mfderivWithin 𝓘(ℝ, F) I ψ s w v‖ₑ ≤ ENNReal.ofReal (L * ‖v‖))
    {u v : F} (hseg : segment ℝ u v ⊆ U) :
    riemannianEDist I (ψ u) (ψ v) ≤ ENNReal.ofReal (L * _root_.Dist.dist u v) := by
  let η := ContinuousAffineMap.lineMap (R := ℝ) u v
  let γ : ℝ → M := ψ ∘ η
  have hηU : _root_.Set.MapsTo η (_root_.Set.Icc (0 : ℝ) 1) U := by
    intro t ht
    apply hseg
    rw [segment_eq_image_lineMap]
    exact ⟨t, ht, rfl⟩
  have hηs : _root_.Set.MapsTo η (_root_.Set.Icc (0 : ℝ) 1) s := fun _ ht => hU (hηU ht)
  have hηsmooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 η (_root_.Set.Icc (0 : ℝ) 1) := by
    rw [contMDiffOn_iff_contDiffOn]
    exact η.contDiff.contDiffOn
  have hγsmooth := hψ.comp hηsmooth hηs
  have hpoint : ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1,
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (_root_.Set.Icc 0 1) t 1‖ₑ ≤
        ENNReal.ofReal (L * _root_.Dist.dist u v) := by
    intro t ht
    have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (_root_.Set.Icc (0 : ℝ) 1) t := by
      rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
    have hηdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) η t := by
      rw [mdifferentiableAt_iff_differentiableAt]
      exact η.differentiableAt
    have hchain := mfderivWithin_comp t (hψ.mdifferentiableOn one_ne_zero _ (hηs ht))
      hηdiff.mdifferentiableWithinAt hηs hu
    have hηderiv : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, F) η (_root_.Set.Icc 0 1) t 1 = v - u := by
      rw [mfderivWithin_eq_mfderiv hu hηdiff, mfderiv_eq_fderiv, η.fderiv]
      change ((AffineMap.lineMap u v).linear : ℝ →ₗ[ℝ] F) 1 = v - u
      rw [AffineMap.lineMap_linear]
      simp
    change ‖(mfderivWithin 𝓘(ℝ, ℝ) I (ψ ∘ η) (_root_.Set.Icc 0 1) t) 1‖ₑ ≤ _
    rw [hchain, ContinuousLinearMap.comp_apply, hηderiv]
    simpa only [dist_eq_norm, norm_sub_rev] using hspd (η t) (hηU ht) (v - u)
  calc
    riemannianEDist I (ψ u) (ψ v) ≤ _root_.Manifold.pathELength I γ 0 1 :=
      _root_.Manifold.riemannianEDist_le_pathELength hγsmooth
        (by simp [γ, η, ContinuousAffineMap.coe_lineMap_eq])
        (by simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]) zero_le_one
    _ = ∫⁻ t in _root_.Set.Icc (0 : ℝ) 1, ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (_root_.Set.Icc 0 1) t 1‖ₑ :=
      _root_.Manifold.pathELength_eq_lintegral_mfderivWithin_Icc
    _ ≤ ∫⁻ _ in _root_.Set.Icc (0 : ℝ) 1, ENNReal.ofReal (L * _root_.Dist.dist u v) :=
      _root_.MeasureTheory.setLIntegral_mono' measurableSet_Icc hpoint
    _ = ENNReal.ofReal (L * _root_.Dist.dist u v) := by
      rw [_root_.MeasureTheory.setLIntegral_const, Real.volume_Icc]
      norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemannianEDist_le_of_mfderivWithin_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemannianEDist_le_of_mfderivWithin_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemannianEDist_le_of_mfderivWithin_le ``Submission.DifferentialGeometry.riemannianEDist_le_of_mfderivWithin_le

end DifferentialGeometry
