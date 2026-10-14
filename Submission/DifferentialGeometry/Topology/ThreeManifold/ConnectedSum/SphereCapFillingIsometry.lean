import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SphereCapFillingSmooth

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.InnerProductSpace
open _root_.Function _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Topology.SphereUnitFilling

noncomputable def modelLinearIsometryPartialDiffeomorph (A : E3 ≃ₗᵢ[ℝ] E3) :
    PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ where
  toFun := fun u => A u
  invFun := fun u => A.symm u
  source := Set.univ
  target := Set.univ
  map_source' := fun _ _ => Set.mem_univ _
  map_target' := fun _ _ => Set.mem_univ _
  left_inv' := fun u _ => A.symm_apply_apply u
  right_inv' := fun u _ => A.apply_symm_apply u
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := (A.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff).contMDiffOn
  contMDiffOn_invFun :=
    (A.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff).contMDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.modelLinearIsometryPartialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.modelLinearIsometryPartialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.modelLinearIsometryPartialDiffeomorph ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.modelLinearIsometryPartialDiffeomorph

@[simp]
lemma modelLinearIsometryPartialDiffeomorph_apply (A : E3 ≃ₗᵢ[ℝ] E3) (u : E3) :
    modelLinearIsometryPartialDiffeomorph A u = A u := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.modelLinearIsometryPartialDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.modelLinearIsometryPartialDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.modelLinearIsometryPartialDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.modelLinearIsometryPartialDiffeomorph_apply

lemma modelLinearIsometryPartialDiffeomorph_source (A : E3 ≃ₗᵢ[ℝ] E3) :
    (modelLinearIsometryPartialDiffeomorph A).source = Set.univ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.modelLinearIsometryPartialDiffeomorph_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.modelLinearIsometryPartialDiffeomorph_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.modelLinearIsometryPartialDiffeomorph_source ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.modelLinearIsometryPartialDiffeomorph_source

noncomputable def sphereChartPartialIso (A : E3 ≃ₗᵢ[ℝ] E3) (P : S3) :
    PartialDiffeomorph 𝓘(ℝ, E3) (𝓡 3) E3 S3 ∞ :=
  (modelLinearIsometryPartialDiffeomorph A).trans (sphereChartPartial P)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.sphereChartPartialIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.sphereChartPartialIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.sphereChartPartialIso ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.sphereChartPartialIso

lemma sphereChartPartialIso_apply (A : E3 ≃ₗᵢ[ℝ] E3) (P : S3) (u : E3) :
    sphereChartPartialIso A P u = (stereographic' 3 P).symm (-((2 : ℝ) • (A u))) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.sphereChartPartialIso_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.sphereChartPartialIso_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.sphereChartPartialIso_apply ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.sphereChartPartialIso_apply

lemma sphereChartPartialIso_source (A : E3 ≃ₗᵢ[ℝ] E3) (P : S3) :
    (sphereChartPartialIso A P).source = Set.univ := by
  change ((modelLinearIsometryPartialDiffeomorph A).toOpenPartialHomeomorph.trans
    (sphereChartPartial P).toOpenPartialHomeomorph).source = Set.univ
  rw [OpenPartialHomeomorph.trans_source]
  have h1 : (modelLinearIsometryPartialDiffeomorph A).toOpenPartialHomeomorph.source = Set.univ :=
    rfl
  have h2 : (sphereChartPartial P).toOpenPartialHomeomorph.source = Set.univ := rfl
  rw [h1, h2, Set.preimage_univ, Set.inter_univ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.sphereChartPartialIso_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.sphereChartPartialIso_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.sphereChartPartialIso_source ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.sphereChartPartialIso_source

noncomputable def sphereBallChartIso (A : E3 ≃ₗᵢ[ℝ] E3) (P : S3) :
    BallChart 3 (𝓡 3) S3 where
  chart := sphereChartPartialIso A P
  closedBall_subset_source := fun x _ => by
    rw [sphereChartPartialIso_source]
    exact Set.mem_univ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.sphereBallChartIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.sphereBallChartIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.sphereBallChartIso ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.sphereBallChartIso

end DifferentialGeometry.Topology.SphereUnitFilling

namespace DifferentialGeometry.Topology.SphereUnitFilling

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M]

noncomputable def capPointIso (A : E3 ≃ₗᵢ[ℝ] E3) (P : S3)
    (x : (sphereBallChart P).Punctured) : Metric.closedBall (0 : E3) 2 :=
  ⟨A.symm ((capPoint P x : E3)), by
    have h := (capPoint P x).2
    rw [Metric.mem_closedBall, dist_zero_right] at h ⊢
    rwa [A.symm.norm_map]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capPointIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capPointIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capPointIso ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capPointIso

lemma capPointIso_apply (A : E3 ≃ₗᵢ[ℝ] E3) (P : S3)
    (x : (sphereBallChart P).Punctured) :
    (capPointIso A P x : E3) = A.symm ((capPoint P x : E3)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capPointIso_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capPointIso_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capPointIso_apply ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capPointIso_apply

noncomputable def capFillMapIso (A : E3 ≃ₗᵢ[ℝ] E3) (P : S3) (c : BallChart 3 (𝓡 3) M) :
    (sphereBallChart P).Punctured →
      {x : M // x ∈ c.chart '' Metric.closedBall (0 : E3) 1} :=
  fun x => ⟨c.chart (capRadialMap (capPointIso A P x)),
    ⟨capRadialMap (capPointIso A P x), by
      rw [← capRadialMap_image_closedBall]
      exact ⟨_, (capPointIso A P x).2, rfl⟩, rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capFillMapIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capFillMapIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capFillMapIso ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capFillMapIso

omit [T2Space M] in
lemma capFillMapIso_val (A : E3 ≃ₗᵢ[ℝ] E3) (P : S3) (c : BallChart 3 (𝓡 3) M)
    (x : (sphereBallChart P).Punctured) :
    (capFillMapIso A P c x : M) = c.chart (capRadialMap (capPointIso A P x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capFillMapIso_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capFillMapIso_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capFillMapIso_val ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capFillMapIso_val

omit [T2Space M] in
lemma capFillMapIso_mem (A : E3 ≃ₗᵢ[ℝ] E3) (P : S3) (c : BallChart 3 (𝓡 3) M)
    (x : (sphereBallChart P).Punctured) :
    capRadialMap (capPointIso A P x) ∈ c.chart.source :=
  c.closedBall_one_subset_source (by
    rw [← capRadialMap_image_closedBall]
    exact ⟨_, (capPointIso A P x).2, rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capFillMapIso_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capFillMapIso_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capFillMapIso_mem ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capFillMapIso_mem

omit [T2Space M] in
lemma continuous_capFillMapIso (A : E3 ≃ₗᵢ[ℝ] E3) (P : S3)
    (c : BallChart 3 (𝓡 3) M) : Continuous (capFillMapIso A P c) := by
  refine Continuous.subtype_mk ?_ _
  have hcont : Continuous fun x : (sphereBallChart P).Punctured =>
      capRadialMap (capPointIso A P x) :=
    contDiff_capRadialMap.continuous.comp
      ((A.symm.toContinuousLinearEquiv.toContinuousLinearMap.continuous).comp
        (continuous_subtype_val.comp (continuous_capPoint P)))
  exact c.chart.contMDiffOn_toFun.continuousOn.comp_continuous hcont (capFillMapIso_mem A P c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.continuous_capFillMapIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.continuous_capFillMapIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.continuous_capFillMapIso ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.continuous_capFillMapIso

omit [T2Space M] in
lemma capFillMapIso_injective (A : E3 ≃ₗᵢ[ℝ] E3) (P : S3)
    (c : BallChart 3 (𝓡 3) M) : Function.Injective (capFillMapIso A P c) := by
  intro x y hxy
  have h1 : capRadialMap (capPointIso A P x) = capRadialMap (capPointIso A P y) :=
    c.chart.toPartialEquiv.injOn (capFillMapIso_mem A P c x) (capFillMapIso_mem A P c y)
      (congrArg Subtype.val hxy)
  have h2 := capRadialMap_injOn (capPointIso A P x).2 (capPointIso A P y).2 h1
  have h3 : A.symm ((capPoint P x : E3)) = A.symm ((capPoint P y : E3)) := by
    simpa only [capPointIso_apply] using h2
  have h4 : (capPoint P x : E3) = (capPoint P y : E3) := A.symm.injective h3
  have h5 : (stereographic' 3 P) (-(x : S3)) = (stereographic' 3 P) (-(y : S3)) := by
    rw [capPoint_apply, capPoint_apply] at h4
    exact h4
  have h6 : (-(x : S3) : S3) = -(y : S3) := by
    rw [← (stereographic' 3 P).left_inv
        (mem_source_stereographic P (neg_mem_compl_of_mem_punctured P x)),
      ← (stereographic' 3 P).left_inv
        (mem_source_stereographic P (neg_mem_compl_of_mem_punctured P y)), h5]
  exact Subtype.ext (neg_injective h6)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capFillMapIso_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capFillMapIso_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capFillMapIso_injective ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capFillMapIso_injective

omit [T2Space M] in
lemma capFillMapIso_surjective (A : E3 ≃ₗᵢ[ℝ] E3) (P : S3)
    (c : BallChart 3 (𝓡 3) M) : Function.Surjective (capFillMapIso A P c) := by
  rintro ⟨y, w, hw, rfl⟩
  have hw1 : ‖w‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hw
  have hwmem : w ∈ Metric.closedBall (0 : E3) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hw1
  obtain ⟨v, hv, hvw⟩ := capRadialMap_surjOn hwmem
  have hvA : (A v : E3) ∈ Metric.closedBall (0 : E3) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right, A.norm_map]
    simpa only [Metric.mem_closedBall, dist_zero_right] using hv
  obtain ⟨x, hx⟩ := capPoint_surjective P ⟨A v, hvA⟩
  have hpoint : capRadialMap (capPointIso A P x) = w := by
    have hx' : (capPointIso A P x : E3) = v := by
      rw [capPointIso_apply,
        congrArg (fun z : Metric.closedBall (0 : E3) 2 => (z : E3)) hx]
      exact A.symm_apply_apply v
    rw [hx', hvw]
  refine ⟨x, Subtype.ext ?_⟩
  change c.chart (capRadialMap (capPointIso A P x)) = c.chart w
  rw [hpoint]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capFillMapIso_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capFillMapIso_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capFillMapIso_surjective ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capFillMapIso_surjective

omit [T2Space M] in
noncomputable def capFillIso (A : E3 ≃ₗᵢ[ℝ] E3) (P : S3) (c : BallChart 3 (𝓡 3) M) :
    (sphereBallChart P).Punctured ≃ₜ
      {x : M // x ∈ c.chart '' Metric.closedBall (0 : E3) 1} :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (capFillMapIso A P c)
      ⟨capFillMapIso_injective A P c, capFillMapIso_surjective A P c⟩)
    (continuous_capFillMapIso A P c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capFillIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capFillIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capFillIso ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capFillIso

@[simp]
lemma capFillIso_apply (A : E3 ≃ₗᵢ[ℝ] E3) (P : S3) (c : BallChart 3 (𝓡 3) M)
    (x : (sphereBallChart P).Punctured) :
    capFillIso A P c x = capFillMapIso A P c x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capFillIso_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capFillIso_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capFillIso_apply ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capFillIso_apply

end DifferentialGeometry.Topology.SphereUnitFilling

namespace DifferentialGeometry.Topology.SphereUnitFilling

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M]

omit [T2Space M] in
lemma capRadialMap_capPointIso_boundary (A : E3 ≃ₗᵢ[ℝ] E3) (P : S3)
    (w : Metric.sphere (0 : E3) 1) :
    capRadialMap (capPointIso A P ((sphereBallChart P).boundaryMap (sphereAnti w))) =
      A.symm (w : E3) := by
  have hneg : ((sphereAnti w : Metric.sphere (0 : E3) 1) : E3) = -(w : E3) := by
    rw [sphereAnti_eq_neg]
    rfl
  have hcp : (capPointIso A P
      ((sphereBallChart P).boundaryMap (sphereAnti w)) : E3) =
        A.symm ((2 : ℝ) • (-(w : E3))) := by
    rw [capPointIso_apply, capPoint_boundary, hneg]
  rw [hcp]
  have hlin : A.symm ((2 : ℝ) • (-(w : E3))) = (2 : ℝ) • (-(A.symm (w : E3))) := by
    rw [map_smul, map_neg]
  rw [hlin]
  have hz : ‖-(A.symm (w : E3))‖ = 1 := by
    rw [norm_neg, A.symm.norm_map]
    simpa only [Metric.mem_sphere, dist_zero_right] using w.2
  rw [capRadialMap_two_smul hz, neg_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capRadialMap_capPointIso_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capRadialMap_capPointIso_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capRadialMap_capPointIso_boundary ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capRadialMap_capPointIso_boundary

omit [T2Space M] in
lemma capRadialMap_capPointIso_radialMap (A : E3 ≃ₗᵢ[ℝ] E3) (P : S3)
    (w : Metric.sphere (0 : E3) 1) {ρ : ℝ} (h1 : 1 ≤ ρ)
    (hρ : ρ ∈ Set.Icc (1 : ℝ) 2) (h2 : ρ ≤ 3 / 2) :
    capRadialMap (capPointIso A P ((sphereBallChart P).radialMap (sphereAnti w) ρ hρ)) =
      (2 - ρ) • (A.symm (w : E3)) := by
  have hρpos : (0 : ℝ) < ρ := by linarith
  have hcp : (capPointIso A P
      ((sphereBallChart P).radialMap (sphereAnti w) ρ hρ) : E3) =
      A.symm ((2 / ρ) • ((sphereAnti w : Metric.sphere (0 : E3) 1) : E3)) := by
    rw [capPointIso_apply, capPoint_radial P (sphereAnti w) h1 hρ]
  rw [hcp]
  have hneg : ((sphereAnti w : Metric.sphere (0 : E3) 1) : E3) = -(w : E3) := by
    rw [sphereAnti_eq_neg]
    rfl
  rw [hneg]
  have hz : ‖-(A.symm (w : E3))‖ = 1 := by
    rw [norm_neg, A.symm.norm_map]
    simpa only [Metric.mem_sphere, dist_zero_right] using w.2
  have hlin : A.symm ((2 / ρ) • (-(w : E3))) = (2 / ρ) • (-(A.symm (w : E3))) := by
    rw [map_smul, map_neg]
  rw [hlin, capRadialMap_two_div_smul hz h1, capRadius_of_le h1 h2]
  module

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capRadialMap_capPointIso_radialMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capRadialMap_capPointIso_radialMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capRadialMap_capPointIso_radialMap ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capRadialMap_capPointIso_radialMap

theorem capFillIso_boundary (A : E3 ≃ₗᵢ[ℝ] E3) (P : S3)
    (c : BallChart 3 (𝓡 3) M) (w : Metric.sphere (0 : E3) 1) :
    capFillIso A P c ((sphereBallChart P).boundaryMap (sphereAnti w)) =
      ⟨c.chart (A.symm (w : E3)),
        ⟨A.symm (w : E3), by
          rw [Metric.mem_closedBall, dist_zero_right, A.symm.norm_map]
          exact le_of_eq (by
            simpa only [Metric.mem_sphere, dist_zero_right] using w.2), rfl⟩⟩ := by
  refine Subtype.ext ?_
  rw [capFillIso_apply, capFillMapIso_val, capRadialMap_capPointIso_boundary]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capFillIso_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capFillIso_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capFillIso_boundary ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capFillIso_boundary

theorem capFillIso_radialRightClamp (A : E3 ≃ₗᵢ[ℝ] E3) (P : S3)
    (c : BallChart 3 (𝓡 3) M) (w : Metric.sphere (0 : E3) 1)
    (p : ConnectedSumQuotient.CollarDomain) (hp : (p.2 : ℝ) < 0) :
    capFillIso A P c (ConnectedSumQuotient.radialRightClamp (sphereBallChart P) (sphereAnti w) p) =
      ⟨c.chart ((1 + (p.2 : ℝ)) • (A.symm (w : E3))),
        ⟨(1 + (p.2 : ℝ)) • (A.symm (w : E3)), by
          rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs]
          have hw1 : ‖(A.symm (w : E3))‖ = 1 := by
            rw [A.symm.norm_map]
            simpa only [Metric.mem_sphere, dist_zero_right] using w.2
          rw [hw1, mul_one, abs_of_nonneg (by linarith [p.2.2.1])]
          linarith [p.2.2.2], rfl⟩⟩ := by
  have ht1 : (p.2 : ℝ) < 1 / 2 := p.2.2.2
  have ht2 : -(1 / 2 : ℝ) < (p.2 : ℝ) := p.2.2.1
  have h1 : (1 : ℝ) ≤ 1 - (p.2 : ℝ) := by linarith
  have h2 : 1 - (p.2 : ℝ) ≤ 3 / 2 := by linarith
  have hρ : 1 - (p.2 : ℝ) ∈ Set.Icc (1 : ℝ) 2 := ⟨h1, by linarith⟩
  have hρ' : (2 - (1 - (p.2 : ℝ))) = 1 + (p.2 : ℝ) := by ring
  refine Subtype.ext ?_
  rw [capFillIso_apply, capFillMapIso_val,
    ConnectedSumQuotient.radialRightClamp_of_neg (sphereBallChart P) (sphereAnti w) p hp,
    capRadialMap_capPointIso_radialMap A P w h1 hρ h2, hρ']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capFillIso_radialRightClamp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capFillIso_radialRightClamp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capFillIso_radialRightClamp ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capFillIso_radialRightClamp

end DifferentialGeometry.Topology.SphereUnitFilling

namespace DifferentialGeometry.Topology.SphereUnitFilling

universe u

variable {M : ConnectedClosedOrientedManifold.{u} 3}

theorem isLocalDiffeomorphAt_sphereFillIso (A : E3 ≃ₗᵢ[ℝ] E3) (P : S3)
    (c : BallChart 3 (𝓡 3) M.Carrier) (y : S3) (hy : y ∈ (sphereBallChart P).interior) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (fun y : S3 => c.chart (capRadialMap (A.symm (stereographic' 3 P (-(y)))))) y := by
  have hneg1 : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (fun x : S3 => -(x)) y :=
    (Manifold.sphereAntipodalDiffeomorph (n := 3) (E := E4)).isLocalDiffeomorph y
  have hstereo : IsLocalDiffeomorphAt (𝓡 3) 𝓘(ℝ, E3) ∞
      (fun z : S3 => stereographic' 3 P z) (-(y)) :=
    isLocalDiffeomorphAt_stereographic P (neg_ne_pole_of_mem_interior hy)
  have hA : IsLocalDiffeomorphAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) ∞ (fun v : E3 => A.symm v)
      (stereographic' 3 P (-(y))) :=
    PartialDiffeomorph.isLocalDiffeomorphAt (𝓘(ℝ, E3)) (𝓘(ℝ, E3)) ∞
      (modelLinearIsometryPartialDiffeomorph A.symm) (Set.mem_univ _)
  have hstereoInv : IsLocalDiffeomorphAt 𝓘(ℝ, E3) (𝓡 3) ∞
      (fun u : E3 => (stereographic' 3 P).symm u)
      (A.symm (stereographic' 3 P (-(y)))) :=
    stereographicInverse_isLocalDiffeomorph P _
  have hneg2 : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (fun x : S3 => -(x))
      ((stereographic' 3 P).symm (A.symm (stereographic' 3 P (-(y))))) :=
    (Manifold.sphereAntipodalDiffeomorph (n := 3) (E := E4)).isLocalDiffeomorph _
  have hbig : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (fun y : S3 => -((stereographic' 3 P).symm (A.symm (stereographic' 3 P (-(y)))))) y :=
    (((hneg1.comp (K := 𝓘(ℝ, E3)) (P := E3) hstereo).comp
      (K := 𝓘(ℝ, E3)) (P := E3) hA).comp
      (K := 𝓡 3) (P := S3) hstereoInv).comp (K := 𝓡 3) (P := S3) hneg2
  have hmem : -((stereographic' 3 P).symm (A.symm (stereographic' 3 P (-(y))))) ∈
      (sphereBallChart P).interior := by
    rw [mem_interior_iff]
    have hv : ‖A.symm (stereographic' 3 P (-(y)))‖ < 2 := by
      rw [A.symm.norm_map]
      exact norm_stereographic_neg_lt_two hy
    have hcoe : ((-((stereographic' 3 P).symm (A.symm (stereographic' 3 P (-(y))))) : S3) : E4) =
        -(((stereographic' 3 P).symm (A.symm (stereographic' 3 P (-(y)))) : S3) : E4) := by
      simp
    rw [hcoe, inner_neg_left, inner_stereographic_symm_apply]
    have hnum : ‖A.symm (stereographic' 3 P (-(y)))‖ ^ 2 - 4 < 0 := by
      nlinarith [norm_nonneg (A.symm (stereographic' 3 P (-(y))))]
    have hden : (0 : ℝ) < ‖A.symm (stereographic' 3 P (-(y)))‖ ^ 2 + 4 := by
      nlinarith [sq_nonneg ‖A.symm (stereographic' 3 P (-(y)))‖]
    exact neg_pos.mpr (div_neg_of_neg_of_pos hnum hden)
  have hG : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (fun z : S3 => c.chart (capRadialMap (stereographic' 3 P (-(z)))))
      (-((stereographic' 3 P).symm (A.symm (stereographic' 3 P (-(y)))))) :=
    isLocalDiffeomorphAt_sphereFill P c _ hmem
  refine isLocalDiffeomorphAt_of_eventuallyEq
    (Filter.Eventually.of_forall fun z => ?_) (hbig.comp (K := 𝓡 3) (P := M.Carrier) hG)
  simp only [Function.comp_apply, neg_neg]
  rw [(stereographic' 3 P).right_inv (mem_target_stereographic P _)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.isLocalDiffeomorphAt_sphereFillIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.isLocalDiffeomorphAt_sphereFillIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.isLocalDiffeomorphAt_sphereFillIso ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.isLocalDiffeomorphAt_sphereFillIso

end DifferentialGeometry.Topology.SphereUnitFilling

namespace DifferentialGeometry.Topology

namespace ConnectedSumUnit

universe u

open _root_.Submission.DifferentialGeometry.Topology.SphereUnitFilling

variable {M : ConnectedClosedOrientedManifold.{u} 3}

theorem puncturedImage_ulift_iso (A : SphereUnitFilling.E3 ≃ₗᵢ[ℝ] SphereUnitFilling.E3)
    (P : SphereUnitFilling.S3)
    (d : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold)
    (hd : ∀ u : csE3, ULift.down (d.toBallChart.chart u)
      = (SphereUnitFilling.sphereBallChart P).chart (A u)) :
    uliftSphereHomeomorph '' (d.toBallChart.chart '' Metric.ball (0 : csE3) 1)
      = (SphereUnitFilling.sphereBallChart P).chart '' Metric.ball (0 : csE3) 1 := by
  ext y
  constructor
  · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨A v, ?_, (hd v).symm⟩
    simpa only [Metric.mem_ball, dist_zero_right, A.norm_map] using hv
  · rintro ⟨v, hv, rfl⟩
    refine ⟨ULift.up ((SphereUnitFilling.sphereBallChart P).chart v),
      ⟨A.symm v, ?_, ?_⟩, rfl⟩
    · simpa only [Metric.mem_ball, dist_zero_right, A.symm.norm_map] using hv
    · apply ULift.down_injective
      rw [hd (A.symm v), A.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.puncturedImage_ulift_iso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.puncturedImage_ulift_iso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.puncturedImage_ulift_iso ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.puncturedImage_ulift_iso

variable (A : SphereUnitFilling.E3 ≃ₗᵢ[ℝ] SphereUnitFilling.E3) (P : SphereUnitFilling.S3)
  (d : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold)
  (hd : ∀ u : csE3, ULift.down (d.toBallChart.chart u)
    = (SphereUnitFilling.sphereBallChart P).chart (A u))
  (c : OrientedBallChart M.toClosedOrientedManifold)

theorem puncturedHomeomorph_apply_val_iso (q : d.toBallChart.Punctured) :
    ((BallChart.puncturedHomeomorphOfImage d.toBallChart
        (SphereUnitFilling.sphereBallChart P) uliftSphereHomeomorph
        (puncturedImage_ulift_iso A P d hd) q
      : (SphereUnitFilling.sphereBallChart P).Punctured) : SphereUnitFilling.S3)
      = ULift.down q.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.puncturedHomeomorph_apply_val_iso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.puncturedHomeomorph_apply_val_iso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.puncturedHomeomorph_apply_val_iso ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.puncturedHomeomorph_apply_val_iso

noncomputable def unitFillingOfSphereChartIso :
    UnitFilling c d boundaryAttachment where
  fill := (BallChart.puncturedHomeomorphOfImage d.toBallChart
      (SphereUnitFilling.sphereBallChart P) uliftSphereHomeomorph
      (puncturedImage_ulift_iso A P d hd)).trans
        (SphereUnitFilling.capFillIso A P c.toBallChart)
  map_boundary := by
    intro z
    let w : Metric.sphere (0 : csE3) 1 := ⟨A (z : csE3), by
      rw [Metric.mem_sphere, dist_zero_right, A.norm_map]
      simpa only [Metric.mem_sphere, dist_zero_right] using z.2⟩
    have hneg_z : ((boundaryAttachment.1 z : csS2) : csE3) = -(z : csE3) := by
      have hb : (boundaryAttachment.1 z : csS2) = (SphereUnitFilling.sphereAnti z : csS2) := rfl
      rw [hb, SphereUnitFilling.sphereAnti_eq_neg]
      rfl
    have hneg_w : ((SphereUnitFilling.sphereAnti w : csS2) : csE3) = -(w : csE3) := by
      rw [SphereUnitFilling.sphereAnti_eq_neg]
      rfl
    have hwcoe : (w : csE3) = A (z : csE3) := rfl
    have hbd : (BallChart.puncturedHomeomorphOfImage d.toBallChart
          (SphereUnitFilling.sphereBallChart P) uliftSphereHomeomorph
          (puncturedImage_ulift_iso A P d hd))
          (d.toBallChart.boundaryMap (boundaryAttachment.1 z))
        = (SphereUnitFilling.sphereBallChart P).boundaryMap
          (SphereUnitFilling.sphereAnti w) := by
      refine Subtype.ext ?_
      have hL : (↑((BallChart.puncturedHomeomorphOfImage d.toBallChart
            (SphereUnitFilling.sphereBallChart P) uliftSphereHomeomorph
            (puncturedImage_ulift_iso A P d hd))
            (d.toBallChart.boundaryMap (boundaryAttachment.1 z))) : SphereUnitFilling.S3)
          = ULift.down (d.toBallChart.chart (boundaryAttachment.1 z : csE3)) := by
        rw [puncturedHomeomorph_apply_val_iso A P d hd, BallChart.boundaryMap_val]
      have hR : (↑((SphereUnitFilling.sphereBallChart P).boundaryMap
            (SphereUnitFilling.sphereAnti w)) : SphereUnitFilling.S3)
          = (SphereUnitFilling.sphereBallChart P).chart
              ((SphereUnitFilling.sphereAnti w : csS2) : csE3) := by
        rw [BallChart.boundaryMap_val]
      rw [hL, hR, hd (boundaryAttachment.1 z)]
      congr 1
      rw [hneg_z, hneg_w, map_neg, hwcoe]
    refine Subtype.ext ?_
    rw [Homeomorph.trans_apply, hbd]
    have hval : (SphereUnitFilling.capFillIso A P c.toBallChart
          ((SphereUnitFilling.sphereBallChart P).boundaryMap
            (SphereUnitFilling.sphereAnti w)) : M.Carrier)
        = c.toBallChart.chart (A.symm (w : SphereUnitFilling.E3)) :=
      congrArg Subtype.val
        (SphereUnitFilling.capFillIso_boundary A P c.toBallChart w)
    rw [hval]
    exact congrArg c.toBallChart.chart (A.symm_apply_apply (z : csE3))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.unitFillingOfSphereChartIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.unitFillingOfSphereChartIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.unitFillingOfSphereChartIso ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.unitFillingOfSphereChartIso

@[simp]
theorem unitFillingOfSphereChartIso_fill (q : d.toBallChart.Punctured) :
    (unitFillingOfSphereChartIso A P d hd c).fill q
      = (SphereUnitFilling.capFillIso A P c.toBallChart)
        ((BallChart.puncturedHomeomorphOfImage d.toBallChart
          (SphereUnitFilling.sphereBallChart P) uliftSphereHomeomorph
          (puncturedImage_ulift_iso A P d hd)) q) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.unitFillingOfSphereChartIso_fill then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.unitFillingOfSphereChartIso_fill"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.unitFillingOfSphereChartIso_fill ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.unitFillingOfSphereChartIso_fill

theorem ballComplementCollar_unitFillingOfSphereChartIso :
    BallComplementCollar (unitFillingOfSphereChartIso A P d hd c) := by
  intro p hp
  let w : Metric.sphere (0 : csE3) 1 := ⟨A (p.1 : csE3), by
    rw [Metric.mem_sphere, dist_zero_right, A.norm_map]
    simpa only [Metric.mem_sphere, dist_zero_right] using p.1.2⟩
  have hneg_p : ((boundaryAttachment.1 p.1 : csS2) : csE3) = -(p.1 : csE3) := by
    have hb : (boundaryAttachment.1 p.1 : csS2) = (SphereUnitFilling.sphereAnti p.1 : csS2) := rfl
    rw [hb, SphereUnitFilling.sphereAnti_eq_neg]
    rfl
  have hneg_w : ((SphereUnitFilling.sphereAnti w : csS2) : csE3) = -(w : csE3) := by
    rw [SphereUnitFilling.sphereAnti_eq_neg]
    rfl
  have hwcoe : (w : csE3) = A (p.1 : csE3) := rfl
  have hbd : (BallChart.puncturedHomeomorphOfImage d.toBallChart
        (SphereUnitFilling.sphereBallChart P) uliftSphereHomeomorph
        (puncturedImage_ulift_iso A P d hd))
        (ConnectedSumQuotient.radialRightClamp d.toBallChart
          (boundaryAttachment.1 p.1) p)
      = ConnectedSumQuotient.radialRightClamp
          (SphereUnitFilling.sphereBallChart P)
          (SphereUnitFilling.sphereAnti w) p := by
    refine Subtype.ext ?_
    have hL : (↑((BallChart.puncturedHomeomorphOfImage d.toBallChart
          (SphereUnitFilling.sphereBallChart P) uliftSphereHomeomorph
          (puncturedImage_ulift_iso A P d hd))
          (ConnectedSumQuotient.radialRightClamp d.toBallChart
            (boundaryAttachment.1 p.1) p)) : SphereUnitFilling.S3)
        = ULift.down (d.toBallChart.chart
            ((1 - (p.2 : ℝ)) • (boundaryAttachment.1 p.1 : csE3))) := by
      rw [puncturedHomeomorph_apply_val_iso A P d hd,
        ConnectedSumQuotient.radialRightClamp_of_neg d.toBallChart
          (boundaryAttachment.1 p.1) p hp]
      rfl
    have hR : (↑(ConnectedSumQuotient.radialRightClamp
          (SphereUnitFilling.sphereBallChart P)
          (SphereUnitFilling.sphereAnti w) p) : SphereUnitFilling.S3)
        = (SphereUnitFilling.sphereBallChart P).chart
            ((1 - (p.2 : ℝ)) • ((SphereUnitFilling.sphereAnti w : csS2) : csE3)) := by
      rw [ConnectedSumQuotient.radialRightClamp_of_neg
          (SphereUnitFilling.sphereBallChart P) (SphereUnitFilling.sphereAnti w) p hp]
      rfl
    rw [hL, hR, hd ((1 - (p.2 : ℝ)) • (boundaryAttachment.1 p.1 : csE3))]
    congr 1
    rw [map_smul, hneg_p, hneg_w, map_neg, hwcoe]
  rw [unitFillingOfSphereChartIso_fill A P d hd c, hbd]
  have hval : (SphereUnitFilling.capFillIso A P c.toBallChart
        (ConnectedSumQuotient.radialRightClamp (SphereUnitFilling.sphereBallChart P)
          (SphereUnitFilling.sphereAnti w) p) : M.Carrier)
      = c.toBallChart.chart ((1 + (p.2 : ℝ)) • (A.symm (w : SphereUnitFilling.E3))) :=
    congrArg Subtype.val
      (SphereUnitFilling.capFillIso_radialRightClamp A P c.toBallChart w p hp)
  rw [hval]
  exact congrArg c.toBallChart.chart
    (congrArg (fun v => (1 + (p.2 : ℝ)) • v) (A.symm_apply_apply (p.1 : csE3)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.ballComplementCollar_unitFillingOfSphereChartIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.ballComplementCollar_unitFillingOfSphereChartIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.ballComplementCollar_unitFillingOfSphereChartIso ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.ballComplementCollar_unitFillingOfSphereChartIso

lemma mem_interior_lift_iso
    (A : SphereUnitFilling.E3 ≃ₗᵢ[ℝ] SphereUnitFilling.E3) (P : SphereUnitFilling.S3)
    (d : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold)
    (hd : ∀ u : csE3, ULift.down (d.toBallChart.chart u)
      = (SphereUnitFilling.sphereBallChart P).chart (A u))
    (x : d.toBallChart.interior) :
    ULift.down (α := SphereUnitFilling.S3) x.1 ∈
      (SphereUnitFilling.sphereBallChart P).interior := by
  have himg : ∀ y : ULift.{u} SphereUnitFilling.S3,
      (y ∈ d.toBallChart.chart '' Metric.closedBall (0 : csE3) 1)
        ↔ (ULift.down y ∈ (SphereUnitFilling.sphereBallChart P).chart ''
            Metric.closedBall (0 : csE3) 1) := by
    intro y
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨A u, ?_, (hd u).symm⟩
      rw [Metric.mem_closedBall, dist_zero_right] at hu ⊢
      rwa [A.norm_map]
    · rintro ⟨u, hu, hu'⟩
      refine ⟨A.symm u, ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right] at hu ⊢
        rwa [A.symm.norm_map]
      · apply ULift.down_injective
        rw [hd (A.symm u), A.apply_symm_apply]
        exact hu'
  have hnot : x.1 ∉ d.toBallChart.chart '' Metric.closedBall (0 : csE3) 1 := by
    have hx := x.2
    rw [BallChart.mem_interior] at hx
    exact hx
  refine (SphereUnitFilling.mem_interior_iff P _).mpr ?_
  have h1 : ULift.down (α := SphereUnitFilling.S3) x.1 ∉
      (SphereUnitFilling.sphereBallChart P).chart '' Metric.closedBall (0 : csE3) 1 :=
    fun h => hnot ((himg _).mpr h)
  rw [SphereUnitFilling.chart_image_closedBall] at h1
  have h2 : ¬ (⟪(ULift.down (α := SphereUnitFilling.S3) x.1 : SphereUnitFilling.E4),
      (P : SphereUnitFilling.E4)⟫_ℝ ≤ 0) :=
    fun h => h1 h
  exact not_le.mp h2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.mem_interior_lift_iso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.mem_interior_lift_iso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.mem_interior_lift_iso ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.mem_interior_lift_iso

theorem unitFillingOfSphereChartIso_fill_eq
    (A : SphereUnitFilling.E3 ≃ₗᵢ[ℝ] SphereUnitFilling.E3) (P : SphereUnitFilling.S3)
    (d : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold)
    (hd : ∀ u : csE3, ULift.down (d.toBallChart.chart u)
      = (SphereUnitFilling.sphereBallChart P).chart (A u))
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (x : d.toBallChart.interior) :
    ((unitFillingOfSphereChartIso A P d hd c).fill
        (d.toBallChart.interiorToPunctured x) : M.Carrier)
      = c.toBallChart.chart
        (SphereUnitFilling.capRadialMap
          (A.symm (stereographic' 3 P (-(ULift.down (α := SphereUnitFilling.S3) x.1))))) := by
  have hΦ : ((BallChart.puncturedHomeomorphOfImage d.toBallChart
        (SphereUnitFilling.sphereBallChart P) uliftSphereHomeomorph
        (puncturedImage_ulift_iso A P d hd)) (d.toBallChart.interiorToPunctured x)
      : SphereUnitFilling.S3) = ULift.down (α := SphereUnitFilling.S3) x.1 := by
    rw [puncturedHomeomorph_apply_val_iso A P d hd]
    rfl
  rw [unitFillingOfSphereChartIso_fill, SphereUnitFilling.capFillIso_apply,
    SphereUnitFilling.capFillMapIso_val, SphereUnitFilling.capPointIso_apply,
    SphereUnitFilling.capPoint_apply, hΦ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.unitFillingOfSphereChartIso_fill_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.unitFillingOfSphereChartIso_fill_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.unitFillingOfSphereChartIso_fill_eq ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.unitFillingOfSphereChartIso_fill_eq

theorem ballComplementSmooth_unitFillingOfSphereChartIso
    (A : SphereUnitFilling.E3 ≃ₗᵢ[ℝ] SphereUnitFilling.E3) (P : SphereUnitFilling.S3)
    (d : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold)
    (hd : ∀ u : csE3, ULift.down (d.toBallChart.chart u)
      = (SphereUnitFilling.sphereBallChart P).chart (A u))
    (c : OrientedBallChart M.toClosedOrientedManifold) :
    BallComplementSmooth (unitFillingOfSphereChartIso A P d hd c) := by
  intro x
  refine isLocalDiffeomorphAt_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => unitFillingOfSphereChartIso_fill_eq A P d hd c y) ?_
  have hsub : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (fun x : d.toBallChart.interior => x.1) x :=
    isLocalDiffeomorphAt_subtype_val d.toBallChart.interior x
  have hulift : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (fun y : standardThreeSphereLift.{u}.Carrier => ULift.down y) x.1 := by
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ULift.{u} SphereUnitFilling.S3) :=
      DifferentialGeometry.Topology.uliftChartedSpace _ _
    let _ : IsManifold (𝓡 3) ∞ (ULift.{u} SphereUnitFilling.S3) :=
      DifferentialGeometry.Topology.isManifold_ulift (𝓡 3) SphereUnitFilling.S3
    have h := (DifferentialGeometry.Topology.uliftDiffeomorph (𝓡 3) SphereUnitFilling.S3).symm
      |>.isLocalDiffeomorph x.1
    refine isLocalDiffeomorphAt_of_eventuallyEq ?_ h
    filter_upwards with y
    exact (DifferentialGeometry.Topology.uliftDiffeomorph_symm_apply (𝓡 3)
      SphereUnitFilling.S3 y).symm
  have hcomp : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (fun x : d.toBallChart.interior => ULift.down (α := SphereUnitFilling.S3) x.1) x :=
    hsub.comp (K := 𝓡 3) (P := SphereUnitFilling.S3) hulift
  have hamb : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (fun y : SphereUnitFilling.S3 => c.toBallChart.chart
        (SphereUnitFilling.capRadialMap
          (A.symm (stereographic' 3 P (-(y)))))) (ULift.down x.1) :=
    SphereUnitFilling.isLocalDiffeomorphAt_sphereFillIso A P c.toBallChart _
      (mem_interior_lift_iso A P d hd x)
  exact hcomp.comp (K := 𝓡 3) (P := M.Carrier) hamb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.ballComplementSmooth_unitFillingOfSphereChartIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.ballComplementSmooth_unitFillingOfSphereChartIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.ballComplementSmooth_unitFillingOfSphereChartIso ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.ballComplementSmooth_unitFillingOfSphereChartIso

end ConnectedSumUnit

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

namespace ConnectedSumUnit

universe u

variable {M : ConnectedClosedOrientedManifold.{u} 3}

theorem nonempty_diffeomorph_connectedSum_sphere_right_iso
    (X : ConnectedClosedOrientedManifold.{u} 3) (P : SphereUnitFilling.S3)
    (A : SphereUnitFilling.E3 ≃ₗᵢ[ℝ] SphereUnitFilling.E3)
    (h : ∃ d : OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold,
      ∀ u : csE3, ULift.down (d.toBallChart.chart u)
        = (SphereUnitFilling.sphereBallChart P).chart (A u)) :
    Nonempty ((connectedSum X standardThreeSphereLift.{u}).toClosedOrientedManifold.Carrier
      ≃ₘ⟮𝓡 3, 𝓡 3⟯ X.toClosedOrientedManifold.Carrier) := by
  obtain ⟨d, hd⟩ := h
  let c := orientedBallChart X
  let c' := orientedBallChart X
  let d' := orientedBallChart standardThreeSphereLift.{u}
  obtain ⟨e₁⟩ := nonempty_diffeomorph_of_unitFilling
    (unitFillingOfSphereChartIso A P d hd c)
    (ballComplementCollar_unitFillingOfSphereChartIso A P d hd c)
    (ballComplementSmooth_unitFillingOfSphereChartIso A P d hd c)
  have hΦ : Manifold.BallChartTransport c.toBallChart c'.toBallChart :=
    ballChartTransport_of_orientedBallCharts X c c'
  have hΨ : Manifold.BallChartTransport d.toBallChart d'.toBallChart :=
    ballChartTransport_of_orientedBallCharts standardThreeSphereLift.{u} d d'
  obtain ⟨e₂⟩ := nonempty_connectedSumQuotient_diffeomorph_of_ballChartTransport
    c c' d d' boundaryAttachment hΦ hΨ
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (ConnectedSumQuotient c.toBallChart d.toBallChart boundaryAttachment.1.toHomeomorph) :=
    ConnectedSumQuotient.csChartedSpace c.toBallChart d.toBallChart
      boundaryAttachment.1.toHomeomorph
  let _ : IsManifold (𝓡 3) ∞
      (ConnectedSumQuotient c.toBallChart d.toBallChart boundaryAttachment.1.toHomeomorph) :=
    ConnectedSumQuotient.csIsManifold c.toBallChart d.toBallChart
      boundaryAttachment.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap boundaryAttachment.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv boundaryAttachment.1)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (ConnectedSumQuotient c'.toBallChart d'.toBallChart boundaryAttachment.1.toHomeomorph) :=
    ConnectedSumQuotient.csChartedSpace c'.toBallChart d'.toBallChart
      boundaryAttachment.1.toHomeomorph
  let _ : IsManifold (𝓡 3) ∞
      (ConnectedSumQuotient c'.toBallChart d'.toBallChart boundaryAttachment.1.toHomeomorph) :=
    ConnectedSumQuotient.csIsManifold c'.toBallChart d'.toBallChart
      boundaryAttachment.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap boundaryAttachment.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv boundaryAttachment.1)
  exact ⟨e₂.symm.trans e₁⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumUnit.nonempty_diffeomorph_connectedSum_sphere_right_iso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumUnit.nonempty_diffeomorph_connectedSum_sphere_right_iso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumUnit.nonempty_diffeomorph_connectedSum_sphere_right_iso ``Submission.DifferentialGeometry.Topology.ConnectedSumUnit.nonempty_diffeomorph_connectedSum_sphere_right_iso

end ConnectedSumUnit

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

open _root_.Submission.DifferentialGeometry.Topology.Manifold
open _root_.Submission.OrientationAssembly
open _root_.Submission.DifferentialGeometry.Topology.SphereUnitFilling (E3)

theorem orientation_map_chartTangentEquiv_of_pullbackSmoothOrientation_eq
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    (o : ManifoldOrientation (𝓡 3) M 3)
    (φ : PartialDiffeomorph 𝓘(ℝ, E3) (𝓡 3)
      E3 M ∞)
    (hφ : ContMDiff 𝓘(ℝ, E3) (𝓡 3) ∞ (fun u => φ u))
    (hbij : ∀ u, _root_.Function.Bijective (mfderiv 𝓘(ℝ, E3) (𝓡 3) (fun u => φ u) u))
    (h : pullbackSmoothOrientation 𝓘(ℝ, E3) (𝓡 3) (fun u => φ u) hφ hbij
          (smoothOrientationOfManifoldOrientation (𝓡 3)
            (reindexManifoldOrientation (𝓡 3) csIdx o))
        = euclideanSmoothOrientation E3 stdOrientationModel) :
    ∀ x, ∀ hx : x ∈ φ.source,
      Orientation.map (Fin 3)
        ((PartialDiffeomorph.isLocalDiffeomorphAt
          (𝓡 3) (𝓡 3) ∞ φ hx).mfderivToContinuousLinearEquiv
          (by simp)).toLinearEquiv
        (stdOrientation x) = o.orientation (φ x) := by
  intro x hx
  set hld := PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ φ hx with hlddef
  set D := differentialEquivOfBijective 𝓘(ℝ, E3) (𝓡 3)
    (fun u => φ u) hbij x with hD
  have hcoe : (hld.mfderivToContinuousLinearEquiv
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)).toContinuousLinearMap
      = mfderiv 𝓘(ℝ, E3) (𝓡 3) (fun u => φ u) x :=
    IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe hld _
  have hDcoe : D.toContinuousLinearMap
      = mfderiv 𝓘(ℝ, E3) (𝓡 3) (fun u => φ u) x :=
    ContinuousLinearMap.ext (fun v => by
      change D v = mfderiv 𝓘(ℝ, E3) (𝓡 3) (fun u => φ u) x v
      exact differentialEquivOfBijective_apply 𝓘(ℝ, E3) (𝓡 3)
        (fun u => φ u) hbij x v)
  have hL : (hld.mfderivToContinuousLinearEquiv
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)).toLinearEquiv = D.toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    change (hld.mfderivToContinuousLinearEquiv (by simp : (∞ : WithTop ℕ∞) ≠ 0)) v = D v
    have hcoe_v : (hld.mfderivToContinuousLinearEquiv (by simp : (∞ : WithTop ℕ∞) ≠ 0)) v
        = mfderiv 𝓘(ℝ, E3) (𝓡 3) (fun u => φ u) x v := congrArg (fun L => L v) hcoe
    rw [hcoe_v]
    exact (differentialEquivOfBijective_apply 𝓘(ℝ, E3) (𝓡 3)
      (fun u => φ u) hbij x v).symm
  rw [hL]
  have hval : (pullbackSmoothOrientation 𝓘(ℝ, E3) (𝓡 3) (fun u => φ u)
      hφ hbij (smoothOrientationOfManifoldOrientation (𝓡 3)
        (reindexManifoldOrientation (𝓡 3) csIdx o))).val x
      = (euclideanSmoothOrientation E3 stdOrientationModel).val x := by
    rw [h]
  have hiff := (pullbackSmoothOrientation_eq_iff 𝓘(ℝ, E3) (𝓡 3)
    (fun u => φ u) hφ hbij
    (smoothOrientationOfManifoldOrientation (𝓡 3)
      (reindexManifoldOrientation (𝓡 3) csIdx o))
    (euclideanSmoothOrientation E3 stdOrientationModel) x).mp hval
  rw [euclideanSmoothOrientation_apply] at hiff
  have hN : (smoothOrientationOfManifoldOrientation (𝓡 3)
      (reindexManifoldOrientation (𝓡 3) csIdx o)).val (φ x)
      = Orientation.reindex ℝ E3 csIdx (o.orientation (φ x)) := rfl
  rw [hN] at hiff
  have h2 : Orientation.map (Fin (Module.finrank ℝ E3)) D.toLinearEquiv
        stdOrientationModel
      = Orientation.reindex ℝ E3 csIdx (o.orientation (φ x)) := by
    simpa only [tangentOrientationEquiv, finCongr_refl, Orientation.reindex_refl,
      Equiv.trans_apply, Equiv.refl_apply] using hiff
  have hstep : Orientation.reindex ℝ E3 csIdx
        (Orientation.map (Fin 3) D.toLinearEquiv (stdOrientation x))
      = Orientation.map (Fin (Module.finrank ℝ E3)) D.toLinearEquiv
          stdOrientationModel := by
    have h1 := orientation_reindex_map_comm (R := ℝ)
      (M := TangentSpace 𝓘(ℝ, E3) x)
      (N := E3) csIdx D.toLinearEquiv (stdOrientation x)
    have hstd' : Orientation.reindex ℝ (TangentSpace 𝓘(ℝ, E3) x) csIdx
        (stdOrientation x) = stdOrientationModel := rfl
    exact h1.trans (congrArg (fun z => Orientation.map
      (Fin (Module.finrank ℝ E3)) D.toLinearEquiv z) hstd')
  apply (Orientation.reindex ℝ E3 csIdx).injective
  exact hstep.trans h2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.orientation_map_chartTangentEquiv_of_pullbackSmoothOrientation_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.orientation_map_chartTangentEquiv_of_pullbackSmoothOrientation_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.orientation_map_chartTangentEquiv_of_pullbackSmoothOrientation_eq ``Submission.DifferentialGeometry.Topology.orientation_map_chartTangentEquiv_of_pullbackSmoothOrientation_eq

theorem tangentOrientationEquiv_negLinearEquiv
    (o : Orientation ℝ E3
      (Fin (Module.finrank ℝ E3))) :
    tangentOrientationEquiv ((LinearIsometryEquiv.neg ℝ :
      E3 ≃ₗᵢ[ℝ] E3).toLinearEquiv) o = -o := by
  have hdet : LinearMap.det (((LinearIsometryEquiv.neg ℝ :
      E3 ≃ₗᵢ[ℝ] E3).toLinearEquiv :
      E3 →ₗ[ℝ] E3)) < 0 := by
    have h : (((LinearIsometryEquiv.neg ℝ :
        E3 ≃ₗᵢ[ℝ] E3).toLinearEquiv :
        E3 →ₗ[ℝ] E3)) =
        (-1 : ℝ) • (LinearMap.id : E3 →ₗ[ℝ] E3) := by
      ext v
      simp
    have hfr : Module.finrank ℝ E3 = 3 := by simp
    rw [h, LinearMap.det_smul, LinearMap.det_id, mul_one, hfr]
    norm_num
  rw [tangentOrientationEquiv_self,
    Orientation.map_eq_neg_iff_det_neg o _
      (by simp : Fintype.card (Fin (Module.finrank ℝ E3))
        = Module.finrank ℝ E3)]
  exact hdet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.tangentOrientationEquiv_negLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.tangentOrientationEquiv_negLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.tangentOrientationEquiv_negLinearEquiv ``Submission.DifferentialGeometry.Topology.tangentOrientationEquiv_negLinearEquiv

theorem negSmoothOrientation_euclideanSmoothOrientation
    (o : Orientation ℝ E3
      (Fin (Module.finrank ℝ E3))) :
    negSmoothOrientation 𝓘(ℝ, E3)
      (euclideanSmoothOrientation E3 o)
      = euclideanSmoothOrientation E3 (-o) := by
  refine Subtype.ext (funext (fun x => ?_))
  rw [negSmoothOrientation_apply, euclideanSmoothOrientation_apply,
    euclideanSmoothOrientation_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.negSmoothOrientation_euclideanSmoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.negSmoothOrientation_euclideanSmoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.negSmoothOrientation_euclideanSmoothOrientation ``Submission.DifferentialGeometry.Topology.negSmoothOrientation_euclideanSmoothOrientation

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.SphereUnitFilling

lemma contMDiff_sphereChartPartialIso (A : E3 ≃ₗᵢ[ℝ] E3) (P : S3) :
    ContMDiff 𝓘(ℝ, E3) (𝓡 3) ∞ (fun u => sphereChartPartialIso A P u) := by
  rw [← contMDiffOn_univ]
  simpa only [sphereChartPartialIso_source] using (sphereChartPartialIso A P).contMDiffOn_toFun

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.contMDiff_sphereChartPartialIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.contMDiff_sphereChartPartialIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.contMDiff_sphereChartPartialIso ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.contMDiff_sphereChartPartialIso

lemma bijective_mfderiv_sphereChartPartialIso (A : E3 ≃ₗᵢ[ℝ] E3) (P : S3) (u : E3) :
    Bijective (mfderiv 𝓘(ℝ, E3) (𝓡 3) (fun u => sphereChartPartialIso A P u) u) := by
  have hsrc : u ∈ (sphereChartPartialIso A P).source := by
    rw [sphereChartPartialIso_source]
    exact Set.mem_univ u
  have hld := PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
    (sphereChartPartialIso A P) hsrc
  have hcoe := IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe hld (by simp)
  rw [← hcoe]
  exact ContinuousLinearEquiv.bijective _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.bijective_mfderiv_sphereChartPartialIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.bijective_mfderiv_sphereChartPartialIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.bijective_mfderiv_sphereChartPartialIso ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.bijective_mfderiv_sphereChartPartialIso

end DifferentialGeometry.Topology.SphereUnitFilling

namespace DifferentialGeometry.Topology

open _root_.Submission.OrientationAssembly

noncomputable def orientedBallChartOfPullbackSmoothOrientation
    (A : SphereUnitFilling.E3 ≃ₗᵢ[ℝ] SphereUnitFilling.E3) (P : SphereUnitFilling.S3)
    (h : pullbackSmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3) (𝓡 3)
          (fun u => SphereUnitFilling.sphereChartPartialIso A P u)
          (SphereUnitFilling.contMDiff_sphereChartPartialIso A P)
          (SphereUnitFilling.bijective_mfderiv_sphereChartPartialIso A P)
          (smoothOrientationOfManifoldOrientation (𝓡 3)
            (reindexManifoldOrientation (𝓡 3) csIdx standardThreeSphere.orientation))
        = euclideanSmoothOrientation SphereUnitFilling.E3 stdOrientationModel) :
    OrientedBallChart standardThreeSphere.toClosedOrientedManifold where
  toBallChart := SphereUnitFilling.sphereBallChartIso A P
  preserves_orientation := orientation_map_chartTangentEquiv_of_pullbackSmoothOrientation_eq
    standardThreeSphere.orientation (SphereUnitFilling.sphereChartPartialIso A P)
    (SphereUnitFilling.contMDiff_sphereChartPartialIso A P)
    (SphereUnitFilling.bijective_mfderiv_sphereChartPartialIso A P) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.orientedBallChartOfPullbackSmoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.orientedBallChartOfPullbackSmoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.orientedBallChartOfPullbackSmoothOrientation ``Submission.DifferentialGeometry.Topology.orientedBallChartOfPullbackSmoothOrientation

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

open _root_.Submission.OrientationAssembly
open _root_.Submission.DifferentialGeometry.Topology.SphereUnitFilling (E3)

noncomputable def compPartialDiffeomorph
    {M : Type*} {N : Type*} [TopologicalSpace M]
    [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold (𝓡 3) ∞ N]
    (φ : PartialDiffeomorph 𝓘(ℝ, E3) (𝓡 3)
      E3 M ∞)
    (Φ : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N) :
    PartialDiffeomorph 𝓘(ℝ, E3) (𝓡 3)
      E3 N ∞ where
  toPartialEquiv :=
    { toFun := fun u => Φ (φ u)
      invFun := fun y => φ.symm (Φ.symm y)
      source := φ.source
      target := Φ '' φ.target
      map_source' := fun u hu => ⟨φ u, φ.map_source hu, rfl⟩
      map_target' := fun y hy => by
        obtain ⟨z, hz, rfl⟩ := hy
        have hzs : Φ.symm (Φ z) ∈ φ.target := by rw [Φ.symm_apply_apply]; exact hz
        exact φ.toPartialEquiv.map_target hzs
      left_inv' := fun u hu => by
        rw [Φ.symm_apply_apply]
        exact φ.toPartialEquiv.left_inv' hu
      right_inv' := fun y hy => by
        obtain ⟨z, hz, rfl⟩ := hy
        have hzi : φ (φ.symm z) = z := φ.toPartialEquiv.right_inv' hz
        rw [Φ.symm_apply_apply, hzi] }
  open_source := φ.open_source
  open_target := Φ.toHomeomorph.isOpenMap _ φ.open_target
  contMDiffOn_toFun := Φ.contMDiff.comp_contMDiffOn φ.contMDiffOn_toFun
  contMDiffOn_invFun := by
    refine φ.contMDiffOn_invFun.comp Φ.symm.contMDiff.contMDiffOn ?_
    rintro y ⟨z, hz, rfl⟩
    have hmem : Φ.symm (Φ z) ∈ φ.target := by rw [Φ.symm_apply_apply]; exact hz
    exact hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.compPartialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.compPartialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.compPartialDiffeomorph ``Submission.DifferentialGeometry.Topology.compPartialDiffeomorph

@[simp]
lemma compPartialDiffeomorph_apply
    {M : Type*} {N : Type*} [TopologicalSpace M]
    [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold (𝓡 3) ∞ N]
    (φ : PartialDiffeomorph 𝓘(ℝ, E3) (𝓡 3)
      E3 M ∞)
    (Φ : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N) (u : E3) :
    compPartialDiffeomorph φ Φ u = Φ (φ u) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.compPartialDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.compPartialDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.compPartialDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.compPartialDiffeomorph_apply

lemma compPartialDiffeomorph_source
    {M : Type*} {N : Type*} [TopologicalSpace M]
    [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold (𝓡 3) ∞ N]
    (φ : PartialDiffeomorph 𝓘(ℝ, E3) (𝓡 3)
      E3 M ∞)
    (Φ : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N) :
    (compPartialDiffeomorph φ Φ).source = φ.source := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.compPartialDiffeomorph_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.compPartialDiffeomorph_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.compPartialDiffeomorph_source ``Submission.DifferentialGeometry.Topology.compPartialDiffeomorph_source


theorem preservesOrientation_compPartialDiffeomorph
    {M : Type*} {N : Type*} [TopologicalSpace M]
    [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold (𝓡 3) ∞ N]
    (φ : PartialDiffeomorph 𝓘(ℝ, E3) (𝓡 3)
      E3 M ∞)
    (oM : ManifoldOrientation (𝓡 3) M 3) (oN : ManifoldOrientation (𝓡 3) N 3)
    (Φ : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N) (hΦ : Φ.preservesOrientation oM oN)
    (hc : ∀ x, ∀ hx : x ∈ φ.source,
      Orientation.map (Fin 3)
        ((PartialDiffeomorph.isLocalDiffeomorphAt
          (𝓡 3) (𝓡 3) ∞ φ hx).mfderivToContinuousLinearEquiv
          (by simp)).toLinearEquiv
        (stdOrientation x) = oM.orientation (φ x)) :
    ∀ x, ∀ hx : x ∈ (compPartialDiffeomorph φ Φ).source,
      Orientation.map (Fin 3)
        ((PartialDiffeomorph.isLocalDiffeomorphAt
          (𝓡 3) (𝓡 3) ∞ (compPartialDiffeomorph φ Φ) hx).mfderivToContinuousLinearEquiv
          (by simp)).toLinearEquiv
        (stdOrientation x) = oN.orientation (compPartialDiffeomorph φ Φ x) := by
  intro x hx
  have hkey : (((PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (compPartialDiffeomorph φ Φ) hx).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv :
          TangentSpace (𝓡 3) x ≃ₗ[ℝ] TangentSpace (𝓡 3) (Φ (φ x))) =
      ((PartialDiffeomorph.isLocalDiffeomorphAt
        (𝓡 3) (𝓡 3) ∞ φ hx).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv.trans
        ((Φ.mfderivToContinuousLinearEquiv (by simp) (φ x)).toLinearEquiv) := by
    apply LinearEquiv.ext
    intro v
    change mfderiv 𝓘(ℝ, E3) (𝓡 3)
        ((fun z : M => Φ z) ∘ (fun y : E3 => φ y)) x v =
      (Φ.mfderivToContinuousLinearEquiv (by simp) (φ x))
        (((PartialDiffeomorph.isLocalDiffeomorphAt
          (𝓡 3) (𝓡 3) ∞ φ hx).mfderivToContinuousLinearEquiv
          (by simp)) v)
    rw [mfderiv_comp_apply x (Φ.mdifferentiable (by simp) (φ x))
      (PartialDiffeomorph.mdifferentiableAt φ (by simp) hx)]
    rfl
  rw [hkey]
  erw [orientation_map_trans]
  rw [hc x hx]
  erw [hΦ (φ x)]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.preservesOrientation_compPartialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.preservesOrientation_compPartialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.preservesOrientation_compPartialDiffeomorph ``Submission.DifferentialGeometry.Topology.preservesOrientation_compPartialDiffeomorph


end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

open _root_.Submission.OrientationAssembly

universe u

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

open _root_.Submission.OrientationAssembly

universe u

section LiftIso

local instance instChartedSpaceUliftSphere :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ULift.{u} SphereUnitFilling.S3) :=
  standardThreeSphereLift.{u}.toClosedOrientedManifold.charts

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.instChartedSpaceUliftSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.instChartedSpaceUliftSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.instChartedSpaceUliftSphere ``Submission.DifferentialGeometry.Topology.instChartedSpaceUliftSphere

local instance instIsManifoldUliftSphere :
    IsManifold (𝓡 3) ∞ (ULift.{u} SphereUnitFilling.S3) :=
  standardThreeSphereLift.{u}.toClosedOrientedManifold.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.instIsManifoldUliftSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.instIsManifoldUliftSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.instIsManifoldUliftSphere ``Submission.DifferentialGeometry.Topology.instIsManifoldUliftSphere

noncomputable def sphereBallChartIsoLift
    (A : SphereUnitFilling.E3 ≃ₗᵢ[ℝ] SphereUnitFilling.E3) (P : SphereUnitFilling.S3) :
    BallChart 3 (𝓡 3) (ULift.{u} SphereUnitFilling.S3) where
  chart := compPartialDiffeomorph (SphereUnitFilling.sphereChartPartialIso A P)
    standardThreeSphereLiftDiffeomorph.{u}
  closedBall_subset_source := fun _ hx =>
    (SphereUnitFilling.sphereBallChartIso A P).closedBall_subset_source hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereBallChartIsoLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereBallChartIsoLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereBallChartIsoLift ``Submission.DifferentialGeometry.Topology.sphereBallChartIsoLift

noncomputable def orientedBallChartLiftIso
    (A : SphereUnitFilling.E3 ≃ₗᵢ[ℝ] SphereUnitFilling.E3) (P : SphereUnitFilling.S3)
    (h : pullbackSmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3) (𝓡 3)
          (fun u => SphereUnitFilling.sphereChartPartialIso A P u)
          (SphereUnitFilling.contMDiff_sphereChartPartialIso A P)
          (SphereUnitFilling.bijective_mfderiv_sphereChartPartialIso A P)
          (smoothOrientationOfManifoldOrientation (𝓡 3)
            (reindexManifoldOrientation (𝓡 3) csIdx standardThreeSphere.orientation))
        = euclideanSmoothOrientation SphereUnitFilling.E3 stdOrientationModel) :
    OrientedBallChart standardThreeSphereLift.{u}.toClosedOrientedManifold where
  toBallChart := sphereBallChartIsoLift A P
  preserves_orientation := preservesOrientation_compPartialDiffeomorph
    (SphereUnitFilling.sphereChartPartialIso A P) standardThreeSphere.orientation
    standardThreeSphereLift.{u}.orientation standardThreeSphereLiftDiffeomorph.{u}
    standardThreeSphereLiftDiffeomorph_preservesOrientation
    (orientedBallChartOfPullbackSmoothOrientation A P h).preserves_orientation

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.orientedBallChartLiftIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.orientedBallChartLiftIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.orientedBallChartLiftIso ``Submission.DifferentialGeometry.Topology.orientedBallChartLiftIso

theorem orientedBallChartLiftIso_chart
    (A : SphereUnitFilling.E3 ≃ₗᵢ[ℝ] SphereUnitFilling.E3) (P : SphereUnitFilling.S3)
    (h : pullbackSmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3) (𝓡 3)
          (fun u => SphereUnitFilling.sphereChartPartialIso A P u)
          (SphereUnitFilling.contMDiff_sphereChartPartialIso A P)
          (SphereUnitFilling.bijective_mfderiv_sphereChartPartialIso A P)
          (smoothOrientationOfManifoldOrientation (𝓡 3)
            (reindexManifoldOrientation (𝓡 3) csIdx standardThreeSphere.orientation))
        = euclideanSmoothOrientation SphereUnitFilling.E3 stdOrientationModel)
    (u : csE3) :
    ULift.down (α := SphereUnitFilling.S3) ((orientedBallChartLiftIso A P h).toBallChart.chart u)
      = (SphereUnitFilling.sphereBallChart P).chart (A u) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.orientedBallChartLiftIso_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.orientedBallChartLiftIso_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.orientedBallChartLiftIso_chart ``Submission.DifferentialGeometry.Topology.orientedBallChartLiftIso_chart


theorem nonempty_diffeomorph_connectedSum_sphere_right_unit
    (X : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty ((connectedSum X standardThreeSphereLift.{u}).toClosedOrientedManifold.Carrier
      ≃ₘ⟮𝓡 3, 𝓡 3⟯ X.toClosedOrientedManifold.Carrier) := by
  obtain ⟨P0, hP0⟩ := (NormedSpace.sphere_nonempty (E := SphereUnitFilling.E4)
    (x := 0) (r := 1)).mpr (by norm_num)
  let P : SphereUnitFilling.S3 := ⟨P0, hP0⟩
  let A₁ : SphereUnitFilling.E3 ≃ₗᵢ[ℝ] SphereUnitFilling.E3 :=
    LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 3))
  let oSph : SmoothOrientation (𝓡 3) SphereUnitFilling.S3 :=
    smoothOrientationOfManifoldOrientation (𝓡 3)
      (reindexManifoldOrientation (𝓡 3) csIdx standardThreeSphere.orientation)
  let oF : SmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3) SphereUnitFilling.E3 :=
    pullbackSmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3) (𝓡 3)
      (fun u => SphereUnitFilling.sphereChartPartialIso A₁ P u)
      (SphereUnitFilling.contMDiff_sphereChartPartialIso A₁ P)
      (SphereUnitFilling.bijective_mfderiv_sphereChartPartialIso A₁ P) oSph
  let oE : SmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3) SphereUnitFilling.E3 :=
    euclideanSmoothOrientation SphereUnitFilling.E3 stdOrientationModel
  rcases smoothOrientation_eq_or_eq_neg 𝓘(ℝ, SphereUnitFilling.E3) oF oE 0 with hcase | hcase
  · have hle : oF = oE := Subtype.ext (funext hcase)
    refine ConnectedSumUnit.nonempty_diffeomorph_connectedSum_sphere_right_iso X P A₁
      ⟨orientedBallChartLiftIso A₁ P hle, ?_⟩
    intro u
    rw [orientedBallChartLiftIso_chart]
  · let A₂ : SphereUnitFilling.E3 ≃ₗᵢ[ℝ] SphereUnitFilling.E3 :=
    (LinearIsometryEquiv.neg ℝ : SphereUnitFilling.E3 ≃ₗᵢ[ℝ] SphereUnitFilling.E3)
    have hmfA₂ : ∀ u : SphereUnitFilling.E3,
        mfderiv 𝓘(ℝ, SphereUnitFilling.E3) 𝓘(ℝ, SphereUnitFilling.E3)
          (fun u => A₂ u) u = A₂.toContinuousLinearEquiv.toContinuousLinearMap := by
      intro u
      exact ContinuousLinearMap.mfderiv_eq (𝕜 := ℝ)
        (f := (A₂ : SphereUnitFilling.E3 →L[ℝ] SphereUnitFilling.E3)) (x := u)
    have hA₂ : ContMDiff 𝓘(ℝ, SphereUnitFilling.E3) 𝓘(ℝ, SphereUnitFilling.E3) ∞
        (fun u => A₂ u) := A₂.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff
    have hbA₂ : ∀ u, _root_.Function.Bijective (mfderiv 𝓘(ℝ, SphereUnitFilling.E3)
        𝓘(ℝ, SphereUnitFilling.E3) (fun u => A₂ u) u) := by
      intro u
      rw [hmfA₂ u]
      exact A₂.toContinuousLinearEquiv.bijective
    have hneg : oF = euclideanSmoothOrientation SphereUnitFilling.E3 (-stdOrientationModel) := by
      have h1 : oF = negSmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3) oE := by
        refine Subtype.ext (funext (fun x => ?_))
        rw [negSmoothOrientation_apply]
        exact hcase x
      exact h1.trans (negSmoothOrientation_euclideanSmoothOrientation stdOrientationModel)
    have hApull : pullbackSmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3)
        𝓘(ℝ, SphereUnitFilling.E3) (fun u => A₂ u) hA₂ hbA₂
        (euclideanSmoothOrientation SphereUnitFilling.E3 (-stdOrientationModel)) = oE := by
      refine Subtype.ext (funext (fun x => ?_))
      rw [pullbackSmoothOrientation_eq_iff]
      rw [euclideanSmoothOrientation_apply, euclideanSmoothOrientation_apply]
      have hD : differentialEquivOfBijective 𝓘(ℝ, SphereUnitFilling.E3)
          𝓘(ℝ, SphereUnitFilling.E3) (fun u => A₂ u) hbA₂ x
          = A₂.toContinuousLinearEquiv := by
        apply ContinuousLinearEquiv.ext
        funext v
        rw [differentialEquivOfBijective_apply, hmfA₂ x]
        rfl
      rw [hD]
      exact tangentOrientationEquiv_negLinearEquiv stdOrientationModel
    have h₂ : pullbackSmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3) (𝓡 3)
        (fun u => SphereUnitFilling.sphereChartPartialIso A₂ P u)
        (SphereUnitFilling.contMDiff_sphereChartPartialIso A₂ P)
        (SphereUnitFilling.bijective_mfderiv_sphereChartPartialIso A₂ P) oSph = oE := by
      refine Subtype.ext (funext (fun x => ?_))
      have hcomp := pullbackSmoothOrientation_comp_apply 𝓘(ℝ, SphereUnitFilling.E3)
        𝓘(ℝ, SphereUnitFilling.E3) (𝓡 3) (fun u : SphereUnitFilling.E3 => A₂ u)
        (fun v : SphereUnitFilling.E3 => SphereUnitFilling.sphereChartPartialIso A₁ P v)
        hA₂ (SphereUnitFilling.contMDiff_sphereChartPartialIso A₁ P) hbA₂
        (SphereUnitFilling.bijective_mfderiv_sphereChartPartialIso A₁ P)
        (SphereUnitFilling.bijective_mfderiv_sphereChartPartialIso A₂ P) oSph x
      erw [hcomp]
      have hinner : pullbackSmoothOrientation 𝓘(ℝ, SphereUnitFilling.E3) (𝓡 3)
          (fun v : SphereUnitFilling.E3 => SphereUnitFilling.sphereChartPartialIso A₁ P v)
          (SphereUnitFilling.contMDiff_sphereChartPartialIso A₁ P)
          (SphereUnitFilling.bijective_mfderiv_sphereChartPartialIso A₁ P) oSph = oF := rfl
      rw [hinner, hneg, hApull]
    refine ConnectedSumUnit.nonempty_diffeomorph_connectedSum_sphere_right_iso X P A₂
      ⟨orientedBallChartLiftIso A₂ P h₂, ?_⟩
    intro u
    rw [orientedBallChartLiftIso_chart]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_sphere_right_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_sphere_right_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_sphere_right_unit ``Submission.DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_sphere_right_unit

end LiftIso

end DifferentialGeometry.Topology
