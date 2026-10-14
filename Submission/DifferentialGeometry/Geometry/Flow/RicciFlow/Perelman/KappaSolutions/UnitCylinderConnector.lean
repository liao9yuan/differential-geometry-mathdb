import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SphereShortConnector
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeck
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UnitCylinderLength
import Submission.DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.Order.Interval.Set.ProjIcc

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private local instance connectorSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.connectorSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.connectorSphereDimension target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem unitCylinder_exists_short_connector (x y : SpatialNeckCylinder) :
    ∃ γ : ℝ → SpatialNeckCylinder,
      ContMDiff 𝓘(ℝ, ℝ) SpatialNeckCylinderModel ∞ γ ∧ γ 0 = x ∧ γ 1 = y ∧
      (∀ t : ℝ, (γ t).2 = x.2 + t * (y.2 - x.2)) ∧
      metricPathELength (I := SpatialNeckCylinderModel) unitCylinderMetric γ 0 1 ≤
        ENNReal.ofReal (Real.sqrt (Real.pi ^ 2 + (y.2 - x.2) ^ 2)) := by
  obtain ⟨L, c, hL, hc, hc0, hc1, hspeed⟩ := sphere2_exists_short_constant_speed_curve x.1 y.1
  let δ := y.2 - x.2
  let z : ℝ → ℝ := fun t => x.2 + t * δ
  let γ : ℝ → SpatialNeckCylinder := fun t => (c t, z t)
  have hz : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ z :=
    (contDiff_const.add (contDiff_id.mul contDiff_const)).contMDiff
  have hγ : ContMDiff 𝓘(ℝ, ℝ) SpatialNeckCylinderModel ∞ γ := hc.prodMk hz
  have hprodSpeed (t : ℝ) : unitCylinderMetric.inner (γ t)
      (mfderiv 𝓘(ℝ, ℝ) SpatialNeckCylinderModel γ t 1)
      (mfderiv 𝓘(ℝ, ℝ) SpatialNeckCylinderModel γ t 1) = L ^ 2 + δ ^ 2 := by
    have hdlin : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) z t 1 = δ := by
      rw [mfderiv_eq_fderiv]
      change (fderiv ℝ z t) (1 : ℝ) = δ
      have hdz : HasDerivAt z δ t := by
        exact ((hasDerivAt_const t x.2).add ((hasDerivAt_id t).mul_const δ)).congr_deriv
          (by ring)
      simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
        congrArg (fun D : ℝ →L[ℝ] ℝ => D 1) hdz.hasFDerivAt.fderiv
    have hdprod := mfderiv_prodMk
      (hc.mdifferentiableAt (x := t) (by decide))
      (hz.mdifferentiableAt (x := t) (by decide))
    have hdvalue := congrArg
      (fun D : ℝ →L[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ) => D 1) hdprod
    change (mfderiv 𝓘(ℝ, ℝ) SpatialNeckCylinderModel γ t 1 :
      EuclideanSpace ℝ (Fin 2) × ℝ) =
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) c t 1, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) z t 1) at hdvalue
    have hd := hdvalue.trans (congrArg
      (fun a : ℝ => (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) c t 1, a)) hdlin)
    have hinner := congrArg₂
      (fun V Z : EuclideanSpace ℝ (Fin 2) × ℝ => unitCylinderMetric.inner (γ t) V Z) hd hd
    apply hinner.trans
    have hu := unitCylinderMetric_inner (c t) (z t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) c t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) c t 1) δ δ
    exact hu.trans ((congrArg (fun a : ℝ => a + δ * δ) (hspeed t)).trans (by ring))
  have hlength : metricPathELength (I := SpatialNeckCylinderModel) unitCylinderMetric γ 0 1 =
      ENNReal.ofReal (Real.sqrt (L ^ 2 + δ ^ 2)) := by
    rw [metricPathELength_eq]
    simp only [hprodSpeed]
    rw [_root_.MeasureTheory.setLIntegral_const, Real.volume_Ioo]
    norm_num
  refine ⟨γ, hγ, ?_, ?_, fun _ => rfl, ?_⟩
  · simp only [γ, z, hc0, _root_.MulZeroClass.zero_mul, add_zero, Prod.mk.eta]
  · apply Prod.ext
    · exact hc1
    · change x.2 + 1 * (y.2 - x.2) = y.2
      ring
  · apply hlength.trans_le
    apply ENNReal.ofReal_le_ofReal
    apply Real.sqrt_le_sqrt
    dsimp only [δ]
    nlinarith [hL.1, hL.2, Real.pi_pos]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinder_exists_short_connector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinder_exists_short_connector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinder_exists_short_connector ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinder_exists_short_connector

private theorem cylinder_affine_mem_Icc {r a b t : ℝ}
    (ha : a ∈ _root_.Set.Icc (-r) r) (hb : b ∈ _root_.Set.Icc (-r) r) (ht : t ∈ _root_.Set.Icc 0 1) :
    a + t * (b - a) ∈ _root_.Set.Icc (-r) r := by
  have hloA := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha.1)
  have hloB := mul_nonneg ht.1 (sub_nonneg.mpr hb.1)
  have hhiA := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha.2)
  have hhiB := mul_nonneg ht.1 (sub_nonneg.mpr hb.2)
  constructor <;> nlinarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinder_affine_mem_Icc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinder_affine_mem_Icc target :: scope.openDecls } }

theorem unitCylinder_exists_short_core_connector (epsilon : ℝ)
    (x y : spatialNeckBuffer epsilon)
    (hx : x ∈ spatialNeckClosedCore epsilon) (hy : y ∈ spatialNeckClosedCore epsilon) :
    ∃ β : ℝ → spatialNeckBuffer epsilon,
      ContMDiffOn 𝓘(ℝ, ℝ) SpatialNeckCylinderModel 1 β (_root_.Set.Icc 0 1) ∧
      β 0 = x ∧ β 1 = y ∧ (∀ t : ℝ, β t ∈ spatialNeckClosedCore epsilon) ∧
      metricPathELength (I := SpatialNeckCylinderModel)
          (unitCylinderMetric.restrictOpen (spatialNeckBuffer epsilon)) β 0 1 ≤
        ENNReal.ofReal (Real.sqrt (Real.pi ^ 2 + (y.val.2 - x.val.2) ^ 2)) := by
  obtain ⟨γ, hγ, hγ0, hγ1, haxial, hlength⟩ := unitCylinder_exists_short_connector x.val y.val
  have hheight (t : ℝ) (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1) :
      (γ t).2 ∈ _root_.Set.Icc (-epsilon⁻¹) epsilon⁻¹ := by
    rw [haxial]
    exact cylinder_affine_mem_Icc hx hy ht
  let τ : ℝ → _root_.Set.Icc (0 : ℝ) 1 := Set.projIcc 0 1 zero_le_one
  let β : ℝ → spatialNeckBuffer epsilon := fun t =>
    ⟨γ (τ t), by
      have hh := hheight (τ t) (τ t).property
      change -epsilon⁻¹ - 1 < (γ (τ t)).2 ∧ (γ (τ t)).2 < epsilon⁻¹ + 1
      constructor <;> linarith [hh.1, hh.2]⟩
  have hβcore (t : ℝ) : β t ∈ spatialNeckClosedCore epsilon :=
    hheight (τ t) (τ t).property
  have hβval (t : ℝ) (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1) : (β t).val = γ t := by
    change γ (Set.projIcc 0 1 zero_le_one t) = γ t
    rw [Set.projIcc_of_mem zero_le_one ht]
  have hvalSmooth : ContMDiffOn 𝓘(ℝ, ℝ) SpatialNeckCylinderModel ∞
      ((Subtype.val : spatialNeckBuffer epsilon → SpatialNeckCylinder) ∘ β) (_root_.Set.Icc 0 1) :=
    hγ.contMDiffOn.congr hβval
  have hβsmooth : ContMDiffOn 𝓘(ℝ, ℝ) SpatialNeckCylinderModel ∞ β (_root_.Set.Icc 0 1) := by
    intro t ht
    exact (ContMDiffWithinAt.subtypeVal_comp_iff (spatialNeckBuffer epsilon) β
      (_root_.Set.Icc (0 : ℝ) 1) t).mp (hvalSmooth t ht)
  have hlift : metricPathELength (I := SpatialNeckCylinderModel)
        (unitCylinderMetric.restrictOpen (spatialNeckBuffer epsilon)) β 0 1 =
      metricPathELength (I := SpatialNeckCylinderModel) unitCylinderMetric
        ((Subtype.val : spatialNeckBuffer epsilon → SpatialNeckCylinder) ∘ β) 0 1 :=
    unitCylinder_metricPathELength_restrict_open (spatialNeckBuffer epsilon)
      (hβsmooth.of_le (by decide))
  have hsame : metricPathELength (I := SpatialNeckCylinderModel) unitCylinderMetric
        ((Subtype.val : spatialNeckBuffer epsilon → SpatialNeckCylinder) ∘ β) 0 1 =
      metricPathELength (I := SpatialNeckCylinderModel) unitCylinderMetric γ 0 1 := by
    let _ : _root_.Bundle.RiemannianBundle (fun q : SpatialNeckCylinder => TangentSpace SpatialNeckCylinderModel q) :=
      ⟨unitCylinderMetric.toRiemannianMetric⟩
    exact Manifold.pathELength_congr hβval
  refine ⟨β, hβsmooth.of_le (by decide), ?_, ?_, hβcore, (hlift.trans hsame).trans_le hlength⟩
  · exact Subtype.ext ((hβval 0 ⟨le_rfl, zero_le_one⟩).trans hγ0)
  · exact Subtype.ext ((hβval 1 ⟨zero_le_one, le_rfl⟩).trans hγ1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinder_exists_short_core_connector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinder_exists_short_core_connector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinder_exists_short_core_connector ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinder_exists_short_core_connector

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
