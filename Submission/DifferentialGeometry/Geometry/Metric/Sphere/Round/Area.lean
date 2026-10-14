import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Round.GraphParametrization
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import Submission.DifferentialGeometry.Geometry.Comparison.Volume.Model
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Parametric.AreaFormula
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Euclidean

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Metric _root_.Set _root_.Module _root_.Submission.Module _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Integral.Measure (paramDensity paramGramMatrix paramGramMatrix_apply
  modelHaar riemannianVolumeMeasure)
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.RealInnerProductSpace _root_.ENNReal _root_.Topology _root_.Matrix

namespace DifferentialGeometry.Geometry

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

private instance _root_.Submission.DifferentialGeometry.Geometry.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.Geometry.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry_1 : Fact (Module.finrank ℝ E2 = 1 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry_1 target :: scope.openDecls } }

variable {v : E3}

private local instance _root_.Submission.DifferentialGeometry.Geometry.instMeasurableSpaceEuclideanSpaceRealFinOfNatNat_differentialGeometry : MeasurableSpace E2 := borel E2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.instMeasurableSpaceEuclideanSpaceRealFinOfNatNat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.instMeasurableSpaceEuclideanSpaceRealFinOfNatNat_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.instBorelSpaceEuclideanSpaceRealFinOfNatNat_differentialGeometry : BorelSpace E2 := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.instBorelSpaceEuclideanSpaceRealFinOfNatNat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.instBorelSpaceEuclideanSpaceRealFinOfNatNat_differentialGeometry target :: scope.openDecls } }

theorem det_add_smul_vecMulVec_transpose_mulVec (B : Matrix (Fin 2) (Fin 2) ℝ)
    (c : Fin 2 → ℝ) (k : ℝ) :
    (B + k • Matrix.vecMulVec (Bᵀ *ᵥ c) (Bᵀ *ᵥ c)).det =
      B.det * (1 + k * (dotProduct c (B *ᵥ c))) := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.det_fin_two,
    Matrix.mulVec, Matrix.transpose_apply, Fin.sum_univ_two, dotProduct]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.det_add_smul_vecMulVec_transpose_mulVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.det_add_smul_vecMulVec_transpose_mulVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.det_add_smul_vecMulVec_transpose_mulVec ``Submission.DifferentialGeometry.Geometry.det_add_smul_vecMulVec_transpose_mulVec

private def graphDomain : TopologicalSpace.Opens E2 := ⟨ball (0 : E2) 1, isOpen_ball⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.graphDomain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.graphDomain target :: scope.openDecls } }

private theorem mem_graphDomain_iff {y : E2} : y ∈ graphDomain ↔ y ∈ _root_.Metric.ball (0 : E2) 1 := Iff.rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.mem_graphDomain_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.mem_graphDomain_iff target :: scope.openDecls } }

noncomputable def sphereGraphParametrization (hv : ‖v‖ = 1)
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) : E2 → _root_.Metric.sphere (0 : E3) 1 :=
  fun y => by
    classical
    exact if hy : y ∈ _root_.Metric.ball (0 : E2) 1 then
      ⟨sphereGraphMap R y, by
        rw [mem_sphere_zero_iff_norm]
        have hle : ‖y‖ ≤ 1 := le_of_lt (mem_ball_zero_iff.mp hy)
        have h := sphereGraphMap_norm_sq hv R y hle
        nlinarith [norm_nonneg (sphereGraphMap R y)]⟩
    else ⟨v, mem_sphere_zero_iff_norm.mpr hv⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sphereGraphParametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sphereGraphParametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sphereGraphParametrization ``Submission.DifferentialGeometry.Geometry.sphereGraphParametrization

theorem coe_sphereGraphParametrization (hv : ‖v‖ = 1) (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ)
    {y : E2} (hy : y ∈ _root_.Metric.ball (0 : E2) 1) :
    (sphereGraphParametrization hv R y : E3) = sphereGraphMap R y := by
  rw [sphereGraphParametrization, dif_pos hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.coe_sphereGraphParametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.coe_sphereGraphParametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.coe_sphereGraphParametrization ``Submission.DifferentialGeometry.Geometry.coe_sphereGraphParametrization

private theorem contDiffAt_sphereGraphMap (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ)
    {y : E2} (hy : ‖y‖ < 1) :
    ContDiffAt ℝ ∞ (sphereGraphMap (v := v) R) y := by
  have hpos : 0 < 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
  have hR : ContDiffAt ℝ ∞ (fun z : E2 => (R z : E3)) y :=
    ((Submodule.subtypeL (ℝ ∙ v)ᗮ).contDiff.comp R.contDiff).contDiffAt
  have hsq : ContDiffAt ℝ ∞ (fun z : E2 => ‖z‖ ^ 2) y := (contDiff_norm_sq ℝ).contDiffAt
  have hsub : ContDiffAt ℝ ∞ (fun z : E2 => 1 - ‖z‖ ^ 2) y := contDiffAt_const.sub hsq
  have hsqrt : ContDiffAt ℝ ∞ (fun z : E2 => Real.sqrt (1 - ‖z‖ ^ 2)) y :=
    hsub.sqrt (by positivity)
  have hsmul : ContDiffAt ℝ ∞ (fun z : E2 => Real.sqrt (1 - ‖z‖ ^ 2) • v) y :=
    hsqrt.smul contDiffAt_const
  exact hR.add hsmul

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.contDiffAt_sphereGraphMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.contDiffAt_sphereGraphMap target :: scope.openDecls } }

private theorem sphereGraphMap_mem_sphere (hv : ‖v‖ = 1) (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ)
    {y : E2} (hy : ‖y‖ < 1) :
    sphereGraphMap (v := v) R y ∈ _root_.Metric.sphere (0 : E3) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have hle : ‖y‖ ≤ 1 := le_of_lt hy
  have h := sphereGraphMap_norm_sq hv R y hle
  nlinarith [norm_nonneg (sphereGraphMap R y)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.sphereGraphMap_mem_sphere
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.sphereGraphMap_mem_sphere target :: scope.openDecls } }

private theorem contMDiff_sphereGraphMap_domain (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) :
    ContMDiff 𝓘(ℝ, E2) 𝓘(ℝ, E3) ∞ (fun y : graphDomain => sphereGraphMap R (y : E2)) := by
  intro y
  exact (contMDiffAt_subtype_iff (I := 𝓘(ℝ, E2)) (I' := 𝓘(ℝ, E3)) (U := graphDomain)
    (f := sphereGraphMap R)).mpr
    ((contDiffAt_sphereGraphMap R (mem_ball_zero_iff.mp (mem_graphDomain_iff.mp y.2))).contMDiffAt)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.contMDiff_sphereGraphMap_domain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.contMDiff_sphereGraphMap_domain target :: scope.openDecls } }

private theorem contMDiff_sphereGraphPoint_domain (hv : ‖v‖ = 1) (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) :
    ContMDiff 𝓘(ℝ, E2) (𝓡 2) ∞ (fun y : graphDomain =>
      (⟨sphereGraphMap R (y : E2),
        sphereGraphMap_mem_sphere hv R (mem_ball_zero_iff.mp (mem_graphDomain_iff.mp y.2))⟩ :
          sphere (0 : E3) 1)) :=
  ContMDiff.codRestrict_sphere (n := 2) (contMDiff_sphereGraphMap_domain (v := v) R) _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.contMDiff_sphereGraphPoint_domain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.contMDiff_sphereGraphPoint_domain target :: scope.openDecls } }

private theorem contMDiffAt_sphereGraphParametrization (hv : ‖v‖ = 1)
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) {y : E2} (hy : y ∈ graphDomain) :
    ContMDiffAt 𝓘(ℝ, E2) (𝓡 2) ∞ (sphereGraphParametrization hv R) y := by
  have hcod := contMDiff_sphereGraphPoint_domain hv R
  have heq : (fun z : graphDomain => sphereGraphParametrization hv R (z : E2)) =
      fun z : graphDomain =>
        (⟨sphereGraphMap R (z : E2), sphereGraphMap_mem_sphere hv R
          (mem_ball_zero_iff.mp (mem_graphDomain_iff.mp z.2))⟩ : _root_.Metric.sphere (0 : E3) 1) := by
    funext z
    rw [sphereGraphParametrization, dif_pos (mem_graphDomain_iff.mp z.2)]
  have hsub : ContMDiffAt 𝓘(ℝ, E2) (𝓡 2) ∞
      (fun z : graphDomain => sphereGraphParametrization hv R (z : E2)) ⟨y, hy⟩ := by
    rw [heq]
    exact hcod ⟨y, hy⟩
  exact (contMDiffAt_subtype_iff (I := 𝓘(ℝ, E2)) (I' := 𝓡 2) (U := graphDomain)
    (f := sphereGraphParametrization hv R) (x := ⟨y, hy⟩)).mp hsub

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.contMDiffAt_sphereGraphParametrization
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.contMDiffAt_sphereGraphParametrization target :: scope.openDecls } }

theorem contMDiffOn_sphereGraphParametrization (hv : ‖v‖ = 1)
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) :
    ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) 1 (sphereGraphParametrization hv R)
      (_root_.Metric.ball (0 : E2) 1) :=
  fun y hy => ((contMDiffAt_sphereGraphParametrization hv R hy).contMDiffWithinAt).of_le (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contMDiffOn_sphereGraphParametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contMDiffOn_sphereGraphParametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contMDiffOn_sphereGraphParametrization ``Submission.DifferentialGeometry.Geometry.contMDiffOn_sphereGraphParametrization

theorem sphereGraphParametrization_injOn (hv : ‖v‖ = 1) (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) :
    Set.InjOn (sphereGraphParametrization hv R) (_root_.Metric.ball (0 : E2) 1) := by
  intro y hy y' hy' h
  have hcoe := congrArg (fun w : _root_.Metric.sphere (0 : E3) 1 => (w : E3)) h
  simp only [coe_sphereGraphParametrization hv R hy,
    coe_sphereGraphParametrization hv R hy'] at hcoe
  have hsq : Real.sqrt (1 - ‖y‖ ^ 2) = Real.sqrt (1 - ‖y'‖ ^ 2) := by
    have := congrArg (fun w : E3 => ⟪w, v⟫) hcoe
    simpa only [sphereGraphMap_inner_base hv R y, sphereGraphMap_inner_base hv R y'] using this
  have hnorm : ‖y‖ = ‖y'‖ := by
    have hle : ‖y‖ ≤ 1 := le_of_lt (mem_ball_zero_iff.mp hy)
    have hle' : ‖y'‖ ≤ 1 := le_of_lt (mem_ball_zero_iff.mp hy')
    have h1 : 1 - ‖y‖ ^ 2 = 1 - ‖y'‖ ^ 2 := by
      refine (Real.sqrt_inj ?_ ?_).mp hsq <;> nlinarith [norm_nonneg y, norm_nonneg y', hle, hle']
    have h2 : ‖y‖ ^ 2 = ‖y'‖ ^ 2 := by linarith
    nlinarith [norm_nonneg y, norm_nonneg y']
  have hR : (R y : E3) = (R y' : E3) := by
    have h4 : (R y : E3) + Real.sqrt (1 - ‖y‖ ^ 2) • v =
        (R y' : E3) + Real.sqrt (1 - ‖y'‖ ^ 2) • v := hcoe
    rw [hsq] at h4
    exact add_right_cancel h4
  have hRy : R y = R y' := Subtype.ext hR
  exact R.injective hRy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sphereGraphParametrization_injOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sphereGraphParametrization_injOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sphereGraphParametrization_injOn ``Submission.DifferentialGeometry.Geometry.sphereGraphParametrization_injOn

theorem dIncl_mfderiv_sphereGraphParametrization (hv : ‖v‖ = 1)
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) {y : E2} (hy : ‖y‖ < 1) (z : E2) :
    dIncl (n := 2) (sphereGraphParametrization hv R y)
        (mfderiv 𝓘(ℝ, E2) (𝓡 2) (sphereGraphParametrization hv R) y z) =
      fderiv ℝ (sphereGraphMap (v := v) R) y z := by
  have hyU : y ∈ graphDomain := mem_graphDomain_iff.mpr (mem_ball_zero_iff.mpr hy)
  have hdiffΨ : MDifferentiableAt 𝓘(ℝ, E2) (𝓡 2) (sphereGraphParametrization hv R) y :=
    (contMDiffAt_sphereGraphParametrization hv R hyU).mdifferentiableAt
      (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hdiffι : MDifferentiableAt (𝓡 2) 𝓘(ℝ, E3) ((↑) : _root_.Metric.sphere (0 : E3) 1 → E3)
      (sphereGraphParametrization hv R y) :=
    (contMDiff_coe_sphere (n := 2)).contMDiffAt.mdifferentiableAt
      (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hcomp := mfderiv_comp_apply (I := 𝓘(ℝ, E2)) (I' := 𝓡 2) (I'' := 𝓘(ℝ, E3))
    (f := sphereGraphParametrization hv R) (g := ((↑) : _root_.Metric.sphere (0 : E3) 1 → E3))
    y hdiffι hdiffΨ z
  have hcoe : ((↑) : _root_.Metric.sphere (0 : E3) 1 → E3) ∘ sphereGraphParametrization hv R
      =ᶠ[𝓝 y] sphereGraphMap (v := v) R := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hy)] with w hw
    exact coe_sphereGraphParametrization hv R hw
  rw [mfderiv_eq_fderiv, hcoe.fderiv_eq] at hcomp
  have hkey : dIncl (n := 2) (sphereGraphParametrization hv R y)
      (mfderiv 𝓘(ℝ, E2) (𝓡 2) (sphereGraphParametrization hv R) y z) =
      mfderiv (𝓡 2) 𝓘(ℝ, E3) ((↑) : _root_.Metric.sphere (0 : E3) 1 → E3)
        (sphereGraphParametrization hv R y)
        (mfderiv 𝓘(ℝ, E2) (𝓡 2) (sphereGraphParametrization hv R) y z) := by
    with_unfolding_all rfl
  exact hkey.trans hcomp.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.dIncl_mfderiv_sphereGraphParametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.dIncl_mfderiv_sphereGraphParametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.dIncl_mfderiv_sphereGraphParametrization ``Submission.DifferentialGeometry.Geometry.dIncl_mfderiv_sphereGraphParametrization

private noncomputable def graphBasisIndex : Fin (Module.finrank ℝ E2) ≃ Fin 2 :=
  finCongr (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.graphBasisIndex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.graphBasisIndex target :: scope.openDecls } }

theorem chartModelBasisTwo_apply_index (i : Fin 2) :
    chartModelBasisTwo i =
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E2) (graphBasisIndex.symm i) := by
  rw [chartModelBasisTwo, graphBasisIndex, Basis.reindex_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.chartModelBasisTwo_apply_index then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.chartModelBasisTwo_apply_index"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.chartModelBasisTwo_apply_index ``Submission.DifferentialGeometry.Geometry.chartModelBasisTwo_apply_index

theorem paramGramMatrix_roundMetric_sphereGraphParametrization (hv : ‖v‖ = 1)
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) {y : E2} (hy : ‖y‖ < 1) :
    paramGramMatrix (I := 𝓡 2) (roundMetric (E := E3) (n := 2))
        (sphereGraphParametrization hv R) y =
      Matrix.reindex graphBasisIndex.symm graphBasisIndex.symm
        (sphereGraphGram + (1 - ‖y‖ ^ 2)⁻¹ • Matrix.vecMulVec
          (fun i => ⟪y, (chartModelBasisTwo i : E2)⟫)
          (fun i => ⟪y, (chartModelBasisTwo i : E2)⟫)) := by
  ext i j
  rw [paramGramMatrix_apply, Matrix.reindex_apply, Matrix.submatrix_apply, roundMetric_inner,
    dIncl_mfderiv_sphereGraphParametrization hv R hy,
    dIncl_mfderiv_sphereGraphParametrization hv R hy]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, sphereGraphGram,
    Matrix.of_apply, chartModelBasisTwo_apply_index, Equiv.apply_symm_apply]
  rw [inner_fderiv_sphereGraphMap hv R hy, div_eq_mul_inv]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.paramGramMatrix_roundMetric_sphereGraphParametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.paramGramMatrix_roundMetric_sphereGraphParametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.paramGramMatrix_roundMetric_sphereGraphParametrization ``Submission.DifferentialGeometry.Geometry.paramGramMatrix_roundMetric_sphereGraphParametrization

theorem paramDensity_roundMetric_sphereGraphParametrization (hv : ‖v‖ = 1)
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) {y : E2} (hy : ‖y‖ < 1) :
    paramDensity (I := 𝓡 2) (roundMetric (E := E3) (n := 2))
        (sphereGraphParametrization hv R) y =
      Real.sqrt sphereGraphGram.det * Real.sqrt ((1 - ‖y‖ ^ 2)⁻¹) := by
  have hw : (fun i : Fin 2 => ⟪y, (chartModelBasisTwo i : E2)⟫) =
      sphereGraphGramᵀ *ᵥ (chartModelBasisTwo.repr y) := by
    funext i
    rw [inner_y_chartBasis]
    simp only [dotProduct, Fin.sum_univ_two, Matrix.mulVec, Matrix.transpose_apply]
  have hc : (chartModelBasisTwo.repr y) ⬝ᵥ (sphereGraphGram *ᵥ chartModelBasisTwo.repr y) =
      ‖y‖ ^ 2 := by
    rw [norm_sq_eq_chart y]
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    ring
  have hk : 1 + (1 - ‖y‖ ^ 2)⁻¹ * ‖y‖ ^ 2 = (1 - ‖y‖ ^ 2)⁻¹ := by
    have hne : 1 - ‖y‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg y]
    field_simp
    ring
  rw [paramDensity, paramGramMatrix_roundMetric_sphereGraphParametrization hv R hy,
    Matrix.det_reindex_self, hw, det_add_smul_vecMulVec_transpose_mulVec, hc, hk]
  exact Real.sqrt_mul' _ (inv_nonneg.mpr (by nlinarith [norm_nonneg y]))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.paramDensity_roundMetric_sphereGraphParametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.paramDensity_roundMetric_sphereGraphParametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.paramDensity_roundMetric_sphereGraphParametrization ``Submission.DifferentialGeometry.Geometry.paramDensity_roundMetric_sphereGraphParametrization

private theorem sphereGraphGram_eq_reindex_chartModelBasis :
    sphereGraphGram = Matrix.reindex graphBasisIndex graphBasisIndex
      (Matrix.of fun i j =>
        ⟪(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E2 i : E2),
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E2 j : E2)⟫) := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, sphereGraphGram, Matrix.of_apply,
    Matrix.of_apply, chartModelBasisTwo_apply_index, chartModelBasisTwo_apply_index]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.sphereGraphGram_eq_reindex_chartModelBasis
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.sphereGraphGram_eq_reindex_chartModelBasis target :: scope.openDecls } }

private theorem volume_eq_smul_modelHaar :
    (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E2) =
      ENNReal.ofReal (Real.sqrt sphereGraphGram.det) • modelHaar (E := E2) := by
  have hdet : (Matrix.det (Matrix.of fun i j =>
      ⟪(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E2 i : E2),
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E2 j : E2)⟫)) =
      sphereGraphGram.det := by
    rw [sphereGraphGram_eq_reindex_chartModelBasis, Matrix.det_reindex_self]
  have h := DifferentialGeometry.Integral.Measure.addHaar_withDensity_sqrt_det_gramMatrix_eq_volume
    (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E2)
  rw [← h, modelHaar, _root_.MeasureTheory.withDensity_const, hdet]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.volume_eq_smul_modelHaar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.volume_eq_smul_modelHaar target :: scope.openDecls } }

theorem riemannianVolumeMeasure_roundMetric_sphereGraphParametrization_image_eq (hv : ‖v‖ = 1)
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) :
    riemannianVolumeMeasure (I := 𝓡 2) (M := _root_.Metric.sphere (0 : E3) 1)
        (roundMetric (E := E3) (n := 2)) (sphereGraphParametrization hv R '' _root_.Metric.ball (0 : E2) 1) =
      ∫⁻ y in _root_.Metric.ball (0 : E2) 1, ENNReal.ofReal (Real.sqrt ((1 - ‖y‖ ^ 2)⁻¹))
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E2) := by
  rw [DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_image_eq
    (I := 𝓡 2) (M := _root_.Metric.sphere (0 : E3) 1)
    (roundMetric (E := E3) (n := 2)) _root_.Metric.isOpen_ball measurableSet_ball (Subset.rfl)
    (contMDiffOn_sphereGraphParametrization hv R) (sphereGraphParametrization_injOn hv R)]
  calc ∫⁻ y in _root_.Metric.ball (0 : E2) 1,
        ENNReal.ofReal (paramDensity (I := 𝓡 2) (roundMetric (E := E3) (n := 2))
          (sphereGraphParametrization hv R) y) ∂modelHaar (E := E2)
      = ∫⁻ y in _root_.Metric.ball (0 : E2) 1, ENNReal.ofReal (Real.sqrt sphereGraphGram.det) *
          ENNReal.ofReal (Real.sqrt ((1 - ‖y‖ ^ 2)⁻¹)) ∂modelHaar (E := E2) := by
        refine _root_.MeasureTheory.setLIntegral_congr_fun measurableSet_ball fun y hy => ?_
        rw [paramDensity_roundMetric_sphereGraphParametrization hv R (mem_ball_zero_iff.mp hy),
          ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    _ = ENNReal.ofReal (Real.sqrt sphereGraphGram.det) *
          ∫⁻ y in _root_.Metric.ball (0 : E2) 1, ENNReal.ofReal (Real.sqrt ((1 - ‖y‖ ^ 2)⁻¹))
            ∂modelHaar (E := E2) :=
        _root_.MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ∫⁻ y in _root_.Metric.ball (0 : E2) 1, ENNReal.ofReal (Real.sqrt ((1 - ‖y‖ ^ 2)⁻¹))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E2) := by
        rw [volume_eq_smul_modelHaar, Measure.restrict_smul, _root_.MeasureTheory.lintegral_smul_measure, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianVolumeMeasure_roundMetric_sphereGraphParametrization_image_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianVolumeMeasure_roundMetric_sphereGraphParametrization_image_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianVolumeMeasure_roundMetric_sphereGraphParametrization_image_eq ``Submission.DifferentialGeometry.Geometry.riemannianVolumeMeasure_roundMetric_sphereGraphParametrization_image_eq

private theorem integral_Ioi_tangentDensity :
    ∫ y in _root_.Set.Ioi (0 : ℝ), y * Real.sqrt ((1 - y ^ 2)⁻¹) = 1 := by
  have hderiv : ∀ x ∈ _root_.Set.Ioo (_root_.Min.min (0 : ℝ) (Real.pi / 2)) (_root_.Max.max (0 : ℝ) (Real.pi / 2)),
      HasDerivAt Real.sin (Real.cos x) x := fun x _ => Real.hasDerivAt_sin x
  have hcos : ∀ x ∈ _root_.Set.Ioo (_root_.Min.min (0 : ℝ) (Real.pi / 2)) (_root_.Max.max (0 : ℝ) (Real.pi / 2)),
      0 ≤ Real.cos x := by
    intro x hx
    rw [min_eq_left (by positivity : (0 : ℝ) ≤ Real.pi / 2),
      max_eq_right (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hx
    exact (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩).le
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := Real.pi / 2) (f := Real.sin) (f' := Real.cos)
    (g := fun u : ℝ => u * Real.sqrt ((1 - u ^ 2)⁻¹))
    Real.continuous_sin.continuousOn hderiv hcos
  have hleft : ∫ x in (0 : ℝ)..Real.pi / 2,
        ((fun u : ℝ => u * Real.sqrt ((1 - u ^ 2)⁻¹)) ∘ Real.sin) x * Real.cos x =
      ∫ x in (0 : ℝ)..Real.pi / 2, Real.sin x := by
    refine intervalIntegral.integral_congr_ae ?_
    have hnull : ∀ᵐ x : ℝ, x ≠ Real.pi / 2 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hnull] with x hxne hxI
    simp only [Function.comp_apply]
    rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hxI
    have hx0 : 0 < x := hxI.1
    have hxlt : x < Real.pi / 2 := lt_of_le_of_ne hxI.2 hxne
    have hpos : 0 < Real.cos x :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hx0, Real.pi_pos], hxlt⟩
    have hsq : 1 - Real.sin x ^ 2 = Real.cos x ^ 2 := by
      have := Real.sin_sq_add_cos_sq x
      linarith
    rw [hsq, Real.sqrt_inv, Real.sqrt_sq_eq_abs, abs_of_pos hpos]
    field_simp
  rw [hleft, integral_sin, Real.cos_zero, Real.cos_pi_div_two, sub_zero,
    Real.sin_zero, Real.sin_pi_div_two] at hsub
  have hIoi : ∫ y in _root_.Set.Ioi (0 : ℝ), y * Real.sqrt ((1 - y ^ 2)⁻¹) =
      ∫ y in (0 : ℝ)..1, y * Real.sqrt ((1 - y ^ 2)⁻¹) := by
    rw [intervalIntegral.integral_of_le (f := fun y : ℝ => y * Real.sqrt ((1 - y ^ 2)⁻¹))
        (μ := _root_.MeasureTheory.MeasureSpace.volume) (by norm_num : (0 : ℝ) ≤ 1)]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc,
      ← MeasureTheory.integral_indicator measurableSet_Ioi]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ _root_.Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hy]
      by_cases hy1 : y ∈ _root_.Set.Ioc (0 : ℝ) 1
      · rw [Set.indicator_of_mem hy1]
      · rw [Set.indicator_of_notMem hy1]
        have hge : 1 ≤ y := le_of_not_gt fun hlt => hy1 ⟨hy, hlt.le⟩
        have hneg : 1 - y ^ 2 ≤ 0 := by nlinarith
        rw [Real.sqrt_eq_zero_of_nonpos (inv_nonpos.mpr hneg), _root_.MulZeroClass.mul_zero]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem]
      intro hmem
      exact hy (_root_.Set.Ioc_subset_Ioi_self hmem)
  rw [hIoi, ← hsub]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.integral_Ioi_tangentDensity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.integral_Ioi_tangentDensity target :: scope.openDecls } }

private noncomputable def tangentProfile : ℝ → ℝ :=
  fun r => if r < 1 then Real.sqrt ((1 - r ^ 2)⁻¹) else 0

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.tangentProfile
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.tangentProfile target :: scope.openDecls } }

private theorem tangentProfile_apply_of_lt {r : ℝ} (hr : r < 1) :
    tangentProfile r = Real.sqrt ((1 - r ^ 2)⁻¹) := if_pos hr

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.tangentProfile_apply_of_lt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.tangentProfile_apply_of_lt target :: scope.openDecls } }

private theorem tangentProfile_apply_of_ge {r : ℝ} (hr : 1 ≤ r) : tangentProfile r = 0 :=
  if_neg (not_lt.mpr hr)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.tangentProfile_apply_of_ge
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.tangentProfile_apply_of_ge target :: scope.openDecls } }

private theorem tangentProfile_mul_eq (r : ℝ) :
    r * tangentProfile r = r * Real.sqrt ((1 - r ^ 2)⁻¹) := by
  by_cases h : r < 1
  · rw [tangentProfile_apply_of_lt h]
  · rw [tangentProfile_apply_of_ge (le_of_not_gt h)]
    rcases eq_or_lt_of_le (le_of_not_gt h) with h1 | h1
    · rw [← h1]
      simp
    · have hneg : (1 - r ^ 2)⁻¹ ≤ 0 := inv_nonpos.mpr (by nlinarith)
      rw [Real.sqrt_eq_zero_of_nonpos hneg, _root_.MulZeroClass.mul_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.tangentProfile_mul_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.tangentProfile_mul_eq target :: scope.openDecls } }

private theorem tangentProfile_nonneg (r : ℝ) : 0 ≤ tangentProfile r := by
  by_cases h : r < 1
  · rw [tangentProfile_apply_of_lt h]
    exact Real.sqrt_nonneg _
  · rw [tangentProfile_apply_of_ge (le_of_not_gt h)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.tangentProfile_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.tangentProfile_nonneg target :: scope.openDecls } }

private theorem tangentProfile_measurable : Measurable tangentProfile := by
  refine Measurable.ite measurableSet_Iio ?_ measurable_const
  fun_prop

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.tangentProfile_measurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.tangentProfile_measurable target :: scope.openDecls } }

private theorem integral_tangentProfile :
    ∫ y in _root_.Set.Ioi (0 : ℝ), y * tangentProfile y = 1 := by
  rw [funext tangentProfile_mul_eq]
  exact integral_Ioi_tangentDensity

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.integral_tangentProfile
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.integral_tangentProfile target :: scope.openDecls } }

private theorem volumeReal_ball_one :
    (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E2).real (_root_.Metric.ball (0 : E2) 1) = Real.pi := by
  have hG : Real.Gamma (2 : ℝ) = 1 := by
    have h2 : (2 : ℝ) = ((1 : ℕ) : ℝ) + 1 := by norm_num
    rw [h2, Real.Gamma_nat_eq_factorial]
    norm_num
  have harg : (↑(2 : ℕ) : ℝ) / 2 + 1 = 2 := by norm_num
  rw [Measure.real_def, InnerProductSpace.volume_ball (0 : E2) (1 : ℝ),
    finrank_euclideanSpace_fin, ENNReal.ofReal_one, one_pow, one_mul,
    Real.sq_sqrt Real.pi_pos.le, harg, hG, div_one,
    ENNReal.toReal_ofReal Real.pi_pos.le]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.volumeReal_ball_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.volumeReal_ball_one target :: scope.openDecls } }

private theorem integral_tangentProfile_norm :
    ∫ y : E2, tangentProfile ‖y‖ ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E2) = 2 * Real.pi := by
  have h := MeasureTheory.integral_fun_norm_addHaar (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E2) tangentProfile
  rw [h, volumeReal_ball_one]
  have hfin : Module.finrank ℝ E2 = 2 := finrank_euclideanSpace_fin
  rw [hfin]
  have hprof : (∫ y in _root_.Set.Ioi (0 : ℝ), y ^ (2 - 1) • tangentProfile y) = 1 := by
    have hfun : (fun y : ℝ => y ^ (2 - 1) • tangentProfile y) =
        fun y : ℝ => y * tangentProfile y := by
      funext y
      have h21 : (2 : ℕ) - 1 = 1 := rfl
      rw [h21, pow_one, smul_eq_mul]
    rw [hfun]
    exact integral_tangentProfile
  rw [hprof]
  norm_num

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.integral_tangentProfile_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.integral_tangentProfile_norm target :: scope.openDecls } }

theorem lintegral_sphereGraphDensity_eq :
    ∫⁻ y in _root_.Metric.ball (0 : E2) 1, ENNReal.ofReal (Real.sqrt ((1 - ‖y‖ ^ 2)⁻¹))
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E2) = ENNReal.ofReal (2 * Real.pi) := by
  have hpoint : ∀ y : E2, (_root_.Metric.ball (0 : E2) 1).indicator
      (fun y : E2 => ENNReal.ofReal (Real.sqrt ((1 - ‖y‖ ^ 2)⁻¹))) y =
      ENNReal.ofReal (tangentProfile ‖y‖) := by
    intro y
    by_cases hy : y ∈ _root_.Metric.ball (0 : E2) 1
    · rw [Set.indicator_of_mem hy,
        tangentProfile_apply_of_lt (mem_ball_zero_iff.mp hy)]
    · have hge : 1 ≤ ‖y‖ := by
        rw [mem_ball_zero_iff, not_lt] at hy
        exact hy
      rw [Set.indicator_of_notMem hy, tangentProfile_apply_of_ge hge, ENNReal.ofReal_zero]
  have hind : (fun y : E2 => (_root_.Metric.ball (0 : E2) 1).indicator
        (fun y : E2 => ENNReal.ofReal (Real.sqrt ((1 - ‖y‖ ^ 2)⁻¹))) y) =
      fun y : E2 => ENNReal.ofReal (tangentProfile ‖y‖) := funext hpoint
  rw [← _root_.MeasureTheory.lintegral_indicator measurableSet_ball, hind]
  have hnonneg : 0 ≤ᵐ[_root_.MeasureTheory.MeasureSpace.volume] fun y : E2 => tangentProfile ‖y‖ :=
    Filter.Eventually.of_forall fun y => tangentProfile_nonneg ‖y‖
  have hmeas : _root_.MeasureTheory.AEStronglyMeasurable (fun y : E2 => tangentProfile ‖y‖) volume :=
    (tangentProfile_measurable.comp measurable_norm).aestronglyMeasurable
  have h3 := MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnonneg hmeas
  rw [integral_tangentProfile_norm] at h3
  have hne : (∫⁻ y : E2, ENNReal.ofReal (tangentProfile ‖y‖) ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E2)) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at h3
    have hpos : 0 < 2 * Real.pi := by positivity
    linarith
  rw [← ENNReal.ofReal_toReal hne, h3]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.lintegral_sphereGraphDensity_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.lintegral_sphereGraphDensity_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.lintegral_sphereGraphDensity_eq ``Submission.DifferentialGeometry.Geometry.lintegral_sphereGraphDensity_eq

private theorem sphereGraphParametrization_mem_image (hv : ‖v‖ = 1)
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) {x : _root_.Metric.sphere (0 : E3) 1} (hx : 0 < ⟪(x : E3), v⟫) :
    x ∈ sphereGraphParametrization hv R '' _root_.Metric.ball (0 : E2) 1 := by
  have hxnorm : ‖(x : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  set p : E3 := (x : E3) - ⟪(x : E3), v⟫ • v with hp
  have hpv : ⟪p, v⟫ = 0 := by
    rw [hp, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_mul_norm, hv, mul_one]
    ring
  have hpmem : p ∈ (ℝ ∙ v)ᗮ := Submodule.mem_orthogonal_singleton_iff_inner_left.mpr hpv
  set y : E2 := R.symm ⟨p, hpmem⟩ with hy
  have hRy : (R y : E3) = p := by
    have h1 : R y = (⟨p, hpmem⟩ : (ℝ ∙ v)ᗮ) := R.apply_symm_apply ⟨p, hpmem⟩
    exact congrArg Subtype.val h1
  have hynorm : ‖y‖ = ‖p‖ := by
    rw [← R.norm_map y]
    exact congrArg (fun z : E3 => ‖z‖) hRy
  have hdecomp : (x : E3) = p + ⟪(x : E3), v⟫ • v := by
    rw [hp]
    abel
  have hinner : ⟪p, ⟪(x : E3), v⟫ • v⟫ = 0 := by
    rw [real_inner_smul_right, hpv, _root_.MulZeroClass.mul_zero]
  have hsq : 1 = ‖y‖ ^ 2 + ⟪(x : E3), v⟫ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      p (⟪(x : E3), v⟫ • v) hinner
    rw [← hdecomp] at h
    rw [← hynorm] at h
    rw [norm_smul, Real.norm_eq_abs, hv, mul_one, abs_of_pos hx] at h
    nlinarith [h, hxnorm]
  have hlt : ‖y‖ < 1 := by
    have hpos : 0 < ⟪(x : E3), v⟫ ^ 2 := pow_pos hx 2
    nlinarith [norm_nonneg y]
  have hsqrt : Real.sqrt (1 - ‖y‖ ^ 2) = ⟪(x : E3), v⟫ := by
    have h1 : 1 - ‖y‖ ^ 2 = ⟪(x : E3), v⟫ ^ 2 := by linarith [hsq]
    rw [h1, Real.sqrt_sq hx.le]
  refine ⟨y, mem_ball_zero_iff.mpr hlt, ?_⟩
  refine Subtype.ext ?_
  rw [coe_sphereGraphParametrization hv R (mem_ball_zero_iff.mpr hlt), sphereGraphMap, hRy, hsqrt]
  exact hdecomp.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.sphereGraphParametrization_mem_image
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.sphereGraphParametrization_mem_image target :: scope.openDecls } }

private theorem sphereGraphParametrization_image_subset (hv : ‖v‖ = 1)
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) :
    sphereGraphParametrization hv R '' _root_.Metric.ball (0 : E2) 1 ⊆
      {x : _root_.Metric.sphere (0 : E3) 1 | 0 < ⟪(x : E3), v⟫} := by
  rintro x ⟨y, hy, rfl⟩
  change 0 < ⟪(sphereGraphParametrization hv R y : E3), v⟫
  rw [coe_sphereGraphParametrization hv R hy, sphereGraphMap_inner_base hv R y]
  exact Real.sqrt_pos.mpr (by
    have := mem_ball_zero_iff.mp hy
    nlinarith [norm_nonneg y])

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.sphereGraphParametrization_image_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.sphereGraphParametrization_image_subset target :: scope.openDecls } }

private theorem sphereGraphParametrization_image_eq (hv : ‖v‖ = 1)
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) :
    sphereGraphParametrization hv R '' _root_.Metric.ball (0 : E2) 1 =
      {x : _root_.Metric.sphere (0 : E3) 1 | 0 < ⟪(x : E3), v⟫} :=
  Set.Subset.antisymm (sphereGraphParametrization_image_subset hv R)
    fun _ hx => sphereGraphParametrization_mem_image hv R hx

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.sphereGraphParametrization_image_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.sphereGraphParametrization_image_eq target :: scope.openDecls } }

private theorem measurableSet_sphereGraphParametrization_image (hv : ‖v‖ = 1)
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) :
    MeasurableSet (sphereGraphParametrization hv R '' _root_.Metric.ball (0 : E2) 1) := by
  rw [sphereGraphParametrization_image_eq hv R]
  have hcont : Continuous (fun x : _root_.Metric.sphere (0 : E3) 1 => ⟪(x : E3), v⟫) :=
    continuous_subtype_val.inner continuous_const
  exact (isOpen_lt continuous_const hcont).measurableSet

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.measurableSet_sphereGraphParametrization_image
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.measurableSet_sphereGraphParametrization_image target :: scope.openDecls } }

theorem riemannianVolumeMeasure_roundMetric_sphereGraphParametrization_image_eq_two_pi
    (hv : ‖v‖ = 1) (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) :
    riemannianVolumeMeasure (I := 𝓡 2) (M := _root_.Metric.sphere (0 : E3) 1)
        (roundMetric (E := E3) (n := 2)) (sphereGraphParametrization hv R '' _root_.Metric.ball (0 : E2) 1) =
      ENNReal.ofReal (2 * Real.pi) := by
  rw [riemannianVolumeMeasure_roundMetric_sphereGraphParametrization_image_eq hv R,
    lintegral_sphereGraphDensity_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianVolumeMeasure_roundMetric_sphereGraphParametrization_image_eq_two_pi then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianVolumeMeasure_roundMetric_sphereGraphParametrization_image_eq_two_pi"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianVolumeMeasure_roundMetric_sphereGraphParametrization_image_eq_two_pi ``Submission.DifferentialGeometry.Geometry.riemannianVolumeMeasure_roundMetric_sphereGraphParametrization_image_eq_two_pi

theorem riemannianVolumeMeasure_roundMetric_sphereGraphParametrization_image_neg_eq_two_pi
    (hv' : ‖(-v : E3)‖ = 1) (R' : E2 ≃ₗᵢ[ℝ] (ℝ ∙ ((-v : E3)))ᗮ) :
    riemannianVolumeMeasure (I := 𝓡 2) (M := _root_.Metric.sphere (0 : E3) 1) (roundMetric (E := E3) (n := 2))
        (sphereGraphParametrization (v := -v) hv' R' '' _root_.Metric.ball (0 : E2) 1) =
      ENNReal.ofReal (2 * Real.pi) := by
  rw [riemannianVolumeMeasure_roundMetric_sphereGraphParametrization_image_eq (v := -v) hv' R',
    lintegral_sphereGraphDensity_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianVolumeMeasure_roundMetric_sphereGraphParametrization_image_neg_eq_two_pi then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianVolumeMeasure_roundMetric_sphereGraphParametrization_image_neg_eq_two_pi"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianVolumeMeasure_roundMetric_sphereGraphParametrization_image_neg_eq_two_pi ``Submission.DifferentialGeometry.Geometry.riemannianVolumeMeasure_roundMetric_sphereGraphParametrization_image_neg_eq_two_pi

end DifferentialGeometry.Geometry
