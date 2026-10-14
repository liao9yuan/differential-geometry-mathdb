import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Metric
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.MetricData
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Filter
open scoped _root_.Topology _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

local instance angularOneNormedAddCommGroup : NormedAddCommGroup (V →L[ℝ] ℝ) := inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.angularOneNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.angularOneNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.angularOneNormedAddCommGroup ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.angularOneNormedAddCommGroup
local instance angularOneNormedSpace : NormedSpace ℝ (V →L[ℝ] ℝ) := inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.angularOneNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.angularOneNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.angularOneNormedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.angularOneNormedSpace
local instance angularTwoNormedAddCommGroup : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
  inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.angularTwoNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.angularTwoNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.angularTwoNormedAddCommGroup ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.angularTwoNormedAddCommGroup
local instance angularTwoNormedSpace : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.angularTwoNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.angularTwoNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.angularTwoNormedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.angularTwoNormedSpace
local instance productOneNormedAddCommGroup : NormedAddCommGroup ((ℝ × V) →L[ℝ] ℝ) :=
  inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.productOneNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.productOneNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.productOneNormedAddCommGroup ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.productOneNormedAddCommGroup
local instance productOneNormedSpace : NormedSpace ℝ ((ℝ × V) →L[ℝ] ℝ) := inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.productOneNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.productOneNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.productOneNormedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.productOneNormedSpace
local instance productTwoNormedAddCommGroup :
    NormedAddCommGroup ((ℝ × V) →L[ℝ] (ℝ × V) →L[ℝ] ℝ) := inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.productTwoNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.productTwoNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.productTwoNormedAddCommGroup ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.productTwoNormedAddCommGroup
local instance productTwoNormedSpace :
    NormedSpace ℝ ((ℝ × V) →L[ℝ] (ℝ × V) →L[ℝ] ℝ) := inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.productTwoNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.productTwoNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.productTwoNormedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.productTwoNormedSpace


def coneAngularForm (B : V →L[ℝ] V →L[ℝ] ℝ) :
    (ℝ × V) →L[ℝ] (ℝ × V) →L[ℝ] ℝ :=
  (ContinuousLinearMap.precomp ℝ (ContinuousLinearMap.snd ℝ ℝ V)).comp
    (B.comp (ContinuousLinearMap.snd ℝ ℝ V))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneAngularForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneAngularForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneAngularForm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneAngularForm

@[simp] theorem coneAngularForm_apply (B : V →L[ℝ] V →L[ℝ] ℝ)
    (v w : ℝ × V) : coneAngularForm B v w = B v.2 w.2 := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneAngularForm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneAngularForm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneAngularForm_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneAngularForm_apply


def coneForm (h : V → V →L[ℝ] V →L[ℝ] ℝ) (z : ℝ × V) :
    (ℝ × V) →L[ℝ] (ℝ × V) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ V).smulRight (ContinuousLinearMap.fst ℝ ℝ V) +
    z.1 ^ 2 • coneAngularForm (h z.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneForm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneForm

@[simp] theorem coneForm_apply (h : V → V →L[ℝ] V →L[ℝ] ℝ)
    (z v w : ℝ × V) :
    coneForm h z v w = v.1 * w.1 + z.1 ^ 2 * h z.2 v.2 w.2 := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneForm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneForm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneForm_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneForm_apply

theorem coneForm_differentiableAt
    {h : V → V →L[ℝ] V →L[ℝ] ℝ} {z : ℝ × V}
    (hh : DifferentiableAt ℝ h z.2) : DifferentiableAt ℝ (coneForm h) z := by
  have ha : DifferentiableAt ℝ (fun y : ℝ × V => coneAngularForm (h y.2)) z :=
    (differentiableAt_const _).clm_comp
      ((hh.comp z differentiableAt_snd).clm_comp (differentiableAt_const _))
  exact (differentiableAt_const _).add ((differentiableAt_fst.pow 2).smul ha)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneForm_differentiableAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneForm_differentiableAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneForm_differentiableAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneForm_differentiableAt


theorem fderiv_coneForm_apply
    {h : V → V →L[ℝ] V →L[ℝ] ℝ} {z : ℝ × V}
    (hh : DifferentiableAt ℝ h z.2) (v w u : ℝ × V) :
    fderiv ℝ (coneForm h) z v w u =
      2 * z.1 * v.1 * h z.2 w.2 u.2 +
        z.1 ^ 2 * fderiv ℝ h z.2 v.2 w.2 u.2 := by
  have hw : HasFDerivAt (fun _ : ℝ × V => w) 0 z :=
    hasFDerivAt_const (𝕜 := ℝ) w z
  have hu : HasFDerivAt (fun _ : ℝ × V => u) 0 z :=
    hasFDerivAt_const (𝕜 := ℝ) u z
  have heval := ((coneForm_differentiableAt hh).hasFDerivAt.clm_apply hw).clm_apply hu
  have heq : fderiv ℝ (fun y : ℝ × V => coneForm h y w u) z v =
      fderiv ℝ (coneForm h) z v w u := by
    simpa using DFunLike.congr_fun heval.fderiv v
  have hc : HasFDerivAt (fun y : ℝ × V => h y.2)
      ((fderiv ℝ h z.2).comp (ContinuousLinearMap.snd ℝ ℝ V)) z :=
    hh.hasFDerivAt.comp z (hasFDerivAt_snd (𝕜 := ℝ) (p := z))
  have hfirst := hc.clm_apply (hasFDerivAt_const (𝕜 := ℝ) w.2 z)
  have hangular := hfirst.clm_apply (hasFDerivAt_const (𝕜 := ℝ) u.2 z)
  have hformula := (hasFDerivAt_const (𝕜 := ℝ) (w.1 * u.1) z).add
    (((hasFDerivAt_fst (𝕜 := ℝ) (p := z)).pow 2).mul hangular)
  simp only [coneForm_apply] at heq
  erw [hformula.fderiv] at heq
  simpa [mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm, add_comm] using heq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.fderiv_coneForm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.fderiv_coneForm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.fderiv_coneForm_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.fderiv_coneForm_apply


theorem koszulCov_coneForm_radial
    {h : V → V →L[ℝ] V →L[ℝ] ℝ} {z : ℝ × V}
    (hh : DifferentiableAt ℝ h z.2) (v u : ℝ × V) :
    MetricKoszul.koszulCov (fderiv ℝ (coneForm h) z) v (1, 0) u =
      z.1 * h z.2 v.2 u.2 := by
  rw [MetricKoszul.koszul_cov_apply]
  simp only [fderiv_coneForm_apply hh, map_zero,
    zero_apply, _root_.MulZeroClass.mul_zero, zero_add, add_zero, mul_one, sub_zero]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.koszulCov_coneForm_radial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.koszulCov_coneForm_radial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.koszulCov_coneForm_radial ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.koszulCov_coneForm_radial

theorem koszulCov_coneForm_radial_eq
    {h : V → V →L[ℝ] V →L[ℝ] ℝ} {z : ℝ × V}
    (hh : DifferentiableAt ℝ h z.2) (hr : z.1 ≠ 0) (v : ℝ × V) :
    MetricKoszul.koszulCov (fderiv ℝ (coneForm h) z) v (1, 0) =
      coneForm h z (0, z.1⁻¹ • v.2) := by
  apply ContinuousLinearMap.ext
  intro u
  rw [koszulCov_coneForm_radial hh, coneForm_apply]
  simp only [_root_.MulZeroClass.zero_mul, zero_add, map_smul, smul_apply, smul_eq_mul]
  field_simp [hr]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.koszulCov_coneForm_radial_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.koszulCov_coneForm_radial_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.koszulCov_coneForm_radial_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.koszulCov_coneForm_radial_eq

variable [FiniteDimensional ℝ V]

theorem leviCivita_radial_of_coneForm
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ × V) (ℝ × V))
    {h : V → V →L[ℝ] V →L[ℝ] ℝ} {z : ℝ × V}
    (hmetric : (fun y => tangentBilinearFormToModel y (g.inner y)) =ᶠ[𝓝 z]
      coneForm h)
    (hh : DifferentiableAt ℝ h z.2) (hr : z.1 ≠ 0) (v : ℝ × V) :
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, ℝ × V)) z
      ((leviCivitaConnectionOfMetric (I := 𝓘(ℝ, ℝ × V)) g
        (constantModelVectorField (1, 0)) z)
          ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, ℝ × V)) z).symm v)) =
      (0, z.1⁻¹ • v.2) := by
  let e := tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, ℝ × V)) z
  let a := (leviCivitaConnectionOfMetric (I := 𝓘(ℝ, ℝ × V)) g
    (constantModelVectorField (1, 0)) z) (e.symm v)
  have hflat := const_flat_eq_nhds g (coneForm h) hmetric
    (coneForm_differentiableAt hh) v (1, 0)
  rw [koszulCov_coneForm_radial_eq hh hr] at hflat
  have hmetric0 := hmetric.self_of_nhds
  have ha : a = e.symm (0, z.1⁻¹ • v.2) := by
    apply tangentFlatLinear_injective_gen (I := 𝓘(ℝ, ℝ × V)) g z
    ext w
    have hpair := DFunLike.congr_fun hflat (e w)
    rw [← hmetric0, tangentBilinearFormToModel_apply,
      tangentBilinearFormToModel_apply] at hpair
    simpa only [e, a, ContinuousLinearEquiv.symm_apply_apply,
      tangentFlatLinear_apply_gen] using hpair
  change e a = _
  rw [ha, e.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.leviCivita_radial_of_coneForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.leviCivita_radial_of_coneForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.leviCivita_radial_of_coneForm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.leviCivita_radial_of_coneForm


def coneEulerField (z : ℝ × V) : TangentSpace 𝓘(ℝ, ℝ × V) z :=
  z.1 • constantModelVectorField (1, 0) z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneEulerField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneEulerField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneEulerField ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneEulerField

omit [FiniteDimensional ℝ V] in
theorem coneEulerField_contMDiff :
    ContMDiff 𝓘(ℝ, ℝ × V) (𝓘(ℝ, ℝ × V).tangent) ∞
      (T% (coneEulerField (V := V))) := by
  apply contMDiff_vectorSpace_iff_contDiff.mpr
  exact contDiff_fst.smul contDiff_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneEulerField_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneEulerField_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneEulerField_contMDiff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.coneEulerField_contMDiff


theorem leviCivita_coneEuler_of_coneForm
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ × V) (ℝ × V))
    {h : V → V →L[ℝ] V →L[ℝ] ℝ} {z : ℝ × V}
    (hmetric : (fun y => tangentBilinearFormToModel y (g.inner y)) =ᶠ[𝓝 z]
      coneForm h)
    (hh : DifferentiableAt ℝ h z.2) (hr : z.1 ≠ 0)
    (v : TangentSpace 𝓘(ℝ, ℝ × V) z) :
    (leviCivitaConnectionOfMetric (I := 𝓘(ℝ, ℝ × V)) g
      (coneEulerField (V := V)) z) v = v := by
  let e := tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, ℝ × V)) z
  let vModel : ℝ × V := e v
  have hrad : ContMDiff 𝓘(ℝ, ℝ × V) (𝓘(ℝ, ℝ × V).tangent) ∞
      (T% (constantModelVectorField (𝕜 := ℝ) ((1 : ℝ), (0 : V)))) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hleib :=
    (leviCivitaConnectionOfMetric (I := 𝓘(ℝ, ℝ × V)) g).isCovariantDerivativeOnUniv.leibniz
      (x := z) (g := fun y : ℝ × V => y.1)
      (hrad.contMDiffAt.mdifferentiableAt (by simp))
      (differentiableAt_fst.mdifferentiableAt)
  have hradial : (leviCivitaConnectionOfMetric (I := 𝓘(ℝ, ℝ × V)) g
      (constantModelVectorField (1, 0)) z) v = e.symm (0, z.1⁻¹ • vModel.2) := by
    apply e.injective
    simpa only [vModel, e, ContinuousLinearEquiv.symm_apply_apply,
      ContinuousLinearEquiv.apply_symm_apply] using
      leviCivita_radial_of_coneForm g hmetric hh hr vModel
  have hdf : mvfderiv (I := 𝓘(ℝ, ℝ × V)) (fun y : ℝ × V => y.1) z v = vModel.1 := by
    rw [mvfderiv_model_apply_eq_fderiv, (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).fderiv]
    rfl
  have hEuler : coneEulerField (V := V) =
      (fun y : ℝ × V => y.1) • constantModelVectorField ((1 : ℝ), (0 : V)) := rfl
  rw [hEuler, hleib]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, hdf]
  rw [hradial]
  apply e.injective
  simp only [map_add, map_smul, ContinuousLinearEquiv.apply_symm_apply]
  change z.1 • (0, z.1⁻¹ • vModel.2) + vModel.1 • (1, (0 : V)) = vModel
  ext <;> simp [smul_smul, hr]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.leviCivita_coneEuler_of_coneForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.leviCivita_coneEuler_of_coneForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.leviCivita_coneEuler_of_coneForm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.leviCivita_coneEuler_of_coneForm

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
