import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Parametric.AreaFormula
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Euclidean
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.MetricComparison
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Metric _root_.Set _root_.Module _root_.Submission.Module _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Integral.Measure (paramDensity paramGramMatrix paramGramMatrix_apply
  modelHaar riemannianVolumeMeasure)
open scoped _root_.Manifold _root_.ContDiff _root_.RealInnerProductSpace _root_.ENNReal _root_.Topology _root_.Matrix

namespace DifferentialGeometry.Geometry

section MatrixDet

open _root_.Matrix
open scoped _root_.MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma eigenvalues_le_of_rayleigh
    {A : Matrix ι ι Real} {a : Real} (hA : A.IsHermitian)
    (hray : ∀ v : EuclideanSpace Real ι, ‖v‖ = 1 →
      RCLike.re (dotProduct (_root_.Star.star ⇑v) (Matrix.mulVec A ⇑v)) ≤ a) :
    ∀ i, hA.eigenvalues i ≤ a := by
  intro i
  rw [hA.eigenvalues_eq i]
  exact hray (hA.eigenvectorBasis i) (hA.eigenvectorBasis.norm_eq_one i)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.eigenvalues_le_of_rayleigh
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.eigenvalues_le_of_rayleigh target :: scope.openDecls } }

private lemma det_le_one_of_rayleigh
    {A : Matrix ι ι Real} (hA : A.PosSemidef)
    (hray : ∀ v : EuclideanSpace Real ι, ‖v‖ = 1 →
      RCLike.re (dotProduct (_root_.Star.star ⇑v) (Matrix.mulVec A ⇑v)) ≤ 1) :
    A.det ≤ 1 := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  refine Finset.prod_le_one (fun i _ ↦ ?_) (fun i _ ↦ ?_)
  · exact_mod_cast hA.eigenvalues_nonneg i
  · exact_mod_cast eigenvalues_le_of_rayleigh hA.isHermitian hray i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.det_le_one_of_rayleigh
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.det_le_one_of_rayleigh target :: scope.openDecls } }

private lemma det_le_one_of_dotProduct
    {A : Matrix ι ι Real} (hA : A.PosSemidef)
    (hray : ∀ x : ι → Real, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ x) :
    A.det ≤ 1 := by
  refine det_le_one_of_rayleigh hA (fun v hv ↦ ?_)
  have hnorm : (⇑v : ι → Real) ⬝ᵥ ⇑v = 1 := by
    have h1 := EuclideanSpace.inner_eq_star_dotProduct (𝕜 := Real) v v
    rw [_root_.TrivialStar.star_trivial] at h1
    have h2 : (⇑v : ι → Real) ⬝ᵥ ⇑v = ‖v‖ ^ 2 := by
      rw [← h1]
      exact real_inner_self_eq_norm_sq v
    rw [h2, hv, one_pow]
  simp only [_root_.TrivialStar.star_trivial, RCLike.re_to_real]
  exact (hray ⇑v).trans hnorm.le

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.det_le_one_of_dotProduct
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.det_le_one_of_dotProduct target :: scope.openDecls } }

private lemma det_le_of_quad_le
    {A B : Matrix ι ι Real} (hA : A.PosSemidef) (hB : B.PosDef)
    (hAB : ∀ x : ι → Real, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x)) :
    A.det ≤ B.det := by
  classical
  have quad_symm : ∀ (S : Matrix ι ι Real), Sᵀ = S → ∀ x z : ι → Real,
      x ⬝ᵥ (S *ᵥ z) = (S *ᵥ x) ⬝ᵥ z := by
    intro S hS x z
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS]
  set P := CFC.sqrt B with hP_def
  have hP_nonneg : (0 : Matrix ι ι Real) ≤ P := by
    rw [hP_def]
    exact CFC.sqrt_nonneg B
  have hP_psd : P.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hP_nonneg
  have hP_herm : Pᴴ = P := hP_psd.isHermitian
  have hPsymm : Pᵀ = P := by
    ext i j
    simpa [Matrix.transpose_apply, _root_.TrivialStar.star_trivial] using hP_psd.isHermitian.apply i j
  have hPP : P * P = B := by
    rw [hP_def]
    exact CFC.sqrt_mul_sqrt_self B (Matrix.nonneg_iff_posSemidef.mpr hB.posSemidef)
  have hdetB_pos : 0 < B.det := hB.det_pos
  have hdetPP : P.det * P.det = B.det := by rw [← Matrix.det_mul, hPP]
  have hdetP_ne : P.det ≠ 0 := fun h0 ↦
    hdetB_pos.ne' (by rw [← hdetPP, h0, _root_.MulZeroClass.zero_mul])
  have hdetP_unit : IsUnit P.det := isUnit_iff_ne_zero.mpr hdetP_ne
  have hPinv_r : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdetP_unit
  have hPinv_l : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdetP_unit
  have hPinvsymm : (P⁻¹)ᵀ = P⁻¹ := by rw [Matrix.transpose_nonsing_inv, hPsymm]
  have hC_psd : (P⁻¹ * A * P⁻¹).PosSemidef := by
    have h := hA.conjTranspose_mul_mul_same P⁻¹
    rwa [Matrix.conjTranspose_nonsing_inv, hP_herm] at h
  have hC_ray : ∀ x : ι → Real,
      x ⬝ᵥ ((P⁻¹ * A * P⁻¹) *ᵥ x) ≤ x ⬝ᵥ x := by
    intro x
    have hPw : P *ᵥ (P⁻¹ *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, hPinv_r, Matrix.one_mulVec]
    have e1 : x ⬝ᵥ ((P⁻¹ * A * P⁻¹) *ᵥ x) =
        (P⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ (P⁻¹ *ᵥ x)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact quad_symm P⁻¹ hPinvsymm x (A *ᵥ (P⁻¹ *ᵥ x))
    have e3 : (P⁻¹ *ᵥ x) ⬝ᵥ (B *ᵥ (P⁻¹ *ᵥ x)) = x ⬝ᵥ x := by
      rw [← hPP, ← Matrix.mulVec_mulVec,
        quad_symm P hPsymm (P⁻¹ *ᵥ x) (P *ᵥ (P⁻¹ *ᵥ x)), hPw]
    calc
      x ⬝ᵥ ((P⁻¹ * A * P⁻¹) *ᵥ x) =
          (P⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ (P⁻¹ *ᵥ x)) := e1
      _ ≤ (P⁻¹ *ᵥ x) ⬝ᵥ (B *ᵥ (P⁻¹ *ᵥ x)) := hAB (P⁻¹ *ᵥ x)
      _ = x ⬝ᵥ x := e3
  have hdetC : (P⁻¹ * A * P⁻¹).det ≤ 1 :=
    det_le_one_of_dotProduct hC_psd hC_ray
  have hACM : P * (P⁻¹ * A * P⁻¹) * P = A := by
    rw [show P * (P⁻¹ * A * P⁻¹) * P =
      (P * P⁻¹) * A * (P⁻¹ * P) by simp only [mul_assoc]]
    rw [hPinv_r, hPinv_l, one_mul, mul_one]
  have hdetA : A.det = B.det * (P⁻¹ * A * P⁻¹).det := by
    have hcongr := congrArg Matrix.det hACM
    rw [Matrix.det_mul, Matrix.det_mul] at hcongr
    rw [← hcongr, ← hdetPP]
    ring
  rw [hdetA]
  exact mul_le_of_le_one_right hdetB_pos.le hdetC

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.det_le_of_quad_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.det_le_of_quad_le target :: scope.openDecls } }

end MatrixDet

variable {n : ℕ}

private instance ballVolumeBoundFact (n : ℕ) :
    Fact (_root_.Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.ballVolumeBoundFact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.ballVolumeBoundFact target :: scope.openDecls } }

private local instance ballVolumeBoundMeasurable (n : ℕ) :
    MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.ballVolumeBoundMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.ballVolumeBoundMeasurable target :: scope.openDecls } }
private local instance ballVolumeBoundBorel (n : ℕ) :
    BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.ballVolumeBoundBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.ballVolumeBoundBorel target :: scope.openDecls } }

private def graphMap {v : EuclideanSpace ℝ (Fin (n + 1))}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  (R y : EuclideanSpace ℝ (Fin (n + 1))) + Real.sqrt (1 - ‖y‖ ^ 2) • v

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.graphMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.graphMap target :: scope.openDecls } }

private theorem graphMap_mem_sphere {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : ‖v‖ = 1)
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) {y : EuclideanSpace ℝ (Fin n)}
    (hy : ‖y‖ < 1) : graphMap R y ∈ _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  have h0 : ⟪(R y : EuclideanSpace ℝ (Fin (n + 1))), v⟫ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp (R y).property
  have hnorm : ‖(R y : EuclideanSpace ℝ (Fin (n + 1)))‖ = ‖y‖ := by
    rw [← Submodule.coe_norm, R.norm_map]
  have h1 : 0 ≤ 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
  have horth : ⟪(R y : EuclideanSpace ℝ (Fin (n + 1))), Real.sqrt (1 - ‖y‖ ^ 2) • v⟫ = 0 := by
    rw [real_inner_smul_right, h0, _root_.MulZeroClass.mul_zero]
  have h2 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (R y : EuclideanSpace ℝ (Fin (n + 1))) (Real.sqrt (1 - ‖y‖ ^ 2) • v) horth
  have h3 : ‖graphMap R y‖ ^ 2 = 1 := by
    rw [graphMap, sq, h2, hnorm, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), hv, mul_one, Real.mul_self_sqrt h1]
    ring
  rw [mem_sphere_zero_iff_norm]
  nlinarith [norm_nonneg (graphMap R y)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.graphMap_mem_sphere
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.graphMap_mem_sphere target :: scope.openDecls } }

private theorem contDiffAt_graphMap {v : EuclideanSpace ℝ (Fin (n + 1))}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) {y : EuclideanSpace ℝ (Fin n)}
    (hy : ‖y‖ < 1) : ContDiffAt ℝ ∞ (graphMap R) y := by
  have hpos : 0 < 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
  have hR : ContDiffAt ℝ ∞
      (fun z : EuclideanSpace ℝ (Fin n) => (R z : EuclideanSpace ℝ (Fin (n + 1)))) y :=
    ((Submodule.subtypeL (ℝ ∙ v)ᗮ).contDiff.comp R.contDiff).contDiffAt
  have hsq : ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2) y :=
    (contDiff_norm_sq ℝ).contDiffAt
  have hsqrt : ContDiffAt ℝ ∞
      (fun z : EuclideanSpace ℝ (Fin n) => Real.sqrt (1 - ‖z‖ ^ 2)) y :=
    (contDiffAt_const.sub hsq).sqrt (by positivity)
  exact hR.add (hsqrt.smul contDiffAt_const)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.contDiffAt_graphMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.contDiffAt_graphMap target :: scope.openDecls } }

private def graphParam {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : ‖v‖ = 1)
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) :
    EuclideanSpace ℝ (Fin n) → _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  fun y => by
    classical
    exact if hy : ‖y‖ < 1 then ⟨graphMap R y, graphMap_mem_sphere hv R hy⟩
      else ⟨v, mem_sphere_zero_iff_norm.mpr hv⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.graphParam
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.graphParam target :: scope.openDecls } }

private theorem coe_graphParam {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : ‖v‖ = 1)
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) {y : EuclideanSpace ℝ (Fin n)}
    (hy : ‖y‖ < 1) :
    (graphParam hv R y : EuclideanSpace ℝ (Fin (n + 1))) = graphMap R y := by
  rw [graphParam, dif_pos hy]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.coe_graphParam
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.coe_graphParam target :: scope.openDecls } }

private def graphDomain (n : ℕ) : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) :=
  ⟨ball 0 1, isOpen_ball⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.graphDomain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.graphDomain target :: scope.openDecls } }

private theorem contMDiffAt_graphParam {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : ‖v‖ = 1)
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ graphDomain n) :
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ (graphParam hv R) y := by
  have hmem : ∀ z : graphDomain n, ‖(z : EuclideanSpace ℝ (Fin n))‖ < 1 :=
    fun z => mem_ball_zero_iff.mp z.2
  have hamb : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
      (fun z : graphDomain n => graphMap R (z : EuclideanSpace ℝ (Fin n))) := by
    intro z
    exact (contMDiffAt_subtype_iff (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) (U := graphDomain n)
      (f := graphMap R)).mpr (contDiffAt_graphMap R (hmem z)).contMDiffAt
  have hcod := ContMDiff.codRestrict_sphere (n := n) hamb
    (fun z => graphMap_mem_sphere hv R (hmem z))
  have heq : (fun z : graphDomain n => graphParam hv R (z : EuclideanSpace ℝ (Fin n))) =
      Set.codRestrict (fun z : graphDomain n => graphMap R (z : EuclideanSpace ℝ (Fin n))) _
        (fun z => graphMap_mem_sphere hv R (hmem z)) := by
    funext z
    exact Subtype.ext (coe_graphParam hv R (hmem z))
  have hsub : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞
      (fun z : graphDomain n => graphParam hv R (z : EuclideanSpace ℝ (Fin n))) ⟨y, hy⟩ := by
    rw [heq]
    exact hcod ⟨y, hy⟩
  exact (contMDiffAt_subtype_iff (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (I' := 𝓡 n)
    (U := graphDomain n) (f := graphParam hv R) (x := ⟨y, hy⟩)).mp hsub

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.contMDiffAt_graphParam
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.contMDiffAt_graphParam target :: scope.openDecls } }

private theorem contMDiffOn_graphParam {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : ‖v‖ = 1)
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) 1 (graphParam hv R) (_root_.Metric.ball 0 1) :=
  fun _ hy => ((contMDiffAt_graphParam hv R hy).contMDiffWithinAt).of_le (by simp)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.contMDiffOn_graphParam
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.contMDiffOn_graphParam target :: scope.openDecls } }

private def graphProj {v : EuclideanSpace ℝ (Fin (n + 1))}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  R.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (ℝ ∙ v)ᗮ.orthogonalProjectionOnto

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.graphProj
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.graphProj target :: scope.openDecls } }

private theorem graphProj_graphMap {v : EuclideanSpace ℝ (Fin (n + 1))}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (y : EuclideanSpace ℝ (Fin n)) :
    graphProj R (graphMap R y) = y := by
  simp [graphProj, graphMap]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.graphProj_graphMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.graphProj_graphMap target :: scope.openDecls } }

private theorem norm_graphProj_le {v : EuclideanSpace ℝ (Fin (n + 1))}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) (w : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖graphProj R w‖ ≤ ‖w‖ := by
  change ‖R.symm ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto w)‖ ≤ ‖w‖
  rw [LinearIsometryEquiv.norm_map]
  exact (ℝ ∙ v)ᗮ.norm_orthogonalProjectionOnto_apply_le w

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.norm_graphProj_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.norm_graphProj_le target :: scope.openDecls } }

private theorem norm_le_norm_fderiv_graphMap {v : EuclideanSpace ℝ (Fin (n + 1))}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) {y : EuclideanSpace ℝ (Fin n)}
    (hy : ‖y‖ < 1) (z : EuclideanSpace ℝ (Fin n)) :
    ‖z‖ ≤ ‖fderiv ℝ (graphMap R) y z‖ := by
  have hG : HasFDerivAt (graphMap R) (fderiv ℝ (graphMap R) y) y :=
    ((contDiffAt_graphMap R hy).differentiableAt (by simp)).hasFDerivAt
  have hcomp := (graphProj R).hasFDerivAt.comp y hG
  have hid : HasFDerivAt (graphProj R ∘ graphMap R)
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) y := by
    have hfun : graphProj R ∘ graphMap R = id := funext (graphProj_graphMap R)
    rw [hfun]
    exact hasFDerivAt_id y
  have huniq := hcomp.unique hid
  have hz : graphProj R (fderiv ℝ (graphMap R) y z) = z := by
    have := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => L z)
      huniq
    simpa using this
  calc ‖z‖ = ‖graphProj R (fderiv ℝ (graphMap R) y z)‖ := by rw [hz]
    _ ≤ ‖fderiv ℝ (graphMap R) y z‖ := norm_graphProj_le R _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.norm_le_norm_fderiv_graphMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.norm_le_norm_fderiv_graphMap target :: scope.openDecls } }

private theorem dIncl_mfderiv_graphParam {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : ‖v‖ = 1)
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) {y : EuclideanSpace ℝ (Fin n)}
    (hy : ‖y‖ < 1) (z : EuclideanSpace ℝ (Fin n)) :
    dIncl (n := n) (graphParam hv R y)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) (graphParam hv R) y z) =
      fderiv ℝ (graphMap R) y z := by
  have hyU : y ∈ graphDomain n := mem_ball_zero_iff.mpr hy
  have hdiffΨ : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) (graphParam hv R) y :=
    (contMDiffAt_graphParam hv R hyU).mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hdiffι : MDifferentiableAt (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      ((↑) : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → EuclideanSpace ℝ (Fin (n + 1)))
      (graphParam hv R y) :=
    (contMDiff_coe_sphere (n := n)).contMDiffAt.mdifferentiableAt
      (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hcomp := mfderiv_comp_apply (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (I' := 𝓡 n)
    (I'' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) (f := graphParam hv R)
    (g := ((↑) : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → EuclideanSpace ℝ (Fin (n + 1))))
    y hdiffι hdiffΨ z
  have hcoe : ((↑) : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
      EuclideanSpace ℝ (Fin (n + 1))) ∘ graphParam hv R =ᶠ[𝓝 y] graphMap R := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hy)] with w hw
    exact coe_graphParam hv R (mem_ball_zero_iff.mp hw)
  rw [mfderiv_eq_fderiv, hcoe.fderiv_eq] at hcomp
  have hkey : dIncl (n := n) (graphParam hv R y)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) (graphParam hv R) y z) =
      mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        ((↑) : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → EuclideanSpace ℝ (Fin (n + 1)))
        (graphParam hv R y)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) (graphParam hv R) y z) := by
    with_unfolding_all rfl
  exact hkey.trans hcomp.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.dIncl_mfderiv_graphParam
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.dIncl_mfderiv_graphParam target :: scope.openDecls } }

private theorem paramGramMatrix_graphParam {v : EuclideanSpace ℝ (Fin (n + 1))}
    (hv : ‖v‖ = 1) (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : ‖y‖ < 1) :
    paramGramMatrix (I := 𝓡 n) (roundMetric (E := EuclideanSpace ℝ (Fin (n + 1))) (n := n))
        (graphParam hv R) y =
      Matrix.gram ℝ (fun i => fderiv ℝ (graphMap R) y
        (Tensor.Coordinates.chartModelBasis (EuclideanSpace ℝ (Fin n)) i)) := by
  ext i j
  rw [paramGramMatrix_apply, roundMetric_inner, dIncl_mfderiv_graphParam hv R hy,
    dIncl_mfderiv_graphParam hv R hy, Matrix.gram_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.paramGramMatrix_graphParam
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.paramGramMatrix_graphParam target :: scope.openDecls } }

private theorem sqrt_det_gram_le_paramDensity_graphParam {v : EuclideanSpace ℝ (Fin (n + 1))}
    (hv : ‖v‖ = 1) (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ)
    {y : EuclideanSpace ℝ (Fin n)} (hy : ‖y‖ < 1) :
    Real.sqrt (Matrix.gram ℝ (Tensor.Coordinates.chartModelBasis (EuclideanSpace ℝ (Fin n)))).det ≤
      paramDensity (I := 𝓡 n) (roundMetric (E := EuclideanSpace ℝ (Fin (n + 1))) (n := n))
        (graphParam hv R) y := by
  classical
  rw [DifferentialGeometry.Integral.Measure.paramDensity_apply, paramGramMatrix_graphParam hv R hy]
  apply Real.sqrt_le_sqrt
  set b := Tensor.Coordinates.chartModelBasis (EuclideanSpace ℝ (Fin n))
  set L := fderiv ℝ (graphMap R) y
  have hL : ∀ u, ‖u‖ ≤ ‖L u‖ := norm_le_norm_fderiv_graphMap R hy
  have hinj : LinearMap.ker (L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) =
      ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr fun u hu => ?_
    have hu' : L u = 0 := hu
    have := hL u
    rw [hu', norm_zero] at this
    exact norm_le_zero_iff.mp this
  have hli : LinearIndependent ℝ (fun i => L (b i)) :=
    b.linearIndependent.map' (L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
      hinj
  refine det_le_of_quad_le (Matrix.posSemidef_gram ℝ b)
    (Matrix.posDef_gram_of_linearIndependent hli) fun x => ?_
  have h1 := Matrix.star_dotProduct_gram_mulVec (𝕜 := ℝ) b x x
  have h2 := Matrix.star_dotProduct_gram_mulVec (𝕜 := ℝ) (fun i => L (b i)) x x
  simp only [_root_.TrivialStar.star_trivial] at h1 h2
  rw [h1, h2]
  have hsum : ∑ i, x i • L (b i) = L (∑ i, x i • b i) := by
    simp only [map_sum, map_smul]
  rw [hsum, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (hL _) 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.sqrt_det_gram_le_paramDensity_graphParam
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.sqrt_det_gram_le_paramDensity_graphParam target :: scope.openDecls } }

private theorem graphParam_injOn {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : ‖v‖ = 1)
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) :
    Set.InjOn (graphParam hv R) (_root_.Metric.ball 0 1) := by
  intro y hy y' hy' h
  have hcoe := congrArg (fun w : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 =>
    graphProj R (w : EuclideanSpace ℝ (Fin (n + 1)))) h
  simpa only [coe_graphParam hv R (mem_ball_zero_iff.mp hy),
    coe_graphParam hv R (mem_ball_zero_iff.mp hy'), graphProj_graphMap] using hcoe

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.graphParam_injOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.graphParam_injOn target :: scope.openDecls } }

private theorem volume_ball_le_of_graph {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : ‖v‖ = 1)
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) :
    (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) (_root_.Metric.ball 0 1) ≤
      riemannianVolumeMeasure (I := 𝓡 n) (M := _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
        (roundMetric (E := EuclideanSpace ℝ (Fin (n + 1))) (n := n)) univ := by
  set b := Tensor.Coordinates.chartModelBasis (EuclideanSpace ℝ (Fin n))
  have hvol : (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) =
      ENNReal.ofReal (Real.sqrt (Matrix.gram ℝ b).det) •
        modelHaar (E := EuclideanSpace ℝ (Fin n)) := by
    have h :=
      DifferentialGeometry.Integral.Measure.addHaar_withDensity_sqrt_det_gramMatrix_eq_volume b
    rw [← h, modelHaar, _root_.MeasureTheory.withDensity_const]
    rfl
  rw [hvol, Measure.smul_apply, smul_eq_mul, ← _root_.MeasureTheory.setLIntegral_const]
  calc ∫⁻ _ in _root_.Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1,
        ENNReal.ofReal (Real.sqrt (Matrix.gram ℝ b).det) ∂modelHaar (E := EuclideanSpace ℝ (Fin n))
      ≤ ∫⁻ y in _root_.Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1,
          ENNReal.ofReal (paramDensity (I := 𝓡 n)
            (roundMetric (E := EuclideanSpace ℝ (Fin (n + 1))) (n := n)) (graphParam hv R) y)
          ∂modelHaar (E := EuclideanSpace ℝ (Fin n)) :=
        _root_.MeasureTheory.setLIntegral_mono' measurableSet_ball fun y hy =>
          ENNReal.ofReal_le_ofReal
            (sqrt_det_gram_le_paramDensity_graphParam hv R (mem_ball_zero_iff.mp hy))
    _ = riemannianVolumeMeasure (I := 𝓡 n) (M := _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
          (roundMetric (E := EuclideanSpace ℝ (Fin (n + 1))) (n := n))
          (graphParam hv R '' _root_.Metric.ball 0 1) :=
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_image_eq
          (I := 𝓡 n) (M := _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
          (roundMetric (E := EuclideanSpace ℝ (Fin (n + 1))) (n := n)) _root_.Metric.isOpen_ball
          measurableSet_ball Subset.rfl (contMDiffOn_graphParam hv R)
          (graphParam_injOn hv R)).symm
    _ ≤ _ := _root_.MeasureTheory.measure_mono (_root_.Set.subset_univ _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.volume_ball_le_of_graph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.volume_ball_le_of_graph target :: scope.openDecls } }

private theorem volume_ball_le_riemannianVolumeMeasure_roundMetric (n : ℕ) :
    (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) (_root_.Metric.ball 0 1) ≤
      riemannianVolumeMeasure (I := 𝓡 n) (M := _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
        (roundMetric (E := EuclideanSpace ℝ (Fin (n + 1))) (n := n)) univ := by
  let v : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single (Fin.last n) 1
  have hv : ‖v‖ = 1 := by simp [v]
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv
    exact zero_ne_one hv
  let R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ :=
    ((stdOrthonormalBasis ℝ ((ℝ ∙ v)ᗮ)).reindex
      (finCongr (Submodule.finrank_orthogonal_span_singleton hv0))).repr.symm
  exact volume_ball_le_of_graph hv R

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.volume_ball_le_riemannianVolumeMeasure_roundMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.volume_ball_le_riemannianVolumeMeasure_roundMetric target :: scope.openDecls } }

theorem ofReal_sqrt_pi_pow_div_gamma_le_riemannianVolumeMeasure_roundMetric_univ
    (n : ℕ) [NeZero n] :
    ENNReal.ofReal (Real.sqrt Real.pi ^ n / Real.Gamma (n / 2 + 1)) ≤
      riemannianVolumeMeasure (I := 𝓡 n) (M := _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
        (roundMetric (E := EuclideanSpace ℝ (Fin (n + 1))) (n := n)) univ := by
  have h := volume_ball_le_riemannianVolumeMeasure_roundMetric n
  have hpos : 0 < _root_.Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [finrank_euclideanSpace_fin]
    exact Nat.pos_of_ne_zero (NeZero.ne n)
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) := Module.nontrivial_of_finrank_pos hpos
  rw [InnerProductSpace.volume_ball, finrank_euclideanSpace_fin, ENNReal.ofReal_one, one_pow,
    one_mul] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.ofReal_sqrt_pi_pow_div_gamma_le_riemannianVolumeMeasure_roundMetric_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.ofReal_sqrt_pi_pow_div_gamma_le_riemannianVolumeMeasure_roundMetric_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.ofReal_sqrt_pi_pow_div_gamma_le_riemannianVolumeMeasure_roundMetric_univ ``Submission.DifferentialGeometry.Geometry.ofReal_sqrt_pi_pow_div_gamma_le_riemannianVolumeMeasure_roundMetric_univ

theorem ofReal_four_pi_div_three_le_riemannianVolumeMeasure_roundMetric_univ :
    ENNReal.ofReal (4 * Real.pi / 3) ≤
      riemannianVolumeMeasure (I := 𝓡 3) (M := _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
        (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)) univ := by
  have h := ofReal_sqrt_pi_pow_div_gamma_le_riemannianVolumeMeasure_roundMetric_univ 3
  have hG : Real.Gamma ((3 : ℕ) / 2 + 1) = 3 / 4 * Real.sqrt Real.pi := by
    have h1 : ((3 : ℕ) : ℝ) / 2 + 1 = 3 / 2 + 1 := by norm_num
    have h2 : (3 / 2 : ℝ) = 1 / 2 + 1 := by norm_num
    rw [h1, Real.Gamma_add_one (by norm_num), h2, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  have hpi : Real.sqrt Real.pi ^ 3 / (3 / 4 * Real.sqrt Real.pi) = 4 * Real.pi / 3 := by
    have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have hsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
    have hcube : Real.sqrt Real.pi ^ 3 = Real.pi * Real.sqrt Real.pi := by
      rw [pow_succ, hsq]
    rw [hcube]
    field_simp
  rw [hG, hpi] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.ofReal_four_pi_div_three_le_riemannianVolumeMeasure_roundMetric_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.ofReal_four_pi_div_three_le_riemannianVolumeMeasure_roundMetric_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.ofReal_four_pi_div_three_le_riemannianVolumeMeasure_roundMetric_univ ``Submission.DifferentialGeometry.Geometry.ofReal_four_pi_div_three_le_riemannianVolumeMeasure_roundMetric_univ

end DifferentialGeometry.Geometry
