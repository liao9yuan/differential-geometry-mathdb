import Submission.DifferentialGeometry.Geometry.Metric.LinearAlgebra.OrthogonalFixedVector

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Geometry

open _root_.Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma map_mem_normal (A : E ≃ₗᵢ[ℝ] E) {u : E} (hu : A u = u)
    {v : E} (hv : v ∈ (ℝ ∙ u)ᗮ) : A v ∈ (ℝ ∙ u)ᗮ := by
  rw [_root_.Submodule.mem_orthogonal_singleton_iff_inner_left] at hv ⊢
  rw [← hu, A.inner_map_map]
  exact hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.map_mem_normal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.map_mem_normal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.map_mem_normal ``Submission.DifferentialGeometry.Geometry.map_mem_normal


def normalIsometry (A : E ≃ₗᵢ[ℝ] E) {u : E} (hu : A u = u) :
    (ℝ ∙ u)ᗮ ≃ₗᵢ[ℝ] (ℝ ∙ u)ᗮ where
  toFun v := ⟨A v, map_mem_normal A hu v.property⟩
  invFun v := ⟨A.symm v, map_mem_normal A.symm
    (by rw [A.symm_apply_eq, hu]) v.property⟩
  left_inv v := by ext; simp
  right_inv v := by ext; simp
  map_add' v w := by ext; simp
  map_smul' c v := by ext; simp
  norm_map' v := A.norm_map v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.normalIsometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.normalIsometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.normalIsometry ``Submission.DifferentialGeometry.Geometry.normalIsometry

omit [FiniteDimensional ℝ E] in
@[simp]
lemma normalIsometry_apply (A : E ≃ₗᵢ[ℝ] E) {u : E} (hu : A u = u)
    (v : (ℝ ∙ u)ᗮ) : (normalIsometry A hu v : E) = A v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.normalIsometry_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.normalIsometry_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.normalIsometry_apply ``Submission.DifferentialGeometry.Geometry.normalIsometry_apply


theorem det_normalIsometry (A : E ≃ₗᵢ[ℝ] E) {u : E} (hu : A u = u) :
    (normalIsometry A hu).toLinearMap.det = A.toLinearMap.det := by
  let K := ℝ ∙ u
  let e := K.prodEquivOfIsCompl Kᗮ K.isCompl_orthogonal
  have hline (v : K) : A (v : E) = v := by
    obtain ⟨c, hc⟩ := mem_span_singleton.mp v.property
    rw [← hc, map_smul, hu]
  have hconj : e.symm.toLinearMap ∘ₗ A.toLinearMap ∘ₗ e.toLinearMap =
      (LinearMap.id : K →ₗ[ℝ] K).prodMap (normalIsometry A hu).toLinearMap := by
    apply LinearMap.ext
    intro v
    apply e.injective
    change e (e.symm (A (e v))) = e (v.1, normalIsometry A hu v.2)
    rw [e.apply_symm_apply]
    change A ((v.1 : E) + v.2) = (v.1 : E) + A v.2
    rw [map_add, hline]
  have hd := congrArg LinearMap.det hconj
  have hc := LinearMap.det_conj A.toLinearMap e.symm
  simp only [LinearEquiv.symm_symm] at hc
  rw [hc, LinearMap.det_prodMap, LinearMap.det_id, one_mul] at hd
  exact hd.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.det_normalIsometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.det_normalIsometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.det_normalIsometry ``Submission.DifferentialGeometry.Geometry.det_normalIsometry

theorem finrank_normal {u : E} (hu : u ≠ 0) :
    Module.finrank ℝ (ℝ ∙ u)ᗮ = Module.finrank ℝ E - 1 := by
  have h := (ℝ ∙ u).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hu] at h
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.finrank_normal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.finrank_normal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.finrank_normal ``Submission.DifferentialGeometry.Geometry.finrank_normal


theorem exists_unit_normal_fixed_vector (A : E ≃ₗᵢ[ℝ] E) {u : E}
    (hu : u ≠ 0) (hfix : A u = u)
    (hdet : A.toLinearMap.det ≠ (-1 : ℝ) ^ (Module.finrank ℝ E - 1)) :
    ∃ v : E, ‖v‖ = 1 ∧ _root_.Inner.inner ℝ u v = 0 ∧ A v = v := by
  have hd : (normalIsometry A hfix).toLinearMap.det ≠
      (-1 : ℝ) ^ Module.finrank ℝ (ℝ ∙ u)ᗮ := by
    rwa [det_normalIsometry, finrank_normal hu]
  obtain ⟨v, hv, hAv⟩ := exists_unit_fixed_vector_of_det_ne (normalIsometry A hfix) hd
  refine ⟨v, hv, ?_, congrArg Subtype.val hAv⟩
  exact mem_orthogonal_singleton_iff_inner_right.mp v.property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_unit_normal_fixed_vector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_unit_normal_fixed_vector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_unit_normal_fixed_vector ``Submission.DifferentialGeometry.Geometry.exists_unit_normal_fixed_vector


theorem exists_unit_normal_fixed_vector_of_even (A : E ≃ₗᵢ[ℝ] E) {u : E}
    (hu : u ≠ 0) (hfix : A u = u) (hn : 2 ≤ Module.finrank ℝ E)
    (heven : Even (Module.finrank ℝ E)) (hdet : A.toLinearMap.det = 1) :
    ∃ v : E, ‖v‖ = 1 ∧ _root_.Inner.inner ℝ u v = 0 ∧ A v = v := by
  apply exists_unit_normal_fixed_vector A hu hfix
  have hp := (Nat.Even.sub_odd (by omega : 1 ≤ Module.finrank ℝ E) heven odd_one).neg_one_pow (α := ℝ)
  rw [hdet, hp]
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_unit_normal_fixed_vector_of_even then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_unit_normal_fixed_vector_of_even"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_unit_normal_fixed_vector_of_even ``Submission.DifferentialGeometry.Geometry.exists_unit_normal_fixed_vector_of_even


theorem exists_unit_normal_fixed_vector_of_odd (A : E ≃ₗᵢ[ℝ] E) {u : E}
    (hu : u ≠ 0) (hfix : A u = u)
    (hodd : Odd (Module.finrank ℝ E)) (hdet : A.toLinearMap.det = -1) :
    ∃ v : E, ‖v‖ = 1 ∧ _root_.Inner.inner ℝ u v = 0 ∧ A v = v := by
  apply exists_unit_normal_fixed_vector A hu hfix
  rw [hdet, (Nat.Odd.sub_odd hodd odd_one).neg_one_pow]
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_unit_normal_fixed_vector_of_odd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_unit_normal_fixed_vector_of_odd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_unit_normal_fixed_vector_of_odd ``Submission.DifferentialGeometry.Geometry.exists_unit_normal_fixed_vector_of_odd

end DifferentialGeometry.Geometry
