import Mathlib.Analysis.Convex.StdSimplex

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Simplex

variable {ι : Type*} [Fintype ι]

def supportFace (s : Finset ι) : Set (stdSimplex ℝ ι) :=
  {p | ∀ i, i ∉ s → p i = 0}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.supportFace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.supportFace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.supportFace ``Submission.DifferentialGeometry.Simplex.supportFace

@[simp]
theorem mem_supportFace (s : Finset ι) (p : stdSimplex ℝ ι) :
    p ∈ supportFace s ↔ ∀ i, i ∉ s → p i = 0 := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.mem_supportFace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.mem_supportFace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.mem_supportFace ``Submission.DifferentialGeometry.Simplex.mem_supportFace

theorem isClosed_supportFace (s : Finset ι) : IsClosed (supportFace s) := by
  have h : supportFace s = ⋂ (i : ι) (_ : i ∉ s), {p : stdSimplex ℝ ι | p i = 0} := by
    ext p
    simp [supportFace]
  rw [h]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦
    isClosed_eq ((continuous_apply i).comp continuous_subtype_val) continuous_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.isClosed_supportFace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.isClosed_supportFace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.isClosed_supportFace ``Submission.DifferentialGeometry.Simplex.isClosed_supportFace

theorem supportFace_mono {s t : Finset ι} (h : s ⊆ t) : supportFace s ⊆ supportFace t :=
  fun _ hp i hi ↦ hp i (fun his ↦ hi (h his))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.supportFace_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.supportFace_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.supportFace_mono ``Submission.DifferentialGeometry.Simplex.supportFace_mono

@[simp]
theorem supportFace_inter [DecidableEq ι] (s t : Finset ι) :
    supportFace (s ∩ t) = supportFace s ∩ supportFace t := by
  classical
  ext p
  constructor
  · intro hp
    exact ⟨fun i hi ↦ hp i (by simp [hi]), fun i hi ↦ hp i (by simp [hi])⟩
  · rintro ⟨hs, ht⟩ i hi
    by_cases his : i ∈ s
    · exact ht i (fun hit ↦ hi (Finset.mem_inter.mpr ⟨his, hit⟩))
    · exact hs i his

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.supportFace_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.supportFace_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.supportFace_inter ``Submission.DifferentialGeometry.Simplex.supportFace_inter

theorem map_subtype_val_apply_mem (s : Finset ι) (p : stdSimplex ℝ s) (i : s) :
    (stdSimplex.map Subtype.val p) i.val = p i := by
  classical
  change FunOnFinite.linearMap ℝ ℝ Subtype.val p i.val = p i
  rw [FunOnFinite.linearMap_apply_apply]
  simp only [Subtype.val_inj, Finset.filter_eq', Finset.mem_univ, if_true, Finset.sum_singleton]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.map_subtype_val_apply_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.map_subtype_val_apply_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.map_subtype_val_apply_mem ``Submission.DifferentialGeometry.Simplex.map_subtype_val_apply_mem

theorem map_subtype_val_apply_notMem (s : Finset ι) (p : stdSimplex ℝ s) (i : ι)
    (hi : i ∉ s) : (stdSimplex.map Subtype.val p) i = 0 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ Subtype.val p i = 0
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro j hj
  exact (hi ((Finset.mem_filter.mp hj).2 ▸ j.property)).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.map_subtype_val_apply_notMem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.map_subtype_val_apply_notMem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.map_subtype_val_apply_notMem ``Submission.DifferentialGeometry.Simplex.map_subtype_val_apply_notMem

def supportFaceInsert (s : Finset ι) : C(stdSimplex ℝ s, supportFace s) :=
  ⟨fun p ↦ ⟨stdSimplex.map Subtype.val p, map_subtype_val_apply_notMem s p⟩,
    (stdSimplex.continuous_map Subtype.val).subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.supportFaceInsert then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.supportFaceInsert"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.supportFaceInsert ``Submission.DifferentialGeometry.Simplex.supportFaceInsert

def supportFaceRestrict (s : Finset ι) : C(supportFace s, stdSimplex ℝ s) :=
  ⟨fun p ↦ ⟨fun i ↦ p.val i.val, ⟨fun i ↦ p.val.property.1 _, by
      classical
      rw [Finset.sum_coe_sort]
      exact (Finset.sum_subset (Finset.subset_univ s) (fun i _ hi ↦ p.property i hi)).trans
        p.val.property.2⟩⟩,
    (continuous_pi fun i ↦ (continuous_apply i.val).comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.supportFaceRestrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.supportFaceRestrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.supportFaceRestrict ``Submission.DifferentialGeometry.Simplex.supportFaceRestrict

@[simp]
theorem supportFaceRestrict_supportFaceInsert (s : Finset ι) (p : stdSimplex ℝ s) :
    supportFaceRestrict s (supportFaceInsert s p) = p := by
  apply Subtype.ext
  funext i
  exact map_subtype_val_apply_mem s p i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.supportFaceRestrict_supportFaceInsert then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.supportFaceRestrict_supportFaceInsert"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.supportFaceRestrict_supportFaceInsert ``Submission.DifferentialGeometry.Simplex.supportFaceRestrict_supportFaceInsert

@[simp]
theorem supportFaceInsert_supportFaceRestrict (s : Finset ι) (p : supportFace s) :
    supportFaceInsert s (supportFaceRestrict s p) = p := by
  classical
  apply Subtype.ext
  apply Subtype.ext
  funext i
  by_cases hi : i ∈ s
  · exact map_subtype_val_apply_mem s (supportFaceRestrict s p) ⟨i, hi⟩
  · exact (map_subtype_val_apply_notMem s _ i hi).trans (p.property i hi).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.supportFaceInsert_supportFaceRestrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.supportFaceInsert_supportFaceRestrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.supportFaceInsert_supportFaceRestrict ``Submission.DifferentialGeometry.Simplex.supportFaceInsert_supportFaceRestrict

def supportFaceHomeomorph (s : Finset ι) : stdSimplex ℝ s ≃ₜ supportFace s where
  toFun := supportFaceInsert s
  invFun := supportFaceRestrict s
  left_inv := supportFaceRestrict_supportFaceInsert s
  right_inv := supportFaceInsert_supportFaceRestrict s
  continuous_toFun := (supportFaceInsert s).continuous
  continuous_invFun := (supportFaceRestrict s).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.supportFaceHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.supportFaceHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.supportFaceHomeomorph ``Submission.DifferentialGeometry.Simplex.supportFaceHomeomorph

@[simp]
theorem supportFaceHomeomorph_apply_val (s : Finset ι) (p : stdSimplex ℝ s) :
    (supportFaceHomeomorph s p).val = stdSimplex.map Subtype.val p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.supportFaceHomeomorph_apply_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.supportFaceHomeomorph_apply_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.supportFaceHomeomorph_apply_val ``Submission.DifferentialGeometry.Simplex.supportFaceHomeomorph_apply_val

@[simp]
theorem supportFaceHomeomorph_symm_apply (s : Finset ι) (p : supportFace s) (i : s) :
    (supportFaceHomeomorph s).symm p i = p.val i.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.supportFaceHomeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.supportFaceHomeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.supportFaceHomeomorph_symm_apply ``Submission.DifferentialGeometry.Simplex.supportFaceHomeomorph_symm_apply

end DifferentialGeometry.Simplex
