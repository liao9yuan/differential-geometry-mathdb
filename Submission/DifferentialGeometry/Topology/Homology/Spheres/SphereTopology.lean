import Submission.DifferentialGeometry.Topology.Homology.SingularPair
import Submission.DifferentialGeometry.Topology.Sphere.SphereSimplyConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Metric _root_.Module _root_.Set _root_.unitInterval
open scoped _root_.ContinuousMap

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

abbrev unitSphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.unitSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.unitSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.unitSphere ``Submission.DifferentialGeometry.Topology.SingularPair.unitSphere

namespace Sphere

def northPole (n : ℕ) : unitSphere n :=
  ⟨EuclideanSpace.single (Fin.last n) 1, by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.northPole then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.northPole"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.northPole ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.northPole

def southPole (n : ℕ) : unitSphere n :=
  ⟨-EuclideanSpace.single (Fin.last n) 1, by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.southPole then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.southPole"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.southPole ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.southPole

@[simp] lemma northPole_val (n : ℕ) : (northPole n).1 = EuclideanSpace.single (Fin.last n) 1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.northPole_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.northPole_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.northPole_val ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.northPole_val
@[simp] lemma southPole_val (n : ℕ) : (southPole n).1 = -EuclideanSpace.single (Fin.last n) 1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.southPole_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.southPole_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.southPole_val ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.southPole_val

lemma northPole_ne_southPole (n : ℕ) : northPole n ≠ southPole n := by
  intro h
  have := congrArg (fun x : unitSphere n => x.1 (Fin.last n)) h
  simp at this
  norm_num at this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.northPole_ne_southPole then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.northPole_ne_southPole"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.northPole_ne_southPole ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.northPole_ne_southPole

lemma isOpen_compl_singleton {n : ℕ} (x : unitSphere n) : IsOpen ({x}ᶜ : Set (unitSphere n)) :=
  _root_.isOpen_compl_singleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.isOpen_compl_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.isOpen_compl_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.isOpen_compl_singleton ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.isOpen_compl_singleton

lemma cover (n : ℕ) : ({northPole n}ᶜ : Set (unitSphere n)) ∪ {southPole n}ᶜ = univ := by
  ext x
  simp only [_root_.Set.mem_union, _root_.Set.mem_compl_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_univ, iff_true]
  by_contra h
  simp only [not_or, _root_.Classical.not_not] at h
  exact northPole_ne_southPole n (h.1.symm.trans h.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.cover ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.cover

instance contractibleSpace_compl_northPole (n : ℕ) : ContractibleSpace ({northPole n}ᶜ : Set (unitSphere n)) :=
  contractibleSpace_sphere_compl_singleton _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.contractibleSpace_compl_northPole then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.contractibleSpace_compl_northPole"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.contractibleSpace_compl_northPole ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.contractibleSpace_compl_northPole

instance contractibleSpace_compl_southPole (n : ℕ) : ContractibleSpace ({southPole n}ᶜ : Set (unitSphere n)) :=
  contractibleSpace_sphere_compl_singleton _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.contractibleSpace_compl_southPole then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.contractibleSpace_compl_southPole"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.contractibleSpace_compl_southPole ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.contractibleSpace_compl_southPole

lemma eq_smul_single_last {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1)))
    (h : ∀ j : Fin n, x (Fin.castSucc j) = 0) :
    x = x (Fin.last n) • EuclideanSpace.single (Fin.last n) 1 := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp [h j, Fin.castSucc_ne_last]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.eq_smul_single_last then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.eq_smul_single_last"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.eq_smul_single_last ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.eq_smul_single_last

lemma norm_eq_abs_last {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1)))
    (h : ∀ j : Fin n, x (Fin.castSucc j) = 0) : ‖x‖ = |x (Fin.last n)| := by
  conv_lhs => rw [eq_smul_single_last x h]
  simp [norm_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.norm_eq_abs_last then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.norm_eq_abs_last"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.norm_eq_abs_last ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.norm_eq_abs_last

lemma eq_northPole_or_eq_southPole {n : ℕ} (x : unitSphere n) (h : ∀ j : Fin n, x.1 (Fin.castSucc j) = 0) :
    x = northPole n ∨ x = southPole n := by
  have hx : ‖x.1‖ = 1 := mem_sphere_zero_iff_norm.1 x.2
  rw [norm_eq_abs_last x.1 h] at hx
  rcases abs_eq (zero_le_one' ℝ) |>.1 hx with h1 | h1
  · left
    apply Subtype.ext
    rw [eq_smul_single_last x.1 h, h1, one_smul]
    rfl
  · right
    apply Subtype.ext
    rw [eq_smul_single_last x.1 h, h1, neg_one_smul]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.eq_northPole_or_eq_southPole then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.eq_northPole_or_eq_southPole"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.eq_northPole_or_eq_southPole ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.eq_northPole_or_eq_southPole

def proj (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 2)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) where
  toFun x := WithLp.toLp 2 fun j => x (Fin.castSucc j)
  map_add' x y := by ext j; simp
  map_smul' c x := by ext j; simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.proj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.proj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.proj ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.proj

@[simp] lemma proj_apply {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 2))) (j : Fin (n + 1)) :
    proj n x j = x (Fin.castSucc j) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.proj_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.proj_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.proj_apply ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.proj_apply

lemma continuous_proj (n : ℕ) : Continuous (proj n) :=
  (proj n).continuous_of_finiteDimensional

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.continuous_proj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.continuous_proj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.continuous_proj ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.continuous_proj

def incl (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 2)) where
  toFun y := WithLp.toLp 2 (Fin.snoc (fun j => y j) 0)
  map_add' x y := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Fin.snoc_castSucc, Fin.snoc_last]
  map_smul' c x := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Fin.snoc_castSucc, Fin.snoc_last]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.incl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.incl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.incl ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.incl

@[simp] lemma incl_apply_castSucc {n : ℕ} (y : EuclideanSpace ℝ (Fin (n + 1)))
    (j : Fin (n + 1)) :
    incl n y (Fin.castSucc j) = y j := by
  simp [incl, Fin.snoc_castSucc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.incl_apply_castSucc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.incl_apply_castSucc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.incl_apply_castSucc ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.incl_apply_castSucc

@[simp] lemma incl_apply_last {n : ℕ} (y : EuclideanSpace ℝ (Fin (n + 1))) :
    incl n y (Fin.last (n + 1)) = 0 := by
  simp [incl, Fin.snoc_last]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.incl_apply_last then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.incl_apply_last"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.incl_apply_last ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.incl_apply_last

lemma continuous_incl (n : ℕ) : Continuous (incl n) :=
  (incl n).continuous_of_finiteDimensional

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.continuous_incl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.continuous_incl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.continuous_incl ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.continuous_incl

@[simp] lemma proj_incl {n : ℕ} (y : EuclideanSpace ℝ (Fin (n + 1))) :
    proj n (incl n y) = y := by
  ext j
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.proj_incl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.proj_incl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.proj_incl ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.proj_incl

lemma norm_incl {n : ℕ} (y : EuclideanSpace ℝ (Fin (n + 1))) : ‖incl n y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_castSucc]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.norm_incl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.norm_incl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.norm_incl ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.norm_incl

lemma proj_eq_zero_iff {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 2))) :
    proj n x = 0 ↔ ∀ j : Fin (n + 1), x (Fin.castSucc j) = 0 := by
  constructor
  · intro h j
    rw [← proj_apply, h]
    rfl
  · intro h
    ext j
    simp [h j]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.proj_eq_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.proj_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.proj_eq_zero_iff ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.proj_eq_zero_iff

lemma proj_northPole (n : ℕ) : proj n (northPole (n + 1)).1 = 0 := by
  rw [proj_eq_zero_iff]
  intro j
  simp [Fin.castSucc_ne_last]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.proj_northPole then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.proj_northPole"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.proj_northPole ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.proj_northPole

lemma proj_southPole (n : ℕ) : proj n (southPole (n + 1)).1 = 0 := by
  have h := proj_northPole n
  rw [northPole_val] at h
  rw [southPole_val, map_neg, h, neg_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.proj_southPole then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.proj_southPole"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.proj_southPole ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.proj_southPole

lemma proj_ne_zero_iff {n : ℕ} (x : unitSphere (n + 1)) :
    proj n x.1 ≠ 0 ↔ x ≠ northPole (n + 1) ∧ x ≠ southPole (n + 1) := by
  constructor
  · intro h
    refine ⟨fun hx => h ?_, fun hx => h ?_⟩
    · rw [hx]; exact proj_northPole n
    · rw [hx]; exact proj_southPole n
  · rintro ⟨h1, h2⟩ h
    rcases eq_northPole_or_eq_southPole x ((proj_eq_zero_iff _).1 h) with h' | h'
    · exact h1 h'
    · exact h2 h'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.proj_ne_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.proj_ne_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.proj_ne_zero_iff ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.proj_ne_zero_iff

abbrev equator (n : ℕ) : Set (unitSphere (n + 1)) := {northPole (n + 1)}ᶜ ∩ {southPole (n + 1)}ᶜ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.equator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.equator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.equator ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.equator

lemma mem_equator_iff {n : ℕ} (x : unitSphere (n + 1)) :
    x ∈ equator n ↔ proj n x.1 ≠ 0 := by
  rw [proj_ne_zero_iff]
  simp [equator]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.mem_equator_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.mem_equator_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.mem_equator_iff ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.mem_equator_iff

lemma proj_ne_zero {n : ℕ} (x : equator n) : proj n x.1.1 ≠ 0 :=
  (mem_equator_iff x.1).1 x.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.proj_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.proj_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.proj_ne_zero ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.proj_ne_zero

lemma radialProj_mem_equator {n : ℕ} {v : EuclideanSpace ℝ (Fin (n + 2))}
    (hv : proj n v ≠ 0) :
    (⟨radialProj v, radialProj_mem_sphere (fun h => hv (by rw [h, map_zero]))⟩ :
      unitSphere (n + 1)) ∈ equator n := by
  rw [mem_equator_iff]
  change proj n (‖v‖⁻¹ • v) ≠ 0
  rw [map_smul]
  exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.2 fun h => hv (by rw [h, map_zero]))) hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.radialProj_mem_equator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.radialProj_mem_equator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.radialProj_mem_equator ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.radialProj_mem_equator

def toEquator {n : ℕ} (x : equator n) : unitSphere n :=
  ⟨radialProj (proj n x.1.1), radialProj_mem_sphere (proj_ne_zero x)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.toEquator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.toEquator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.toEquator ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.toEquator

lemma continuous_toEquator (n : ℕ) : Continuous (toEquator (n := n)) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_radialProj_comp
    ((continuous_proj n).comp (continuous_subtype_val.comp continuous_subtype_val))
    fun x => proj_ne_zero x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.continuous_toEquator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.continuous_toEquator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.continuous_toEquator ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.continuous_toEquator

def ofEquator {n : ℕ} (y : unitSphere n) : equator n :=
  ⟨⟨incl n y.1, by
      rw [mem_sphere_zero_iff_norm, norm_incl]
      exact mem_sphere_zero_iff_norm.1 y.2⟩, by
    rw [mem_equator_iff]
    change proj n (incl n y.1) ≠ 0
    rw [proj_incl]
    intro h
    have := mem_sphere_zero_iff_norm.1 y.2
    rw [h, norm_zero] at this
    exact zero_ne_one this⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.ofEquator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.ofEquator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.ofEquator ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.ofEquator

lemma continuous_ofEquator (n : ℕ) : Continuous (ofEquator (n := n)) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  exact (continuous_incl n).comp continuous_subtype_val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.continuous_ofEquator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.continuous_ofEquator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.continuous_ofEquator ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.continuous_ofEquator

lemma toEquator_ofEquator {n : ℕ} (y : unitSphere n) : toEquator (ofEquator y) = y := by
  apply Subtype.ext
  change radialProj (proj n (incl n y.1)) = y.1
  rw [proj_incl]
  exact radialProj_of_norm_eq_one (mem_sphere_zero_iff_norm.1 y.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.toEquator_ofEquator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.toEquator_ofEquator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.toEquator_ofEquator ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.toEquator_ofEquator

def line {n : ℕ} (t : ℝ) (x : equator n) : EuclideanSpace ℝ (Fin (n + 2)) :=
  (1 - t) • x.1.1 + t • incl n (radialProj (proj n x.1.1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.line then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.line"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.line ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.line

lemma proj_line {n : ℕ} (t : ℝ) (x : equator n) :
    proj n (line t x) = ((1 - t) + t * ‖proj n x.1.1‖⁻¹) • proj n x.1.1 := by
  simp only [line, map_add, map_smul, proj_incl, radialProj, smul_smul, add_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.proj_line then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.proj_line"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.proj_line ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.proj_line

lemma proj_line_ne_zero {n : ℕ} (t : I) (x : equator n) : proj n (line (t : ℝ) x) ≠ 0 := by
  rw [proj_line]
  refine smul_ne_zero ?_ (proj_ne_zero x)
  have hpos : 0 < ‖proj n x.1.1‖⁻¹ := inv_pos.2 (norm_pos_iff.2 (proj_ne_zero x))
  have ht0 : (0 : ℝ) ≤ t := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  refine ne_of_gt ?_
  rcases eq_or_lt_of_le ht1 with h | h
  · rw [h]; simpa using hpos
  · have := mul_nonneg ht0 hpos.le
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.proj_line_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.proj_line_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.proj_line_ne_zero ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.proj_line_ne_zero

lemma continuous_line (n : ℕ) : Continuous fun p : I × equator n => line (p.1 : ℝ) p.2 := by
  have h1 : Continuous fun p : I × equator n => p.2.1.1 :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  have h2 : Continuous fun p : I × equator n => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  exact ((continuous_const.sub h2).smul h1).add
    (h2.smul ((continuous_incl n).comp (continuous_radialProj_comp ((continuous_proj n).comp h1)
      fun p => proj_ne_zero p.2)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.continuous_line then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.continuous_line"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.continuous_line ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.continuous_line

def equatorHomotopy (n : ℕ) :
    ContinuousMap.Homotopy (ContinuousMap.id (equator n))
      ((⟨ofEquator, continuous_ofEquator n⟩ : C(unitSphere n, equator n)).comp
        ⟨toEquator, continuous_toEquator n⟩) where
  toFun p := ⟨_, radialProj_mem_equator (proj_line_ne_zero p.1 p.2)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact continuous_radialProj_comp (continuous_line n)
      fun p h => proj_line_ne_zero p.1 p.2 (by rw [h, map_zero])
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    change radialProj (line (0 : ℝ) x) = x.1.1
    simp only [line, sub_zero, one_smul, zero_smul, add_zero]
    exact radialProj_of_norm_eq_one (mem_sphere_zero_iff_norm.1 x.1.2)
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    change radialProj (line (1 : ℝ) x) = incl n (radialProj (proj n x.1.1))
    simp only [line, sub_self, zero_smul, one_smul, zero_add]
    apply radialProj_of_norm_eq_one
    rw [norm_incl]
    exact norm_radialProj (proj_ne_zero x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.equatorHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.equatorHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.equatorHomotopy ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.equatorHomotopy

def equatorHomotopyEquiv (n : ℕ) :
    ↥(({northPole (n + 1)}ᶜ : Set (unitSphere (n + 1))) ∩ {southPole (n + 1)}ᶜ) ≃ₕ unitSphere n where
  toFun := ⟨toEquator, continuous_toEquator n⟩
  invFun := ⟨ofEquator, continuous_ofEquator n⟩
  left_inv := ⟨(equatorHomotopy n).symm⟩
  right_inv := by
    have : (⟨toEquator, continuous_toEquator n⟩ : C(equator n, unitSphere n)).comp
        ⟨ofEquator, continuous_ofEquator n⟩ = ContinuousMap.id _ :=
      ContinuousMap.ext fun y => toEquator_ofEquator y
    rw [this]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.equatorHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.equatorHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.equatorHomotopyEquiv ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.equatorHomotopyEquiv

@[simp] lemma equatorHomotopyEquiv_apply {n : ℕ} (x : equator n) :
    equatorHomotopyEquiv n x = toEquator x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.equatorHomotopyEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.equatorHomotopyEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.equatorHomotopyEquiv_apply ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.equatorHomotopyEquiv_apply

@[simp] lemma equatorHomotopyEquiv_symm_apply {n : ℕ} (y : unitSphere n) :
    (equatorHomotopyEquiv n).symm y = ofEquator y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.equatorHomotopyEquiv_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.equatorHomotopyEquiv_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.equatorHomotopyEquiv_symm_apply ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.equatorHomotopyEquiv_symm_apply

instance pathConnectedSpace_succ (n : ℕ) : PathConnectedSpace (unitSphere (n + 1)) := by
  rw [← isPathConnected_iff_pathConnectedSpace]
  refine isPathConnected_sphere ?_ 0 zero_le_one
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  exact_mod_cast (by omega : 1 < n + 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.pathConnectedSpace_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.pathConnectedSpace_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.pathConnectedSpace_succ ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.pathConnectedSpace_succ

theorem pathConnectedSpace_of_one_le {n : ℕ} (hn : 1 ≤ n) : PathConnectedSpace (unitSphere n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.pathConnectedSpace_of_one_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.pathConnectedSpace_of_one_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.pathConnectedSpace_of_one_le ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.pathConnectedSpace_of_one_le

lemma eq_northPole_or_eq_southPole_zero (x : unitSphere 0) : x = northPole 0 ∨ x = southPole 0 :=
  eq_northPole_or_eq_southPole x (fun j => j.elim0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.eq_northPole_or_eq_southPole_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.eq_northPole_or_eq_southPole_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.eq_northPole_or_eq_southPole_zero ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.eq_northPole_or_eq_southPole_zero

lemma northPole_zero_apply : (northPole 0).1 0 = 1 := by
  simp [Fin.last_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.northPole_zero_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.northPole_zero_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.northPole_zero_apply ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.northPole_zero_apply

lemma southPole_zero_apply : (southPole 0).1 0 = -1 := by
  simp [Fin.last_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.southPole_zero_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.southPole_zero_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.southPole_zero_apply ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.southPole_zero_apply

def sphere0Equiv : unitSphere 0 ≃ Fin 2 where
  toFun x := if 0 < x.1 0 then 0 else 1
  invFun i := if i = 0 then northPole 0 else southPole 0
  left_inv x := by
    rcases eq_northPole_or_eq_southPole_zero x with rfl | rfl <;> simp
  right_inv i := by
    fin_cases i <;> simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.sphere0Equiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.sphere0Equiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.sphere0Equiv ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.sphere0Equiv

instance _root_.Submission.DifferentialGeometry.Topology.SingularPair.Sphere.instFiniteElemEuclideanSpaceRealFinHAddNatOfNatUnitSphere : Finite (unitSphere 0) := Finite.of_equiv _ sphere0Equiv.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.instFiniteElemEuclideanSpaceRealFinHAddNatOfNatUnitSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.instFiniteElemEuclideanSpaceRealFinHAddNatOfNatUnitSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.instFiniteElemEuclideanSpaceRealFinHAddNatOfNatUnitSphere ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.instFiniteElemEuclideanSpaceRealFinHAddNatOfNatUnitSphere

instance _root_.Submission.DifferentialGeometry.Topology.SingularPair.Sphere.instDiscreteTopologyElemEuclideanSpaceRealFinHAddNatOfNatUnitSphere : DiscreteTopology (unitSphere 0) := inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.instDiscreteTopologyElemEuclideanSpaceRealFinHAddNatOfNatUnitSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.instDiscreteTopologyElemEuclideanSpaceRealFinHAddNatOfNatUnitSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.instDiscreteTopologyElemEuclideanSpaceRealFinHAddNatOfNatUnitSphere ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.instDiscreteTopologyElemEuclideanSpaceRealFinHAddNatOfNatUnitSphere

instance _root_.Submission.DifferentialGeometry.Topology.SingularPair.Sphere.instTotallyDisconnectedSpaceElemEuclideanSpaceRealFinHAddNatOfNatUnitSphere : TotallyDisconnectedSpace (unitSphere 0) := inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.instTotallyDisconnectedSpaceElemEuclideanSpaceRealFinHAddNatOfNatUnitSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.instTotallyDisconnectedSpaceElemEuclideanSpaceRealFinHAddNatOfNatUnitSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.instTotallyDisconnectedSpaceElemEuclideanSpaceRealFinHAddNatOfNatUnitSphere ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.instTotallyDisconnectedSpaceElemEuclideanSpaceRealFinHAddNatOfNatUnitSphere

def sphere0 : unitSphere 0 ≃ₜ Fin 2 := sphere0Equiv.toHomeomorphOfDiscrete

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.sphere0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.sphere0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.sphere0 ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.sphere0

def sphere0ULift : unitSphere 0 ≃ₜ ULift.{u} (Fin 2) := sphere0.trans Homeomorph.ulift.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.sphere0ULift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.sphere0ULift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.sphere0ULift ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.sphere0ULift

end Sphere

end DifferentialGeometry.Topology.SingularPair
