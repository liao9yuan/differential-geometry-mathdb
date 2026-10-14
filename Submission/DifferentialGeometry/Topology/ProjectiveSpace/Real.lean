import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Ball.Action
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homeomorph.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set

namespace DifferentialGeometry

noncomputable def realProjectiveSpaceAntipodalHomeomorph
    (E : Type*) [NormedAddCommGroup E] :
    Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1 :=
  (Homeomorph.neg E).subtype (by
    intro x
    simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveSpaceAntipodalHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveSpaceAntipodalHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveSpaceAntipodalHomeomorph ``Submission.DifferentialGeometry.realProjectiveSpaceAntipodalHomeomorph

theorem realProjectiveSpaceAntipodalHomeomorph_coe
    {E : Type*} [NormedAddCommGroup E]
    (x : Metric.sphere (0 : E) 1) :
    (realProjectiveSpaceAntipodalHomeomorph E x : E) = -(x : E) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveSpaceAntipodalHomeomorph_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveSpaceAntipodalHomeomorph_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveSpaceAntipodalHomeomorph_coe ``Submission.DifferentialGeometry.realProjectiveSpaceAntipodalHomeomorph_coe

theorem realProjectiveSpaceAntipodalHomeomorph_fixed_point_free
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (x : Metric.sphere (0 : E) 1) :
    realProjectiveSpaceAntipodalHomeomorph E x ≠ x := by
  intro h
  apply ne_neg_of_mem_unit_sphere Real x
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveSpaceAntipodalHomeomorph_fixed_point_free then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveSpaceAntipodalHomeomorph_fixed_point_free"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveSpaceAntipodalHomeomorph_fixed_point_free ``Submission.DifferentialGeometry.realProjectiveSpaceAntipodalHomeomorph_fixed_point_free

private theorem realProjectiveSpaceAntipodalHomeomorph_sq
    (E : Type*) [NormedAddCommGroup E] :
    (realProjectiveSpaceAntipodalHomeomorph E).toEquiv ^ 2 = 1 := by
  apply Equiv.ext
  intro x
  change realProjectiveSpaceAntipodalHomeomorph E
      (realProjectiveSpaceAntipodalHomeomorph E x) = x
  apply Subtype.ext
  rw [realProjectiveSpaceAntipodalHomeomorph_coe,
    realProjectiveSpaceAntipodalHomeomorph_coe]
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.realProjectiveSpaceAntipodalHomeomorph_sq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.realProjectiveSpaceAntipodalHomeomorph_sq target :: scope.openDecls } }

theorem realProjectiveSpaceAntipodalHomeomorph_orderOf
    (E : Type*) [NormedAddCommGroup E] [NormedSpace Real E] [Nontrivial E] :
    orderOf (realProjectiveSpaceAntipodalHomeomorph E).toEquiv = 2 := by
  apply orderOf_eq_prime
  · exact realProjectiveSpaceAntipodalHomeomorph_sq E
  · intro h
    obtain ⟨x, hx⟩ := NormedSpace.sphere_nonempty (E := E).2 zero_le_one
    let y : Metric.sphere (0 : E) 1 := ⟨x, hx⟩
    exact realProjectiveSpaceAntipodalHomeomorph_fixed_point_free y (by
      change (realProjectiveSpaceAntipodalHomeomorph E).toEquiv y = y
      rw [h]
      rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveSpaceAntipodalHomeomorph_orderOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveSpaceAntipodalHomeomorph_orderOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveSpaceAntipodalHomeomorph_orderOf ``Submission.DifferentialGeometry.realProjectiveSpaceAntipodalHomeomorph_orderOf

private theorem mem_zpowers_realProjectiveSpaceAntipodalHomeomorph_iff
    {E : Type*} [NormedAddCommGroup E]
    (psi : Equiv.Perm (Metric.sphere (0 : E) 1)) :
    psi ∈ Subgroup.zpowers
        (realProjectiveSpaceAntipodalHomeomorph E).toEquiv ↔
      psi = 1 ∨
        psi = (realProjectiveSpaceAntipodalHomeomorph E).toEquiv := by
  classical
  have hfinite : IsOfFinOrder
      (realProjectiveSpaceAntipodalHomeomorph E).toEquiv :=
    isOfFinOrder_iff_pow_eq_one.mpr
      ⟨2, Nat.zero_lt_two,
        realProjectiveSpaceAntipodalHomeomorph_sq E⟩
  have hle : orderOf
      (realProjectiveSpaceAntipodalHomeomorph E).toEquiv ≤ 2 :=
    Nat.le_of_dvd Nat.zero_lt_two
      (orderOf_dvd_of_pow_eq_one
        (realProjectiveSpaceAntipodalHomeomorph_sq E))
  constructor
  · intro hpsi
    have hrange := hfinite.mem_zpowers_iff_mem_range_orderOf.mp hpsi
    rcases Finset.mem_image.mp hrange with ⟨n, hn, rfl⟩
    simp only [Finset.mem_range] at hn
    have hn2 : n < 2 := lt_of_lt_of_le hn hle
    interval_cases n <;> simp
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

run_cmd do
  let target := ``Submission.DifferentialGeometry.mem_zpowers_realProjectiveSpaceAntipodalHomeomorph_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.mem_zpowers_realProjectiveSpaceAntipodalHomeomorph_iff target :: scope.openDecls } }

noncomputable def realProjectiveSpaceAntipodalGroup
    (E : Type*) [NormedAddCommGroup E] :
    Subgroup (Equiv.Perm (Metric.sphere (0 : E) 1)) :=
  Subgroup.zpowers (realProjectiveSpaceAntipodalHomeomorph E).toEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveSpaceAntipodalGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveSpaceAntipodalGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveSpaceAntipodalGroup ``Submission.DifferentialGeometry.realProjectiveSpaceAntipodalGroup

instance realProjectiveSpaceAntipodalGroupMulAction
    (E : Type*) [NormedAddCommGroup E] :
    MulAction (realProjectiveSpaceAntipodalGroup E)
      (Metric.sphere (0 : E) 1) :=
  MulAction.instMulAction (realProjectiveSpaceAntipodalGroup E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveSpaceAntipodalGroupMulAction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveSpaceAntipodalGroupMulAction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveSpaceAntipodalGroupMulAction ``Submission.DifferentialGeometry.realProjectiveSpaceAntipodalGroupMulAction

noncomputable instance realProjectiveSpaceAntipodalGroupFinite
    (E : Type*) [NormedAddCommGroup E] :
    Finite (realProjectiveSpaceAntipodalGroup E) := by
  have hfinite : IsOfFinOrder
      (realProjectiveSpaceAntipodalHomeomorph E).toEquiv :=
    isOfFinOrder_iff_pow_eq_one.mpr
      ⟨2, Nat.zero_lt_two,
        realProjectiveSpaceAntipodalHomeomorph_sq E⟩
  exact Finite.of_equiv
    (Fin (orderOf (realProjectiveSpaceAntipodalHomeomorph E).toEquiv))
    (finEquivZPowers hfinite)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveSpaceAntipodalGroupFinite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveSpaceAntipodalGroupFinite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveSpaceAntipodalGroupFinite ``Submission.DifferentialGeometry.realProjectiveSpaceAntipodalGroupFinite

theorem realProjectiveSpaceAntipodalGroup_eq_one_or_generator
    {E : Type*} [NormedAddCommGroup E]
    (psi : realProjectiveSpaceAntipodalGroup E) :
    psi.1 = 1 ∨
      psi.1 = (realProjectiveSpaceAntipodalHomeomorph E).toEquiv :=
  (mem_zpowers_realProjectiveSpaceAntipodalHomeomorph_iff psi.1).mp psi.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveSpaceAntipodalGroup_eq_one_or_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveSpaceAntipodalGroup_eq_one_or_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveSpaceAntipodalGroup_eq_one_or_generator ``Submission.DifferentialGeometry.realProjectiveSpaceAntipodalGroup_eq_one_or_generator

instance realProjectiveSpaceAntipodalGroupContinuousConstSMul
    (E : Type*) [NormedAddCommGroup E] :
    ContinuousConstSMul (realProjectiveSpaceAntipodalGroup E)
      (Metric.sphere (0 : E) 1) where
  continuous_const_smul psi := by
    rcases realProjectiveSpaceAntipodalGroup_eq_one_or_generator psi with
      hpsi | hpsi
    · change Continuous (psi.1 : Metric.sphere (0 : E) 1 → _)
      rw [hpsi]
      exact continuous_id
    · change Continuous (psi.1 : Metric.sphere (0 : E) 1 → _)
      rw [hpsi]
      exact (realProjectiveSpaceAntipodalHomeomorph E).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveSpaceAntipodalGroupContinuousConstSMul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveSpaceAntipodalGroupContinuousConstSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveSpaceAntipodalGroupContinuousConstSMul ``Submission.DifferentialGeometry.realProjectiveSpaceAntipodalGroupContinuousConstSMul

instance realProjectiveSpaceAntipodalGroupIsCancelSMul
    (E : Type*) [NormedAddCommGroup E] [inst : NormedSpace Real E] :
    IsCancelSMul (realProjectiveSpaceAntipodalGroup E)
      (Metric.sphere (0 : E) 1) := by
  let _ := inst
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro psi x hpsi
  rcases realProjectiveSpaceAntipodalGroup_eq_one_or_generator psi with
    hone | hanti
  · exact Subtype.ext hone
  · exfalso
    change psi.1 x = x at hpsi
    rw [hanti] at hpsi
    exact realProjectiveSpaceAntipodalHomeomorph_fixed_point_free x hpsi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveSpaceAntipodalGroupIsCancelSMul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveSpaceAntipodalGroupIsCancelSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveSpaceAntipodalGroupIsCancelSMul ``Submission.DifferentialGeometry.realProjectiveSpaceAntipodalGroupIsCancelSMul

theorem realProjectiveSpaceAntipodalGroup_smul_eq_self_or_neg
    {E : Type*} [NormedAddCommGroup E]
    (psi : realProjectiveSpaceAntipodalGroup E)
    (x : Metric.sphere (0 : E) 1) :
    psi • x = x ∨ psi • x = -x := by
  rcases realProjectiveSpaceAntipodalGroup_eq_one_or_generator psi with
    hone | hanti
  · left
    change psi.1 x = x
    rw [hone]
    rfl
  · right
    change psi.1 x = -x
    rw [hanti]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveSpaceAntipodalGroup_smul_eq_self_or_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveSpaceAntipodalGroup_smul_eq_self_or_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveSpaceAntipodalGroup_smul_eq_self_or_neg ``Submission.DifferentialGeometry.realProjectiveSpaceAntipodalGroup_smul_eq_self_or_neg

abbrev RealProjectiveSpace
    (E : Type*) [NormedAddCommGroup E] :=
  MulAction.orbitRel.Quotient (realProjectiveSpaceAntipodalGroup E)
    (Metric.sphere (0 : E) 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.RealProjectiveSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.RealProjectiveSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.RealProjectiveSpace ``Submission.DifferentialGeometry.RealProjectiveSpace

def realProjectiveSpaceQuotientMap
    {E : Type*} [NormedAddCommGroup E]
    (x : Metric.sphere (0 : E) 1) :
    RealProjectiveSpace E :=
  Quotient.mk'' x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveSpaceQuotientMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveSpaceQuotientMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveSpaceQuotientMap ``Submission.DifferentialGeometry.realProjectiveSpaceQuotientMap

theorem realProjectiveSpaceQuotientMap_isOpenQuotientMap
    {E : Type*} [NormedAddCommGroup E] :
    IsOpenQuotientMap (realProjectiveSpaceQuotientMap (E := E)) :=
  MulAction.isOpenQuotientMap_quotientMk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveSpaceQuotientMap_isOpenQuotientMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveSpaceQuotientMap_isOpenQuotientMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveSpaceQuotientMap_isOpenQuotientMap ``Submission.DifferentialGeometry.realProjectiveSpaceQuotientMap_isOpenQuotientMap

theorem realProjectiveSpaceQuotientMap_eq_iff
    {E : Type*} [NormedAddCommGroup E]
    {x y : Metric.sphere (0 : E) 1} :
    realProjectiveSpaceQuotientMap x = realProjectiveSpaceQuotientMap y ↔
      x = y ∨ (x : E) = -(y : E) := by
  constructor
  · intro hxy
    rcases Quotient.exact hxy with ⟨psi, hpsi⟩
    rcases realProjectiveSpaceAntipodalGroup_eq_one_or_generator psi with
      hone | hanti
    · left
      rw [← hpsi]
      change psi.1 y = y
      rw [hone]
      rfl
    · right
      rw [← hpsi]
      change (psi.1 y : E) = _
      rw [hanti]
      exact realProjectiveSpaceAntipodalHomeomorph_coe y
  · rintro (rfl | hxy)
    · rfl
    · apply Quotient.sound
      let psi : realProjectiveSpaceAntipodalGroup E :=
        ⟨(realProjectiveSpaceAntipodalHomeomorph E).toEquiv, by
          exact Subgroup.mem_zpowers _⟩
      refine ⟨psi, ?_⟩
      change (realProjectiveSpaceAntipodalHomeomorph E).toEquiv y = x
      apply Subtype.ext
      change (realProjectiveSpaceAntipodalHomeomorph E y : E) = (x : E)
      rw [realProjectiveSpaceAntipodalHomeomorph_coe]
      exact hxy.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveSpaceQuotientMap_eq_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveSpaceQuotientMap_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveSpaceQuotientMap_eq_iff ``Submission.DifferentialGeometry.realProjectiveSpaceQuotientMap_eq_iff

theorem realProjectiveSpaceQuotientMap_isQuotientCoveringMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] :
    IsQuotientCoveringMap (realProjectiveSpaceQuotientMap (E := E))
      (realProjectiveSpaceAntipodalGroup E) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveSpaceQuotientMap_isQuotientCoveringMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveSpaceQuotientMap_isQuotientCoveringMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveSpaceQuotientMap_isQuotientCoveringMap ``Submission.DifferentialGeometry.realProjectiveSpaceQuotientMap_isQuotientCoveringMap

theorem realProjectiveSpaceQuotientMap_isCoveringMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] :
    IsCoveringMap (realProjectiveSpaceQuotientMap (E := E)) :=
  realProjectiveSpaceQuotientMap_isQuotientCoveringMap.isCoveringMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveSpaceQuotientMap_isCoveringMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveSpaceQuotientMap_isCoveringMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveSpaceQuotientMap_isCoveringMap ``Submission.DifferentialGeometry.realProjectiveSpaceQuotientMap_isCoveringMap

theorem realProjectiveSpaceQuotientMap_surjective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] :
    Function.Surjective (realProjectiveSpaceQuotientMap (E := E)) :=
  realProjectiveSpaceQuotientMap_isQuotientCoveringMap.surjective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveSpaceQuotientMap_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveSpaceQuotientMap_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveSpaceQuotientMap_surjective ``Submission.DifferentialGeometry.realProjectiveSpaceQuotientMap_surjective

noncomputable def realProjectivePlaneAntipodalHomeomorph :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 :=
  realProjectiveSpaceAntipodalHomeomorph _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectivePlaneAntipodalHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectivePlaneAntipodalHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectivePlaneAntipodalHomeomorph ``Submission.DifferentialGeometry.realProjectivePlaneAntipodalHomeomorph

theorem realProjectivePlaneAntipodalHomeomorph_coe
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    (realProjectivePlaneAntipodalHomeomorph x :
        EuclideanSpace Real (Fin 3)) =
      -(x : EuclideanSpace Real (Fin 3)) :=
  realProjectiveSpaceAntipodalHomeomorph_coe x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectivePlaneAntipodalHomeomorph_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectivePlaneAntipodalHomeomorph_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectivePlaneAntipodalHomeomorph_coe ``Submission.DifferentialGeometry.realProjectivePlaneAntipodalHomeomorph_coe

theorem realProjectivePlaneAntipodalHomeomorph_fixed_point_free
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    realProjectivePlaneAntipodalHomeomorph x ≠ x :=
  realProjectiveSpaceAntipodalHomeomorph_fixed_point_free x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectivePlaneAntipodalHomeomorph_fixed_point_free then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectivePlaneAntipodalHomeomorph_fixed_point_free"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectivePlaneAntipodalHomeomorph_fixed_point_free ``Submission.DifferentialGeometry.realProjectivePlaneAntipodalHomeomorph_fixed_point_free

theorem realProjectivePlaneAntipodalHomeomorph_orderOf :
    orderOf realProjectivePlaneAntipodalHomeomorph.toEquiv = 2 :=
  realProjectiveSpaceAntipodalHomeomorph_orderOf _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectivePlaneAntipodalHomeomorph_orderOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectivePlaneAntipodalHomeomorph_orderOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectivePlaneAntipodalHomeomorph_orderOf ``Submission.DifferentialGeometry.realProjectivePlaneAntipodalHomeomorph_orderOf

abbrev realProjectivePlaneAntipodalGroup :=
  realProjectiveSpaceAntipodalGroup (EuclideanSpace Real (Fin 3))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectivePlaneAntipodalGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectivePlaneAntipodalGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectivePlaneAntipodalGroup ``Submission.DifferentialGeometry.realProjectivePlaneAntipodalGroup

instance realProjectivePlaneAntipodalGroupMulAction :
    MulAction realProjectivePlaneAntipodalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
  realProjectiveSpaceAntipodalGroupMulAction _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectivePlaneAntipodalGroupMulAction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectivePlaneAntipodalGroupMulAction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectivePlaneAntipodalGroupMulAction ``Submission.DifferentialGeometry.realProjectivePlaneAntipodalGroupMulAction

noncomputable instance realProjectivePlaneAntipodalGroupFinite :
    Finite realProjectivePlaneAntipodalGroup :=
  realProjectiveSpaceAntipodalGroupFinite _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectivePlaneAntipodalGroupFinite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectivePlaneAntipodalGroupFinite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectivePlaneAntipodalGroupFinite ``Submission.DifferentialGeometry.realProjectivePlaneAntipodalGroupFinite

instance realProjectivePlaneAntipodalGroupContinuousConstSMul :
    ContinuousConstSMul realProjectivePlaneAntipodalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
  realProjectiveSpaceAntipodalGroupContinuousConstSMul _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectivePlaneAntipodalGroupContinuousConstSMul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectivePlaneAntipodalGroupContinuousConstSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectivePlaneAntipodalGroupContinuousConstSMul ``Submission.DifferentialGeometry.realProjectivePlaneAntipodalGroupContinuousConstSMul

instance realProjectivePlaneAntipodalGroupIsCancelSMul :
    IsCancelSMul realProjectivePlaneAntipodalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
  realProjectiveSpaceAntipodalGroupIsCancelSMul _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectivePlaneAntipodalGroupIsCancelSMul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectivePlaneAntipodalGroupIsCancelSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectivePlaneAntipodalGroupIsCancelSMul ``Submission.DifferentialGeometry.realProjectivePlaneAntipodalGroupIsCancelSMul

abbrev RealProjectivePlane :=
  RealProjectiveSpace (EuclideanSpace Real (Fin 3))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.RealProjectivePlane then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.RealProjectivePlane"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.RealProjectivePlane ``Submission.DifferentialGeometry.RealProjectivePlane

abbrev RealProjectiveThreeSpace :=
  RealProjectiveSpace (EuclideanSpace Real (Fin 4))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.RealProjectiveThreeSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.RealProjectiveThreeSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.RealProjectiveThreeSpace ``Submission.DifferentialGeometry.RealProjectiveThreeSpace

def realProjectivePlaneQuotientMap
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    RealProjectivePlane :=
  realProjectiveSpaceQuotientMap x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectivePlaneQuotientMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectivePlaneQuotientMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectivePlaneQuotientMap ``Submission.DifferentialGeometry.realProjectivePlaneQuotientMap

theorem realProjectivePlaneQuotientMap_isOpenQuotientMap :
    IsOpenQuotientMap realProjectivePlaneQuotientMap :=
  realProjectiveSpaceQuotientMap_isOpenQuotientMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectivePlaneQuotientMap_isOpenQuotientMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectivePlaneQuotientMap_isOpenQuotientMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectivePlaneQuotientMap_isOpenQuotientMap ``Submission.DifferentialGeometry.realProjectivePlaneQuotientMap_isOpenQuotientMap

theorem realProjectivePlaneQuotientMap_isQuotientCoveringMap :
    IsQuotientCoveringMap realProjectivePlaneQuotientMap
      realProjectivePlaneAntipodalGroup :=
  realProjectiveSpaceQuotientMap_isQuotientCoveringMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectivePlaneQuotientMap_isQuotientCoveringMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectivePlaneQuotientMap_isQuotientCoveringMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectivePlaneQuotientMap_isQuotientCoveringMap ``Submission.DifferentialGeometry.realProjectivePlaneQuotientMap_isQuotientCoveringMap

theorem realProjectivePlaneQuotientMap_isCoveringMap :
    IsCoveringMap realProjectivePlaneQuotientMap :=
  realProjectiveSpaceQuotientMap_isCoveringMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectivePlaneQuotientMap_isCoveringMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectivePlaneQuotientMap_isCoveringMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectivePlaneQuotientMap_isCoveringMap ``Submission.DifferentialGeometry.realProjectivePlaneQuotientMap_isCoveringMap

theorem realProjectivePlaneQuotientMap_surjective :
    Function.Surjective realProjectivePlaneQuotientMap :=
  realProjectiveSpaceQuotientMap_surjective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectivePlaneQuotientMap_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectivePlaneQuotientMap_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectivePlaneQuotientMap_surjective ``Submission.DifferentialGeometry.realProjectivePlaneQuotientMap_surjective

theorem realProjectivePlaneQuotientMap_eq_iff
    {x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1} :
    realProjectivePlaneQuotientMap x = realProjectivePlaneQuotientMap y ↔
      x = y ∨
        (x : EuclideanSpace Real (Fin 3)) =
          -(y : EuclideanSpace Real (Fin 3)) :=
  realProjectiveSpaceQuotientMap_eq_iff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectivePlaneQuotientMap_eq_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectivePlaneQuotientMap_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectivePlaneQuotientMap_eq_iff ``Submission.DifferentialGeometry.realProjectivePlaneQuotientMap_eq_iff

end DifferentialGeometry

end

section
namespace DifferentialGeometry

theorem realProjectiveSpaceQuotientMap_normalize_eq_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v w : E} (hv : v ≠ 0) (hw : w ≠ 0) :
    realProjectiveSpaceQuotientMap
        ⟨NormedSpace.normalize v,
          mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hv)⟩ =
      realProjectiveSpaceQuotientMap
        ⟨NormedSpace.normalize w,
          mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hw)⟩ ↔
      ∃ c : ℝ, c ≠ 0 ∧ v = c • w := by
  rw [realProjectiveSpaceQuotientMap_eq_iff]
  constructor
  · rintro (h | h)
    · have hnorm : NormedSpace.normalize v = NormedSpace.normalize w :=
        congrArg Subtype.val h
      refine ⟨‖v‖ * ‖w‖⁻¹,
        mul_ne_zero (norm_ne_zero_iff.mpr hv)
          (inv_ne_zero (norm_ne_zero_iff.mpr hw)), ?_⟩
      calc
        v = ‖v‖ • NormedSpace.normalize v :=
          (NormedSpace.norm_smul_normalize v).symm
        _ = ‖v‖ • NormedSpace.normalize w := congrArg (‖v‖ • ·) hnorm
        _ = (‖v‖ * ‖w‖⁻¹) • w := by rw [NormedSpace.normalize, smul_smul]
    · change NormedSpace.normalize v = -NormedSpace.normalize w at h
      refine ⟨-(‖v‖ * ‖w‖⁻¹),
        neg_ne_zero.mpr (mul_ne_zero (norm_ne_zero_iff.mpr hv)
          (inv_ne_zero (norm_ne_zero_iff.mpr hw))), ?_⟩
      calc
        v = ‖v‖ • NormedSpace.normalize v :=
          (NormedSpace.norm_smul_normalize v).symm
        _ = ‖v‖ • (-NormedSpace.normalize w) := congrArg (‖v‖ • ·) h
        _ = -(‖v‖ * ‖w‖⁻¹) • w := by
          rw [NormedSpace.normalize, smul_neg, smul_smul, neg_smul]
  · rintro ⟨c, hc, h⟩
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · right
      change NormedSpace.normalize v = -NormedSpace.normalize w
      rw [h, NormedSpace.normalize_smul_of_neg hneg]
    · left
      apply Subtype.ext
      change NormedSpace.normalize v = NormedSpace.normalize w
      rw [h, NormedSpace.normalize_smul_of_pos hpos]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.realProjectiveSpaceQuotientMap_normalize_eq_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.realProjectiveSpaceQuotientMap_normalize_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.realProjectiveSpaceQuotientMap_normalize_eq_iff ``Submission.DifferentialGeometry.realProjectiveSpaceQuotientMap_normalize_eq_iff

end DifferentialGeometry

end
