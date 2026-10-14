import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.Basic
import Mathlib.Topology.Path
import Mathlib.Topology.Maps.Proper.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The actual evaluation fiber and based interval paths

The quotient circle is related to the path-space loop model by actual inverse
continuous maps. The circle parameter runs once from zero to one, fixing the
parameter convention needed by based adjunction.
-/

noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

/-- The actual fiber of evaluation at circle parameter zero. -/
abbrev basedCircleLoop {Q : Type*} [TopologicalSpace Q] (q : Q) :=
  {γ : freeLoop Q // γ 0 = q}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedCircleLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedCircleLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedCircleLoop ``Submission.DifferentialGeometry.Topology.basedCircleLoop

/-- The closed unit interval covers the quotient circle. -/
theorem unitInterval_to_loopCircle_surjective :
    Surjective (fun t : unitInterval => (t.val : loopCircle)) := by
  intro θ
  have hmem : θ ∈ (fun t : ℝ => (t : loopCircle)) '' _root_.Set.Icc 0 1 := by
    have h : (fun t : ℝ => (t : loopCircle)) '' _root_.Set.Icc 0 1 = univ := by
      simpa only [zero_add] using AddCircle.coe_image_Icc_eq (1 : ℝ) 0
    rw [h]
    exact _root_.Set.mem_univ θ
  obtain ⟨t, ht, hθ⟩ := hmem
  exact ⟨⟨t, ht⟩, hθ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.unitInterval_to_loopCircle_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.unitInterval_to_loopCircle_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.unitInterval_to_loopCircle_surjective ``Submission.DifferentialGeometry.Topology.unitInterval_to_loopCircle_surjective

/-- This quotient remains a quotient after multiplication by any parameter
space, because the interval-to-circle map is proper. -/
theorem unitInterval_to_loopCircle_prod_quotient (K : Type*) [TopologicalSpace K] :
    _root_.Topology.IsQuotientMap
      (Prod.map (id : K → K) (fun t : unitInterval => (t.val : loopCircle))) := by
  have hc : Continuous (fun t : unitInterval => (t.val : loopCircle)) :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val
  have hp : IsProperMap (Prod.map (id : K → K)
      (fun t : unitInterval => (t.val : loopCircle))) := isProperMap_id.prodMap hc.isProperMap
  exact hp.isClosedMap.isQuotientMap hp.continuous
    ((_root_.Function.surjective_id : _root_.Function.Surjective (id : K → K)).prodMap unitInterval_to_loopCircle_surjective)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.unitInterval_to_loopCircle_prod_quotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.unitInterval_to_loopCircle_prod_quotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.unitInterval_to_loopCircle_prod_quotient ``Submission.DifferentialGeometry.Topology.unitInterval_to_loopCircle_prod_quotient

variable {Q : Type*} [TopologicalSpace Q] {q : Q}

/-- Descend an actual based path, whose two endpoints agree, to the circle. -/
def pathToCircle (p : Path q q) : freeLoop Q :=
  ⟨AddCircle.liftIco 1 0 p.extend,
    AddCircle.liftIco_zero_continuous (by rw [p.extend_zero, p.extend_one]) p.continuous_extend.continuousOn⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathToCircle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathToCircle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathToCircle ``Submission.DifferentialGeometry.Topology.pathToCircle

theorem pathToCircle_zero (p : Path q q) : pathToCircle p 0 = q := by
  change AddCircle.liftIco 1 0 p.extend ((0 : ℝ) : loopCircle) = q
  rw [AddCircle.liftIco_zero_coe_apply (by norm_num : (0 : ℝ) ∈ Ico 0 1), p.extend_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathToCircle_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathToCircle_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathToCircle_zero ``Submission.DifferentialGeometry.Topology.pathToCircle_zero

/-- The descended circle loop agrees exactly with the original path on the
whole closed interval, including both identified endpoints. -/
theorem pathToCircle_coe (p : Path q q) (t : unitInterval) :
    pathToCircle p (t.val : loopCircle) = p t := by
  by_cases ht : (t : ℝ) < 1
  · change AddCircle.liftIco 1 0 p.extend (t.val : loopCircle) = p t
    rw [AddCircle.liftIco_zero_coe_apply ⟨t.property.1, ht⟩]
    exact p.extend_extends' t
  · have ht1 : t = 1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt ht))
    subst t
    change pathToCircle p ((1 : ℝ) : loopCircle) = p 1
    rw [AddCircle.coe_period, Path.target]
    exact pathToCircle_zero p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathToCircle_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathToCircle_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathToCircle_coe ``Submission.DifferentialGeometry.Topology.pathToCircle_coe

/-- Descent is continuous for the actual compact-open path and loop topologies. -/
theorem continuous_pathToCircle : Continuous (pathToCircle (q := q)) := by
  apply _root_.ContinuousMap.continuous_of_continuous_uncurry
  apply (unitInterval_to_loopCircle_prod_quotient (Path q q)).continuous_iff.mpr
  have hc : Continuous (fun p : Path q q × unitInterval => p.1 p.2) :=
    Path.continuous_uncurry_iff.mpr continuous_id
  apply hc.congr
  intro p
  exact (pathToCircle_coe p.1 p.2).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_pathToCircle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_pathToCircle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_pathToCircle ``Submission.DifferentialGeometry.Topology.continuous_pathToCircle

/-- Restrict the actual circle loop to one full closed parameter interval. -/
def circleToPath (γ : basedCircleLoop q) : Path q q where
  toFun t := γ.val (t.val : loopCircle)
  continuous_toFun := γ.val.continuous.comp
    ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val)
  source' := γ.property
  target' := by
    change γ.val ((1 : ℝ) : loopCircle) = q
    simpa only [AddCircle.coe_period] using γ.property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.circleToPath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.circleToPath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.circleToPath ``Submission.DifferentialGeometry.Topology.circleToPath

/-- Restriction is continuous in the actual mapping-space topologies. -/
theorem continuous_circleToPath : Continuous (circleToPath (q := q)) := by
  apply Path.continuous_uncurry_iff.mp
  exact (continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk
    ((AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_subtype_val.comp continuous_snd))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_circleToPath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_circleToPath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_circleToPath ``Submission.DifferentialGeometry.Topology.continuous_circleToPath

/-- The actual evaluation fiber is homeomorphic to the based path-loop space.
Both composites are proved pointwise identities on the original maps. -/
def basedPathCircleHomeomorph (q : Q) : Path q q ≃ₜ basedCircleLoop q where
  toFun p := ⟨pathToCircle p, pathToCircle_zero p⟩
  invFun := circleToPath
  left_inv p := by ext t; exact pathToCircle_coe p t
  right_inv γ := by
    apply Subtype.ext
    ext θ
    obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
    exact pathToCircle_coe (circleToPath γ) t
  continuous_toFun := continuous_pathToCircle.subtype_mk _
  continuous_invFun := continuous_circleToPath

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedPathCircleHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedPathCircleHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedPathCircleHomeomorph ``Submission.DifferentialGeometry.Topology.basedPathCircleHomeomorph

end DifferentialGeometry.Topology
