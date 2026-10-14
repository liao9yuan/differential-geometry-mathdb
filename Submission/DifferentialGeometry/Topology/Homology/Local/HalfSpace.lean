import Submission.DifferentialGeometry.Topology.Homology.Local.Euclidean
import Mathlib.Geometry.Manifold.Instances.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Set _root_.Metric
namespace DifferentialGeometry.Homology
variable {n : ℕ} [NeZero n] (p : EuclideanHalfSpace n)


def puncturedHalfSpaceHomeomorph :
    ({p}ᶜ : Set (EuclideanHalfSpace n)) ≃ₜ
      {v : EuclideanSpace ℝ (Fin n) | 0 ≤ v 0 ∧ v ≠ p.val} where
  toFun x := ⟨x.val.val, x.val.property, fun h => x.property (Subtype.ext h)⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, fun h => x.property.2 (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.puncturedHalfSpaceHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.puncturedHalfSpaceHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.puncturedHalfSpaceHomeomorph ``Submission.DifferentialGeometry.Homology.puncturedHalfSpaceHomeomorph


theorem contractibleSpace_euclideanHalfSpace : ContractibleSpace (EuclideanHalfSpace n) :=
  EuclideanHalfSpace.convex.contractibleSpace ⟨0, by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.contractibleSpace_euclideanHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.contractibleSpace_euclideanHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.contractibleSpace_euclideanHalfSpace ``Submission.DifferentialGeometry.Homology.contractibleSpace_euclideanHalfSpace


theorem contractibleSpace_puncturedHalfSpace (hp : p.val 0 = 0) :
    ContractibleSpace ({p}ᶜ : Set (EuclideanHalfSpace n)) := by
  let c : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => (1 : ℝ))
  have hc : c 0 = 1 := rfl
  have hcS : c ∈ {v : EuclideanSpace ℝ (Fin n) | 0 ≤ v 0 ∧ v ≠ p.val} := by
    refine ⟨by rw [hc]; norm_num, ?_⟩
    intro h
    have he := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v 0) h
    rw [hc, hp] at he
    norm_num at he
  have hs : StarConvex ℝ c {v : EuclideanSpace ℝ (Fin n) | 0 ≤ v 0 ∧ v ≠ p.val} := by
    intro y hy a b ha hb hab
    have he : (a • c + b • y) 0 = a + b * y 0 := by
      simp [hc]
    refine ⟨by rw [he]; exact add_nonneg ha (mul_nonneg hb hy.1), ?_⟩
    by_cases haz : a = 0
    · have hb1 : b = 1 := by linarith
      simpa only [haz, hb1, zero_smul, one_smul, zero_add] using hy.2
    · intro h
      have hh := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v 0) h
      rw [he, hp] at hh
      have : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
      have : 0 ≤ b * y 0 := mul_nonneg hb hy.1
      linarith
  let := hs.contractibleSpace ⟨c, hcS⟩
  exact (puncturedHalfSpaceHomeomorph p).contractibleSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.contractibleSpace_puncturedHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.contractibleSpace_puncturedHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.contractibleSpace_puncturedHalfSpace ``Submission.DifferentialGeometry.Homology.contractibleSpace_puncturedHalfSpace

variable (k : Type) [Field k]


theorem finiteHomologyType_localHalfSpace (hp : p.val 0 = 0) :
    DifferentialGeometry.HomologicalComplex.finiteHomologyType
      (relativeChainComplex (TopCat.of (EuclideanHalfSpace n))
        ({p}ᶜ : Set (EuclideanHalfSpace n)) (ModuleCat.of k k)) := by
  let := contractibleSpace_euclideanHalfSpace (n := n)
  let := contractibleSpace_puncturedHalfSpace p hp
  exact finiteHomologyType_relativeChainComplex _ _ k
    (finiteHomologyType_of_contractible k) (finiteHomologyType_of_contractible k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.finiteHomologyType_localHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.finiteHomologyType_localHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.finiteHomologyType_localHalfSpace ``Submission.DifferentialGeometry.Homology.finiteHomologyType_localHalfSpace


theorem relativeEulerChar_localHalfSpace (hp : p.val 0 = 0) :
    relativeEulerChar (TopCat.of (EuclideanHalfSpace n))
      ({p}ᶜ : Set (EuclideanHalfSpace n)) k = 0 := by
  let := contractibleSpace_euclideanHalfSpace (n := n)
  let := contractibleSpace_puncturedHalfSpace p hp
  rw [relativeEulerChar_eq_sub _ _ k (finiteHomologyType_of_contractible k)
    (finiteHomologyType_of_contractible k), eulerChar_of_contractible,
    eulerChar_of_contractible, sub_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.relativeEulerChar_localHalfSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.relativeEulerChar_localHalfSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.relativeEulerChar_localHalfSpace ``Submission.DifferentialGeometry.Homology.relativeEulerChar_localHalfSpace

end DifferentialGeometry.Homology
