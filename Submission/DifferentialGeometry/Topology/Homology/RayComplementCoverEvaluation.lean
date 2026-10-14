import Submission.DifferentialGeometry.Topology.Homology.ContractibleCoverOneEvaluation
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.TotallyDisconnectedZero

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Metric _root_.Module

namespace DifferentialGeometry.Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def raySet (v : E) : Set E := Set.range fun t : _root_.Set.Ioi (0 : ℝ) => (t : ℝ) • v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.raySet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.raySet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.raySet ``Submission.DifferentialGeometry.Topology.raySet

theorem mem_raySet_iff {v : E} (hv : v ≠ 0) {x : E} :
    x ∈ raySet v ↔ x ∈ (Submodule.span ℝ {v} : Submodule ℝ E) ∧ 0 < _root_.Inner.inner ℝ x v := by
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v), ?_⟩
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    exact mul_pos t.property (pow_pos (norm_pos_iff.mpr hv) 2)
  · rintro ⟨hx, hpos⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have hc : 0 < c := by
      have h : c * ‖v‖ ^ 2 = _root_.Inner.inner ℝ (c • v) v := by
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      nlinarith [norm_pos_iff.mpr hv]
    exact ⟨⟨c, hc⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mem_raySet_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mem_raySet_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mem_raySet_iff ``Submission.DifferentialGeometry.Topology.mem_raySet_iff

def rayUnit {v : E} (hv : v ≠ 0) : _root_.Metric.sphere (0 : E) 1 :=
  ⟨‖v‖⁻¹ • v, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.rayUnit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.rayUnit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.rayUnit ``Submission.DifferentialGeometry.Topology.rayUnit

theorem compl_raySet_eq_preimage {v : E} (hv : v ≠ 0) :
    ({x : ({0}ᶜ : Set E) | (x : E) ∉ raySet v}) =
      (homeomorphUnitSphereProd E) ⁻¹'
        (({rayUnit hv}ᶜ : Set (_root_.Metric.sphere (0 : E) 1)) ×ˢ Set.univ) := by
  ext x
  simp only [Set.mem_ofPred_eq, _root_.Set.mem_preimage, _root_.Set.mem_prod, _root_.Set.mem_compl_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_univ,
    and_true, homeomorphUnitSphereProd_apply_fst_coe, Subtype.ext_iff]
  constructor
  · intro hx hc
    refine hx ⟨⟨‖(x : E)‖ * ‖v‖⁻¹, mul_pos (norm_pos_iff.mpr x.property)
      (inv_pos.mpr (norm_pos_iff.mpr hv))⟩, ?_⟩
    have h2 := congrArg (fun y : E => ‖(x : E)‖ • y) hc
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (norm_pos_iff.mpr x.property)), one_smul] at h2
    have h3 : (↑(rayUnit hv) : E) = ‖v‖⁻¹ • v := rfl
    change (‖(x : E)‖ * ‖v‖⁻¹) • v = (x : E)
    conv_rhs => rw [h2, h3]
    rw [smul_smul]
  · intro hx ht
    obtain ⟨t, ht'⟩ := ht
    refine hx ?_
    have ht0 : (t : ℝ) ≠ 0 := ne_of_gt t.property
    have hnorm : ‖(t : ℝ) • v‖ = (t : ℝ) * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos t.property]
    have key : ‖(t : ℝ) • v‖⁻¹ • ((t : ℝ) • v) = (‖v‖⁻¹ : ℝ) • v := by
      rw [hnorm, smul_smul]
      congr 1
      field_simp
    rw [← ht']
    simpa [rayUnit] using key

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.compl_raySet_eq_preimage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.compl_raySet_eq_preimage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.compl_raySet_eq_preimage ``Submission.DifferentialGeometry.Topology.compl_raySet_eq_preimage

section Evaluation

variable {X : Type u} [TopologicalSpace X]

theorem integralHomologyOneContractibleCoverEquiv_apply_functional [PathConnectedSpace X]
    (A B : Set X) [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (φ : integralSingularHomology 0 (subspaceIntersection A B) →ₗ[ℤ] ℤ)
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X 1)
    (hz : z ≫ (integralSingularChains X).d 1 0 = 0)
    (zA : integralSingularCoefficients ⟶ (integralSingularChains A).X 1)
    (zB : integralSingularCoefficients ⟶ (integralSingularChains B).X 1)
    (hsplit : zA ≫ (integralSingularChainMap (singularSubspaceInclusion A)).f 1 +
      zB ≫ (integralSingularChainMap (singularSubspaceInclusion B)).f 1 = z)
    (a : integralSingularCoefficients ⟶
      (integralSingularChains (subspaceIntersection A B)).X 0)
    (ha : a ≫ (integralSingularChainMap
        (singularSubspaceInclusion (subspaceIntersection A B))).f 0 =
      zB ≫ (integralSingularChains B).d 1 0) :
    φ (((integralHomologyOneContractibleCoverEquiv A B hA hB hcover)
        (((integralSingularChains X).liftCycles z 0
          ((ComplexShape.down ℕ).next_eq' (by simp)) hz ≫
          (integralSingularChains X).homologyπ 1) (ULift.up 1)) :
        integralSingularHomology 0 (subspaceIntersection A B))) =
      φ (((integralSingularChains (subspaceIntersection A B)).liftCycles a 0
        ChainComplex.next_nat_zero (by rw [(integralSingularChains
          (subspaceIntersection A B)).shape 0 0 (by simp), _root_.CategoryTheory.Limits.comp_zero]) ≫
        (integralSingularChains (subspaceIntersection A B)).homologyπ 0) (ULift.up 1)) := by
  rw [integralHomologyOneContractibleCoverEquiv_liftCycles_apply A B hA hB hcover z hz zA zB
    hsplit a ha]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralHomologyOneContractibleCoverEquiv_apply_functional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralHomologyOneContractibleCoverEquiv_apply_functional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralHomologyOneContractibleCoverEquiv_apply_functional ``Submission.DifferentialGeometry.Topology.integralHomologyOneContractibleCoverEquiv_apply_functional

theorem integralHomologyContractibleCoverEquiv_apply_functional (n : ℕ)
    (A B : Set X) [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (φ : integralSingularHomology (n + 1) (subspaceIntersection A B) →ₗ[ℤ] ℤ)
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 2))
    (hz : z ≫ (integralSingularChains X).d (n + 2) (n + 1) = 0)
    (zA : integralSingularCoefficients ⟶ (integralSingularChains A).X (n + 2))
    (zB : integralSingularCoefficients ⟶ (integralSingularChains B).X (n + 2))
    (hsplit : zA ≫ (integralSingularChainMap (singularSubspaceInclusion A)).f (n + 2) +
      zB ≫ (integralSingularChainMap (singularSubspaceInclusion B)).f (n + 2) = z)
    (a : integralSingularCoefficients ⟶
      (integralSingularChains (subspaceIntersection A B)).X (n + 1))
    (hac : a ≫ (integralSingularChains (subspaceIntersection A B)).d (n + 1) n = 0)
    (ha : a ≫ (integralSingularChainMap
        (singularSubspaceInclusion (subspaceIntersection A B))).f (n + 1) =
      zB ≫ (integralSingularChains B).d (n + 2) (n + 1)) :
    φ (integralHomologyContractibleCoverEquiv n A B hA hB hcover
        (((integralSingularChains X).liftCycles z (n + 1)
          ((ComplexShape.down ℕ).next_eq' (by rfl)) hz ≫
          (integralSingularChains X).homologyπ (n + 2)) (ULift.up 1))) =
      φ (((integralSingularChains (subspaceIntersection A B)).liftCycles a n
        ((ComplexShape.down ℕ).next_eq' (by rfl)) hac ≫
        (integralSingularChains (subspaceIntersection A B)).homologyπ (n + 1))
        (ULift.up 1)) := by
  rw [integralHomologyContractibleCoverEquiv_liftCycles_apply n A B hA hB hcover z hz zA zB
    hsplit a hac ha]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralHomologyContractibleCoverEquiv_apply_functional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralHomologyContractibleCoverEquiv_apply_functional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralHomologyContractibleCoverEquiv_apply_functional ``Submission.DifferentialGeometry.Topology.integralHomologyContractibleCoverEquiv_apply_functional

end Evaluation

end DifferentialGeometry.Topology
