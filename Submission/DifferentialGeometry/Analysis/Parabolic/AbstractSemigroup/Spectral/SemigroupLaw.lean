import Submission.DifferentialGeometry.Analysis.Parabolic.AbstractSemigroup.Spectral.Semigroup

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.Topology
open scoped _root_.RealInnerProductSpace _root_.InnerProductSpace _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic

variable {ι : Type*} {X : Type*} [NormedAddCommGroup X]
  [InnerProductSpace ℝ X] [CompleteSpace X]

theorem abstractSpectralSemigroup_apply_zero (b : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) :
    abstractSpectralSemigroup b hlam 0 =
      ContinuousLinearMap.id ℝ X := by
  apply ContinuousLinearMap.ext
  intro v
  rw [abstractSpectralSemigroup_apply_of_nonneg b hlam (le_refl 0) v,
      ContinuousLinearMap.id_apply]
  have h_coeff_one : ∀ i : ι, heatCoeff lam 0 i = 1 := by
    intro i
    rw [heatCoeff_def, show -(lam i) * (0 : ℝ) = 0 from by ring, Real.exp_zero]
  have h_summand_eq :
      (fun i : ι => heatCoeff lam 0 i • ⟪b i, v⟫_ℝ • b i) =
      (fun i => ⟪b i, v⟫_ℝ • b i) := by
    funext i; rw [h_coeff_one i, one_smul]
  rw [h_summand_eq]
  have h_hsum : HasSum (fun i => b.repr v i • b i) v := b.hasSum_repr v
  have h_eq : (fun i => b.repr v i • b i) = (fun i => ⟪b i, v⟫_ℝ • b i) := by
    funext i; rw [b.repr_apply_apply]
  rw [h_eq] at h_hsum
  exact h_hsum.tsum_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.abstractSpectralSemigroup_apply_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.abstractSpectralSemigroup_apply_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.abstractSpectralSemigroup_apply_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.abstractSpectralSemigroup_apply_zero

theorem abstractSpectralSemigroup_apply_add (b : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    abstractSpectralSemigroup b hlam (t + s) =
      (abstractSpectralSemigroup b hlam t).comp
        (abstractSpectralSemigroup b hlam s) := by
  apply ContinuousLinearMap.ext
  intro v
  have hts_nn : 0 ≤ t + s := add_nonneg ht hs
  rw [abstractSpectralSemigroup_apply_of_nonneg b hlam hts_nn,
      ContinuousLinearMap.comp_apply,
      abstractSpectralSemigroup_apply_of_nonneg b hlam hs v]
  have h_summable_s := summable_heatTerm b hlam hs v
  have h_pull :
      abstractSpectralSemigroup b hlam t
          (∑' i : ι, heatCoeff lam s i • ⟪b i, v⟫_ℝ • b i) =
      ∑' i : ι, abstractSpectralSemigroup b hlam t
          (heatCoeff lam s i • ⟪b i, v⟫_ℝ • b i) := by
    have h_hsum := h_summable_s.hasSum
    exact (h_hsum.mapL (abstractSpectralSemigroup b hlam t)).tsum_eq.symm
  rw [h_pull]
  apply tsum_congr
  intro i
  rw [(abstractSpectralSemigroup b hlam t).map_smul,
      (abstractSpectralSemigroup b hlam t).map_smul]
  have h_basis_apply :
      abstractSpectralSemigroup b hlam t (b i) = heatCoeff lam t i • b i :=
    abstractSpectralSemigroup_apply_basis b hlam ht i
  rw [h_basis_apply]
  have h_exp_add : heatCoeff lam (t + s) i = heatCoeff lam t i * heatCoeff lam s i := by
    rw [heatCoeff_def, heatCoeff_def, heatCoeff_def,
        show -(lam i) * (t + s) = -(lam i) * t + -(lam i) * s from by ring,
        Real.exp_add]
  rw [show heatCoeff lam (t + s) i • ⟪b i, v⟫_ℝ • b i =
      (heatCoeff lam (t + s) i * ⟪b i, v⟫_ℝ) • b i from by rw [_root_.SemigroupAction.mul_smul]]
  rw [show heatCoeff lam s i • ⟪b i, v⟫_ℝ • heatCoeff lam t i • b i =
      (heatCoeff lam s i * (⟪b i, v⟫_ℝ * heatCoeff lam t i)) • b i from by
    rw [_root_.SemigroupAction.mul_smul, _root_.SemigroupAction.mul_smul]]
  congr 1
  rw [h_exp_add]; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.abstractSpectralSemigroup_apply_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.abstractSpectralSemigroup_apply_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.abstractSpectralSemigroup_apply_add ``Submission.DifferentialGeometry.Analysis.Parabolic.abstractSpectralSemigroup_apply_add

end Parabolic
end Analysis
end DifferentialGeometry

end
