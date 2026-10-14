import Submission.DifferentialGeometry.Topology.SphereSeparation.SingularSubdivision
import Submission.DifferentialGeometry.Topology.SphereSeparation.PermutationDeletion
import Submission.DifferentialGeometry.Topology.SphereSeparation.BarycentricFacePairing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Simplicial
open scoped _root_.Simplicial

namespace DifferentialGeometry.Topology.SphereSeparation



noncomputable def appendOmittedVertexPermutation {n : ℕ}
    (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Fin (n + 2)) :=
  (extendLastPermutation τ).trans
    (Fin.cycleIcc p (Fin.last (n + 1)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.appendOmittedVertexPermutation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.appendOmittedVertexPermutation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.appendOmittedVertexPermutation ``Submission.DifferentialGeometry.Topology.SphereSeparation.appendOmittedVertexPermutation

@[simp]
theorem appendOmittedVertexPermutation_apply_castSucc {n : ℕ}
    (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) :
    appendOmittedVertexPermutation p τ i.castSucc = p.succAbove (τ i) := by
  simp only [appendOmittedVertexPermutation, Equiv.trans_apply,
    extendLastPermutation_apply_castSucc]
  have h := Fin.cycleIcc_comp_succAbove p (Fin.last (n + 1)) (Fin.le_last p)
  rw [← Fin.succAbove_last_apply (τ i)]
  exact congr_fun h (τ i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.appendOmittedVertexPermutation_apply_castSucc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.appendOmittedVertexPermutation_apply_castSucc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.appendOmittedVertexPermutation_apply_castSucc ``Submission.DifferentialGeometry.Topology.SphereSeparation.appendOmittedVertexPermutation_apply_castSucc

@[simp]
theorem appendOmittedVertexPermutation_apply_last {n : ℕ}
    (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    appendOmittedVertexPermutation p τ (Fin.last (n + 1)) = p := by
  simp only [appendOmittedVertexPermutation, Equiv.trans_apply,
    extendLastPermutation_apply_last]
  exact Fin.cycleIcc_of_last (Fin.le_last p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.appendOmittedVertexPermutation_apply_last then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.appendOmittedVertexPermutation_apply_last"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.appendOmittedVertexPermutation_apply_last ``Submission.DifferentialGeometry.Topology.SphereSeparation.appendOmittedVertexPermutation_apply_last

theorem appendOmittedVertexPermutation_sign {n : ℕ}
    (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm.sign (appendOmittedVertexPermutation p τ) =
      (-1) ^ ((n + 1) - (p : ℕ)) * Equiv.Perm.sign τ := by
  rw [appendOmittedVertexPermutation, Equiv.Perm.sign_trans,
    Fin.sign_cycleIcc_of_le (Fin.le_last p), sign_extendLastPermutation]
  simp only [Fin.val_last]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.appendOmittedVertexPermutation_sign then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.appendOmittedVertexPermutation_sign"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.appendOmittedVertexPermutation_sign ``Submission.DifferentialGeometry.Topology.SphereSeparation.appendOmittedVertexPermutation_sign

theorem appendOmittedVertexPermutation_boundary_sign {n : ℕ}
    (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    ((Equiv.Perm.sign (appendOmittedVertexPermutation p τ) : ℤ) *
        (-1 : ℤ) ^ (n + 1)) =
      (-1 : ℤ) ^ (p : ℕ) * (Equiv.Perm.sign τ : ℤ) := by
  rw [appendOmittedVertexPermutation_sign]
  simp only [Units.val_mul]
  have hp_le : (p : ℕ) ≤ n + 1 := Nat.le_of_lt_succ p.isLt
  have hparity :
      Even (((n + 1) - (p : ℕ)) + (n + 1)) ↔ Even (p : ℕ) := by
    constructor
    · rintro ⟨k, hk⟩
      use (n + 1) - k
      omega
    · rintro ⟨k, hk⟩
      use (n + 1) - k
      omega
  have hpow :
      (-1 : ℤ) ^ (((n + 1) - (p : ℕ)) + (n + 1)) =
        (-1 : ℤ) ^ (p : ℕ) :=
    neg_one_pow_congr hparity
  calc
    (-1 : ℤ) ^ ((n + 1) - (p : ℕ)) *
          (Equiv.Perm.sign τ : ℤ) * (-1 : ℤ) ^ (n + 1) =
        ((-1 : ℤ) ^ ((n + 1) - (p : ℕ)) *
          (-1 : ℤ) ^ (n + 1)) * (Equiv.Perm.sign τ : ℤ) := by ring
    _ = (-1 : ℤ) ^ (p : ℕ) * (Equiv.Perm.sign τ : ℤ) := by
      rw [← pow_add, hpow]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.appendOmittedVertexPermutation_boundary_sign then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.appendOmittedVertexPermutation_boundary_sign"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.appendOmittedVertexPermutation_boundary_sign ``Submission.DifferentialGeometry.Topology.SphereSeparation.appendOmittedVertexPermutation_boundary_sign

noncomputable def omittedVertexPermutationEquiv (n : ℕ) :
    (Fin (n + 2) × Equiv.Perm (Fin (n + 1))) ≃
      Equiv.Perm (Fin (n + 2)) where
  toFun q := appendOmittedVertexPermutation q.1 q.2
  invFun σ := (σ (Fin.last (n + 1)), eraseLastPermutation σ)
  left_inv q := by
    rcases q with ⟨p, τ⟩
    apply Prod.ext
    · exact appendOmittedVertexPermutation_apply_last p τ
    · apply Equiv.ext
      intro i
      have hi := succAbove_eraseLastPermutation
        (appendOmittedVertexPermutation p τ) i
      rw [appendOmittedVertexPermutation_apply_last,
        appendOmittedVertexPermutation_apply_castSucc] at hi
      exact p.succAbove_right_injective hi
  right_inv σ := by
    exact extendLast_eraseLast_trans_cycleIcc σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.omittedVertexPermutationEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.omittedVertexPermutationEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.omittedVertexPermutationEquiv ``Submission.DifferentialGeometry.Topology.SphereSeparation.omittedVertexPermutationEquiv

@[simp]
theorem omittedVertexPermutationEquiv_apply {n : ℕ}
    (q : Fin (n + 2) × Equiv.Perm (Fin (n + 1))) :
    omittedVertexPermutationEquiv n q =
      appendOmittedVertexPermutation q.1 q.2 :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.omittedVertexPermutationEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.omittedVertexPermutationEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.omittedVertexPermutationEquiv_apply ``Submission.DifferentialGeometry.Topology.SphereSeparation.omittedVertexPermutationEquiv_apply

@[simp]
theorem eraseLastPermutation_appendOmittedVertexPermutation {n : ℕ}
    (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    eraseLastPermutation (appendOmittedVertexPermutation p τ) = τ := by
  have h := (omittedVertexPermutationEquiv n).left_inv (p, τ)
  exact congr_arg Prod.snd h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.eraseLastPermutation_appendOmittedVertexPermutation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.eraseLastPermutation_appendOmittedVertexPermutation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.eraseLastPermutation_appendOmittedVertexPermutation ``Submission.DifferentialGeometry.Topology.SphereSeparation.eraseLastPermutation_appendOmittedVertexPermutation

theorem delta_barycentricPiece_appendOmittedVertex_finalFace
    (X : TopCat) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n + 1⦌)
    (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    (TopCat.toSSet.obj X).δ (Fin.last (n + 1))
        (barycentricPieceOfSingularSimplex X s
          (appendOmittedVertexPermutation p τ)) =
      barycentricPieceOfSingularSimplex X
        ((TopCat.toSSet.obj X).δ p s) τ := by
  apply (X.toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro x
  simp only [TopCat.toSSetObjEquiv_δ_apply,
    toSSetObjEquiv_barycentricPieceOfSingularSimplex,
    ContinuousMap.comp_apply]
  apply congr_arg (X.toSSetObjEquiv _ s)
  rw [barycentricPermutationSimplexMap_finalFace,
    appendOmittedVertexPermutation_apply_last,
    eraseLastPermutation_appendOmittedVertexPermutation]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.delta_barycentricPiece_appendOmittedVertex_finalFace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.delta_barycentricPiece_appendOmittedVertex_finalFace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.delta_barycentricPiece_appendOmittedVertex_finalFace ``Submission.DifferentialGeometry.Topology.SphereSeparation.delta_barycentricPiece_appendOmittedVertex_finalFace



theorem sum_sign_delta_barycentricPiece_castSucc_eq_zero
    (X : TopCat) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) (i : Fin (n + 1)) :
    ∑ σ : Equiv.Perm (Fin (n + 2)),
        (Equiv.Perm.sign σ : ℤ) •
          (TopCat.toSSet.obj X).ιChainComplex
            (R := ModuleCat.of ℤ ℤ)
            ((TopCat.toSSet.obj X).δ i.castSucc
              (barycentricPieceOfSingularSimplex X s σ)) = 0 := by
  classical
  exact Finset.sum_involution
    (fun σ _ => adjacentPositionSwap σ i)
    (fun σ _ => by
      rw [delta_barycentricPiece_adjacentPositionSwap,
        sign_adjacentPositionSwap]
      simp)
    (fun σ _ _ => adjacentPositionSwap_ne σ i)
    (fun _ _ => Finset.mem_univ _)
    (fun σ _ => adjacentPositionSwap_involutive σ i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.sum_sign_delta_barycentricPiece_castSucc_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.sum_sign_delta_barycentricPiece_castSucc_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.sum_sign_delta_barycentricPiece_castSucc_eq_zero ``Submission.DifferentialGeometry.Topology.SphereSeparation.sum_sign_delta_barycentricPiece_castSucc_eq_zero

theorem sum_signed_delta_barycentricPiece_castSucc_eq_zero
    (X : TopCat) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) (i : Fin (n + 1)) :
    ∑ σ : Equiv.Perm (Fin (n + 2)),
        (Equiv.Perm.sign σ : ℤ) •
          ((-1 : ℤ) ^ (i : ℕ) •
            (TopCat.toSSet.obj X).ιChainComplex
              (R := ModuleCat.of ℤ ℤ)
              ((TopCat.toSSet.obj X).δ i.castSucc
                (barycentricPieceOfSingularSimplex X s σ))) = 0 := by
  classical
  calc
    (∑ σ : Equiv.Perm (Fin (n + 2)),
        (Equiv.Perm.sign σ : ℤ) •
          ((-1 : ℤ) ^ (i : ℕ) •
            (TopCat.toSSet.obj X).ιChainComplex
              (R := ModuleCat.of ℤ ℤ)
              ((TopCat.toSSet.obj X).δ i.castSucc
                (barycentricPieceOfSingularSimplex X s σ)))) =
      (-1 : ℤ) ^ (i : ℕ) •
        (∑ σ : Equiv.Perm (Fin (n + 2)),
          (Equiv.Perm.sign σ : ℤ) •
            (TopCat.toSSet.obj X).ιChainComplex
              (R := ModuleCat.of ℤ ℤ)
              ((TopCat.toSSet.obj X).δ i.castSucc
                (barycentricPieceOfSingularSimplex X s σ))) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      simp only [smul_smul]
      congr 1
      ring
    _ = 0 := by
      rw [sum_sign_delta_barycentricPiece_castSucc_eq_zero]
      simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.sum_signed_delta_barycentricPiece_castSucc_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.sum_signed_delta_barycentricPiece_castSucc_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.sum_signed_delta_barycentricPiece_castSucc_eq_zero ``Submission.DifferentialGeometry.Topology.SphereSeparation.sum_signed_delta_barycentricPiece_castSucc_eq_zero

theorem sum_finalFaces_barycentricPiece
    (X : TopCat) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    (∑ σ : Equiv.Perm (Fin (n + 2)),
        (Equiv.Perm.sign σ : ℤ) •
          ((-1 : ℤ) ^ (n + 1) •
            (TopCat.toSSet.obj X).ιChainComplex
              (R := ModuleCat.of ℤ ℤ)
              ((TopCat.toSSet.obj X).δ (Fin.last (n + 1))
                (barycentricPieceOfSingularSimplex X s σ)))) =
      ∑ p : Fin (n + 2),
        (-1 : ℤ) ^ (p : ℕ) •
          (∑ τ : Equiv.Perm (Fin (n + 1)),
            (Equiv.Perm.sign τ : ℤ) •
              (TopCat.toSSet.obj X).ιChainComplex
                (R := ModuleCat.of ℤ ℤ)
                (barycentricPieceOfSingularSimplex X
                  ((TopCat.toSSet.obj X).δ p s) τ)) := by
  classical
  rw [← Equiv.sum_comp (omittedVertexPermutationEquiv n),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  simp only [omittedVertexPermutationEquiv_apply,
    delta_barycentricPiece_appendOmittedVertex_finalFace, smul_smul]
  rw [appendOmittedVertexPermutation_boundary_sign]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.sum_finalFaces_barycentricPiece then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.sum_finalFaces_barycentricPiece"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.sum_finalFaces_barycentricPiece ``Submission.DifferentialGeometry.Topology.SphereSeparation.sum_finalFaces_barycentricPiece

theorem barycentricSubdivisionBoundaryCompatible (X : TopCat) :
    BarycentricSubdivisionBoundaryCompatible X := by
  intro n
  change barycentricSubdivisionDegreeMap X (n + 1) ≫
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n =
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n ≫
      barycentricSubdivisionDegreeMap X n
  apply SSet.chainComplex_hom_ext
  intro s
  rw [← Category.assoc, ιChainComplex_barycentricSubdivisionDegreeMap,
    Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, SSet.ιChainComplex_d]
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp,
    ιChainComplex_barycentricSubdivisionDegreeMap]
  have hsplit (σ : Equiv.Perm (Fin (n + 2))) :
      (∑ j : Fin (n + 2),
          (-1 : ℤ) ^ (j : ℕ) •
            (TopCat.toSSet.obj X).ιChainComplex
              (R := ModuleCat.of ℤ ℤ)
              ((TopCat.toSSet.obj X).δ j
                (barycentricPieceOfSingularSimplex X s σ))) =
        (∑ i : Fin (n + 1),
          (-1 : ℤ) ^ (i : ℕ) •
            (TopCat.toSSet.obj X).ιChainComplex
              (R := ModuleCat.of ℤ ℤ)
              ((TopCat.toSSet.obj X).δ i.castSucc
                (barycentricPieceOfSingularSimplex X s σ))) +
          (-1 : ℤ) ^ (n + 1) •
            (TopCat.toSSet.obj X).ιChainComplex
              (R := ModuleCat.of ℤ ℤ)
              ((TopCat.toSSet.obj X).δ (Fin.last (n + 1))
                (barycentricPieceOfSingularSimplex X s σ)) := by
    simpa using Fin.sum_univ_castSucc (fun j : Fin (n + 2) =>
      (-1 : ℤ) ^ (j : ℕ) •
        (TopCat.toSSet.obj X).ιChainComplex
          (R := ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.obj X).δ j
            (barycentricPieceOfSingularSimplex X s σ)))
  simp_rw [hsplit, smul_add]
  rw [Finset.sum_add_distrib]
  have hinternal :
      (∑ σ : Equiv.Perm (Fin (n + 2)),
        (Equiv.Perm.sign σ : ℤ) •
          (∑ i : Fin (n + 1),
            (-1 : ℤ) ^ (i : ℕ) •
              (TopCat.toSSet.obj X).ιChainComplex
                (R := ModuleCat.of ℤ ℤ)
                ((TopCat.toSSet.obj X).δ i.castSucc
                  (barycentricPieceOfSingularSimplex X s σ)))) = 0 := by
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    exact sum_signed_delta_barycentricPiece_castSucc_eq_zero X s i
  rw [hinternal, zero_add, sum_finalFaces_barycentricPiece]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionBoundaryCompatible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionBoundaryCompatible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionBoundaryCompatible ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionBoundaryCompatible

end DifferentialGeometry.Topology.SphereSeparation
