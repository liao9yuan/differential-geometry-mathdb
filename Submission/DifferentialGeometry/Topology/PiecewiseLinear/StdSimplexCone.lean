/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ConeExtension
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LinkEuclidean

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Std

variable (n : ℕ)

noncomputable def stdVertices : Finset (Fin (n + 2) → ℝ) :=
  Finset.univ.image fun i : Fin (n + 2) => (Pi.single i (1 : ℝ) : Fin (n + 2) → ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.stdVertices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.stdVertices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.stdVertices ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.stdVertices

noncomputable def stdCenter : Fin (n + 2) → ℝ := fun _ => ((n : ℝ) + 2)⁻¹

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.stdCenter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.stdCenter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.stdCenter ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.stdCenter

theorem stdVertex_injective :
    Function.Injective fun i : Fin (n + 2) => (Pi.single i (1 : ℝ) : Fin (n + 2) → ℝ) := by
  intro i j h
  by_contra hij
  have h1 : (Pi.single i (1 : ℝ) : Fin (n + 2) → ℝ) i = (Pi.single j (1 : ℝ) : Fin (n + 2) → ℝ) i :=
    congrFun h i
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hij] at h1
  exact one_ne_zero h1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.stdVertex_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.stdVertex_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.stdVertex_injective ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.stdVertex_injective

theorem coe_stdVertices :
    ((stdVertices n : Finset (Fin (n + 2) → ℝ)) : Set (Fin (n + 2) → ℝ)) =
      Set.range fun i : Fin (n + 2) => (Pi.single i (1 : ℝ) : Fin (n + 2) → ℝ) := by
  rw [stdVertices, Finset.coe_image, Finset.coe_univ, Set.image_univ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.coe_stdVertices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.coe_stdVertices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.coe_stdVertices ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.coe_stdVertices

theorem stdVertices_affineIndependent :
    AffineIndependent ℝ ((↑) : stdVertices n → (Fin (n + 2) → ℝ)) := by
  have hlin : LinearIndependent ℝ fun i : Fin (n + 2) => (Pi.single i (1 : ℝ) : Fin (n + 2) → ℝ) :=
      by
    have h := (Pi.basisFun ℝ (Fin (n + 2))).linearIndependent
    have heq : (⇑(Pi.basisFun ℝ (Fin (n + 2))) : Fin (n + 2) → Fin (n + 2) → ℝ) =
        fun i => Pi.single i 1 := funext fun i => by simp
    rwa [heq] at h
  have h := hlin.affineIndependent.range
  rwa [← coe_stdVertices] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.stdVertices_affineIndependent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.stdVertices_affineIndependent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.stdVertices_affineIndependent ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.stdVertices_affineIndependent

theorem card_stdVertices : (stdVertices n).card = n + 2 := by
  rw [stdVertices, Finset.card_image_of_injective _ (stdVertex_injective n), Finset.card_univ,
    Fintype.card_fin]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.card_stdVertices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.card_stdVertices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.card_stdVertices ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.card_stdVertices

theorem two_le_card_stdVertices : 2 ≤ (stdVertices n).card := by
  rw [card_stdVertices]
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.two_le_card_stdVertices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.two_le_card_stdVertices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.two_le_card_stdVertices ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.two_le_card_stdVertices

theorem convexHull_stdVertices :
    convexHull ℝ ((stdVertices n : Finset (Fin (n + 2) → ℝ)) : Set (Fin (n + 2) → ℝ)) =
      stdSimplex ℝ (Fin (n + 2)) := by
  have hfun : (fun i : Fin (n + 2) => (Pi.single i (1 : ℝ) : Fin (n + 2) → ℝ)) =
      fun i j => if i = j then (1 : ℝ) else 0 := by
    funext i j
    rw [Pi.single_apply]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  rw [coe_stdVertices, hfun, convexHull_basis_eq_stdSimplex]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.convexHull_stdVertices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.convexHull_stdVertices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.convexHull_stdVertices ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.convexHull_stdVertices

theorem stdCenter_mem_openSimplex : stdCenter n ∈ openSimplex (stdVertices n) := by
  have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  refine ⟨fun _ => ((n : ℝ) + 2)⁻¹, fun _ _ => inv_pos.mpr (by positivity), ?_, ?_⟩
  · rw [Finset.sum_const, card_stdVertices, nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat,
      mul_inv_cancel₀ hn2]
  · rw [stdVertices, Finset.sum_image fun i _ j _ h => stdVertex_injective n h]
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      _root_.MulZeroClass.mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.stdCenter_mem_openSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.stdCenter_mem_openSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.stdCenter_mem_openSimplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.stdCenter_mem_openSimplex

theorem isConeBase_std :
    IsConeBase (stdCenter n) (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)) :=
  isConeBase_simplexBoundary _ (two_le_card_stdVertices n) (stdCenter_mem_openSimplex n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isConeBase_std then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isConeBase_std"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isConeBase_std ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isConeBase_std

theorem coneComplex_std_space :
    (coneComplex (isConeBase_std n)).space = stdSimplex ℝ (Fin (n + 2)) := by
  rw [← convexHull_stdVertices]
  ext x
  rw [mem_coneComplex_space_iff]
  constructor
  · rintro (hxp | ⟨z, hz, s, hs, hs', rfl⟩)
    · rw [hxp]
      exact openSimplex_subset_convexHull _ (stdCenter_mem_openSimplex n)
    · rw [simplexBoundary_space _ _ (two_le_card_stdVertices n)] at hz
      obtain ⟨v, -, hzv⟩ := mem_iUnion₂.mp hz
      have hzT : z ∈ convexHull ℝ ((stdVertices n : Finset _) : Set _) :=
        convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset v _)) hzv
      rw [add_smul_sub_eq_combo]
      exact (convex_convexHull ℝ _) (openSimplex_subset_convexHull _ (stdCenter_mem_openSimplex n))
        hzT (by linarith) hs.le (by ring)
  · intro hx
    obtain ⟨v, hv, hxv⟩ := exists_mem_convexHull_insert_erase (stdVertices_affineIndependent n)
      (stdCenter_mem_openSimplex n) hx
    rcases exists_combo_of_mem_convexHull_insert
      (notMem_erase_of_mem_openSimplex (stdVertices_affineIndependent n)
        (stdCenter_mem_openSimplex n) hv) hxv with
      hxp | ⟨z, hz, s, hs, hs', rfl⟩
    · exact Or.inl hxp
    · refine Or.inr ⟨z, ?_, s, hs, hs', rfl⟩
      exact Geometry.SimplicialComplex.mem_space_iff.mpr
        ⟨_, erase_mem_simplexBoundary_faces _ (two_le_card_stdVertices n) hv, hz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.coneComplex_std_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.coneComplex_std_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.coneComplex_std_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.coneComplex_std_space

theorem isPLSphere_simplexBoundary_std :
    IsPLSphere n (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).space := by
  rw [simplexBoundary_space _ _ (two_le_card_stdVertices n)]
  exact isPLSphere_biUnion_erase _ (stdVertices_affineIndependent n) (card_stdVertices n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLSphere_simplexBoundary_std then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLSphere_simplexBoundary_std"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLSphere_simplexBoundary_std ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLSphere_simplexBoundary_std

end Std

theorem IsConeBase.isPLBall_of_isPLSphere [FiniteDimensional ℝ E] [DecidableEq E] {p : E}
    {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hL : IsConeBase p L) {n : ℕ}
    (hsph : IsPLSphere n L.space) : IsPLBall (n + 1) (coneComplex hL).space := by
  obtain ⟨f, hf⟩ := hsph
  obtain ⟨f₀, hf₀⟩ := isPLSphere_simplexBoundary_std n
  have hfin : Finite (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hhomeo := hf₀.symm.trans hf
  obtain ⟨g, hg, -, -, -⟩ := exists_isPLHomeomorphOn_coneComplex (isConeBase_std n) hL hhomeo
  rw [coneComplex_std_space] at hg
  exact ⟨g, hg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsConeBase.isPLBall_of_isPLSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsConeBase.isPLBall_of_isPLSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsConeBase.isPLBall_of_isPLSphere ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsConeBase.isPLBall_of_isPLSphere

theorem isPLBall_closedStar [FiniteDimensional ℝ E] [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {p : E} (hp : {p} ∈ K.faces) {n : ℕ}
    (hsph : IsPLSphere n (SimplicialComplex.geometricLink K {p}).space) :
    IsPLBall (n + 1) (closedStar K p) := by
  rw [closedStar_eq_coneComplex_space K hp]
  exact (isConeBase_geometricLink K).isPLBall_of_isPLSphere hsph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_closedStar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_closedStar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_closedStar ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_closedStar

theorem IsCombinatorialManifold.isPLBall_closedStar [FiniteDimensional ℝ E]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold (n + 1) K) {p : E} (hp : {p} ∈ K.faces) :
    IsPLBall (n + 1) (closedStar K p) := by
  classical
  exact PiecewiseLinear.isPLBall_closedStar K hp (by convert hK p hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.isPLBall_closedStar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.isPLBall_closedStar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.isPLBall_closedStar ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.isPLBall_closedStar

end DifferentialGeometry.Topology.PiecewiseLinear
