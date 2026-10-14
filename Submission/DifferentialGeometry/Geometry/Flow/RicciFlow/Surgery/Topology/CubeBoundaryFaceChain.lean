import Submission.DifferentialGeometry.Topology.Homology.SquareBoundaryDegree
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HurewiczCube

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module
open scoped _root_.Topology _root_.unitInterval _root_.Simplicial

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

abbrev cube3 : Type := Fin 3 → unitInterval

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cube3 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cube3"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cube3 ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cube3

private def cubeFace (k : Fin 4) : C(stdSimplex ℝ (Fin 3), stdSimplex ℝ (Fin 4)) :=
  ⟨stdSimplex.map (SimplexCategory.δ k).toOrderHom,
    stdSimplex.continuous_map (SimplexCategory.δ k).toOrderHom⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeFace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeFace target :: scope.openDecls } }

private theorem cubeFace_self (k : Fin 4) (q : stdSimplex ℝ (Fin 3)) :
    cubeFace k q k = 0 := by
  change FunOnFinite.linearMap ℝ ℝ k.succAbove (q : Fin 3 → ℝ) k = 0
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro j hj
  exact False.elim (Fin.succAbove_ne k j (Finset.mem_filter.mp hj).2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeFace_self
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeFace_self target :: scope.openDecls } }

private theorem cubeFace_succAbove (k : Fin 4) (q : stdSimplex ℝ (Fin 3)) (j : Fin 3) :
    cubeFace k q (k.succAbove j) = q j := by
  change FunOnFinite.linearMap ℝ ℝ k.succAbove (q : Fin 3 → ℝ) (k.succAbove j) = q j
  simp [FunOnFinite.linearMap_apply_apply, Fin.succAbove_right_injective.eq_iff,
    Finset.sum_filter]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeFace_succAbove
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeFace_succAbove target :: scope.openDecls } }

private theorem staircaseCoordinate_face (e : Equiv.Perm (Fin 3)) (k : Fin 4)
    (q : stdSimplex ℝ (Fin 3)) (i : Fin 3) :
    staircaseCoordinate e (cubeFace k q) i =
      ∑ j : Fin 3, if (e.symm i).val < (k.succAbove j).val then q j else 0 := by
  unfold staircaseCoordinate
  rw [Fin.sum_univ_succAbove _ k]
  have hz : (if (e.symm i).val < k.val then (cubeFace k q).val k else 0) = 0 := by
    split_ifs
    · exact cubeFace_self k q
    · rfl
  have hsum :
      (∑ j : Fin 3, if (e.symm i).val < (k.succAbove j).val then
        (cubeFace k q).val (k.succAbove j) else 0) =
      ∑ j : Fin 3, if (e.symm i).val < (k.succAbove j).val then q.val j else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · exact cubeFace_succAbove k q j
    · rfl
  exact (congrArg₂ (fun a b : ℝ => a + b) hz hsum).trans (zero_add _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staircaseCoordinate_face
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staircaseCoordinate_face target :: scope.openDecls } }

private theorem staircase_face_zero (e : Equiv.Perm (Fin 3))
    (q : stdSimplex ℝ (Fin 3)) : staircaseSimplex e (cubeFace 0 q) (e 0) = 1 := by
  apply Subtype.ext
  change staircaseCoordinate e (cubeFace 0 q) (e 0) = 1
  rw [staircaseCoordinate_face]
  simp [Fin.succAbove]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staircase_face_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staircase_face_zero target :: scope.openDecls } }

private theorem staircase_face_three (e : Equiv.Perm (Fin 3))
    (q : stdSimplex ℝ (Fin 3)) : staircaseSimplex e (cubeFace 3 q) (e 2) = 0 := by
  apply Subtype.ext
  change staircaseCoordinate e (cubeFace 3 q) (e 2) = 0
  rw [staircaseCoordinate_face]
  simp [Fin.sum_univ_succ, Fin.succAbove]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staircase_face_three
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staircase_face_three target :: scope.openDecls } }

private theorem staircase_face_one_swap (e : Equiv.Perm (Fin 3)) :
    (staircaseSimplex e).comp (cubeFace 1) =
      (staircaseSimplex ((Equiv.swap 0 1).trans e)).comp (cubeFace 1) := by
  ext q i
  obtain ⟨k, rfl⟩ := e.surjective i
  change staircaseCoordinate e (cubeFace 1 q) (e k) =
    staircaseCoordinate ((Equiv.swap 0 1).trans e) (cubeFace 1 q) (e k)
  rw [staircaseCoordinate_face, staircaseCoordinate_face]
  fin_cases k <;> simp [Fin.sum_univ_succ, Equiv.swap_apply_def, Fin.succAbove]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staircase_face_one_swap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staircase_face_one_swap target :: scope.openDecls } }

private theorem staircase_face_two_swap (e : Equiv.Perm (Fin 3)) :
    (staircaseSimplex e).comp (cubeFace 2) =
      (staircaseSimplex ((Equiv.swap 1 2).trans e)).comp (cubeFace 2) := by
  ext q i
  obtain ⟨k, rfl⟩ := e.surjective i
  change staircaseCoordinate e (cubeFace 2 q) (e k) =
    staircaseCoordinate ((Equiv.swap 1 2).trans e) (cubeFace 2 q) (e k)
  rw [staircaseCoordinate_face, staircaseCoordinate_face]
  fin_cases k <;> simp [Fin.sum_univ_succ, Equiv.swap_apply_def, Fin.succAbove]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staircase_face_two_swap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staircase_face_two_swap target :: scope.openDecls } }

def cubeChain : integralCoefficients ⟶ (IntegralChains cube3).X 3 :=
  ∑ e : Equiv.Perm (Fin 3), ((e.sign : ℤˣ) : ℤ) • singularSimplexChain (staircaseSimplex e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeChain ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeChain

def cubeTopFaceChain (i : Fin 3) : integralCoefficients ⟶ (IntegralChains cube3).X 2 :=
  ∑ e : Equiv.Perm (Fin 3), if e 0 = i then
    ((e.sign : ℤˣ) : ℤ) • singularSimplexChain ((staircaseSimplex e).comp (cubeFace 0)) else 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeTopFaceChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeTopFaceChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeTopFaceChain ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeTopFaceChain

def cubeBottomFaceChain (i : Fin 3) : integralCoefficients ⟶ (IntegralChains cube3).X 2 :=
  ∑ e : Equiv.Perm (Fin 3), if e 2 = i then
    ((e.sign : ℤˣ) : ℤ) • singularSimplexChain ((staircaseSimplex e).comp (cubeFace 3)) else 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeBottomFaceChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeBottomFaceChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeBottomFaceChain ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeBottomFaceChain

theorem card_topFace_permutations (i : Fin 3) :
    Fintype.card {e : Equiv.Perm (Fin 3) // e 0 = i} = 2 := by
  fin_cases i <;> decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.card_topFace_permutations then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.card_topFace_permutations"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.card_topFace_permutations ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.card_topFace_permutations

theorem card_bottomFace_permutations (i : Fin 3) :
    Fintype.card {e : Equiv.Perm (Fin 3) // e 2 = i} = 2 := by
  fin_cases i <;> decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.card_bottomFace_permutations then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.card_bottomFace_permutations"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.card_bottomFace_permutations ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.card_bottomFace_permutations

private theorem nativeCubeTetrahedronBoundary (s : C(stdSimplex ℝ (Fin 4), cube3)) :
    singularSimplexChain s ≫ (IntegralChains cube3).d 3 2 =
      ∑ k : Fin 4, (-1 : ℤ) ^ k.val • singularSimplexChain (s.comp (cubeFace k)) :=
  (TopCat.toSSet.obj (TopCat.of cube3)).ιChainComplex_d
    (R := integralCoefficients)
    ((TopCat.toSSetObjEquiv (TopCat.of cube3) (.op ⦋3⦌)).symm s)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nativeCubeTetrahedronBoundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nativeCubeTetrahedronBoundary target :: scope.openDecls } }

private theorem cubeChain_tetrahedron_boundary (e : Equiv.Perm (Fin 3)) :
    singularSimplexChain (staircaseSimplex e) ≫ (IntegralChains cube3).d 3 2 =
      singularSimplexChain ((staircaseSimplex e).comp (cubeFace 0)) -
        singularSimplexChain ((staircaseSimplex e).comp (cubeFace 1)) +
        singularSimplexChain ((staircaseSimplex e).comp (cubeFace 2)) -
        singularSimplexChain ((staircaseSimplex e).comp (cubeFace 3)) := by
  rw [nativeCubeTetrahedronBoundary]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    pow_zero, one_smul, add_zero]
  norm_num
  abel

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeChain_tetrahedron_boundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeChain_tetrahedron_boundary target :: scope.openDecls } }

private theorem signed_swap_pairing {A : Type*} [AddCommGroup A] (F : Equiv.Perm (Fin 3) → A)
    (i j : Fin 3) (hij : i ≠ j) (hF : ∀ e, F ((Equiv.swap i j).trans e) = F e) :
    (∑ e : Equiv.Perm (Fin 3), ((e.sign : ℤˣ) : ℤ) • F e) = 0 := by
  classical
  apply Finset.sum_ninvolution (fun e => (Equiv.swap i j).trans e)
  · intro e
    rw [hF]
    simp [Equiv.Perm.sign_trans, Equiv.Perm.sign_swap hij]
  · intro e _ he
    have h := congrArg (fun p : Equiv.Perm (Fin 3) => p i) he
    have hji : j = i := e.injective (by simpa using h)
    exact hij hji.symm
  · intro e
    exact Finset.mem_univ _
  · intro e
    ext k
    exact congrArg (fun z => (e z).val) (Equiv.swap_apply_self i j k)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.signed_swap_pairing
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.signed_swap_pairing target :: scope.openDecls } }

theorem cubeChain_boundary :
    cubeChain ≫ (IntegralChains cube3).d 3 2 =
      ∑ i : Fin 3, (cubeTopFaceChain i - cubeBottomFaceChain i) := by
  classical
  have h₁ := signed_swap_pairing (fun e : Equiv.Perm (Fin 3) =>
    singularSimplexChain ((staircaseSimplex e).comp (cubeFace 1))) 0 1 (by decide)
    (fun e => by rw [← staircase_face_one_swap e])
  have h₂ := signed_swap_pairing (fun e : Equiv.Perm (Fin 3) =>
    singularSimplexChain ((staircaseSimplex e).comp (cubeFace 2))) 1 2 (by decide)
    (fun e => by rw [← staircase_face_two_swap e])
  have htop : (∑ e : Equiv.Perm (Fin 3), ((e.sign : ℤˣ) : ℤ) •
      singularSimplexChain ((staircaseSimplex e).comp (cubeFace 0))) =
      ∑ i : Fin 3, cubeTopFaceChain i := by
    simp only [cubeTopFaceChain]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  have hbot : (∑ e : Equiv.Perm (Fin 3), ((e.sign : ℤˣ) : ℤ) •
      singularSimplexChain ((staircaseSimplex e).comp (cubeFace 3))) =
      ∑ i : Fin 3, cubeBottomFaceChain i := by
    simp only [cubeBottomFaceChain]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  unfold cubeChain
  simp only [Preadditive.sum_comp, Linear.smul_comp, cubeChain_tetrahedron_boundary,
    smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [h₁, h₂, htop, hbot]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeChain_boundary ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cubeChain_boundary

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.Topology

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private theorem moduleCat_sum_apply {ι : Type*} {M N : ModuleCat ℤ} (s : Finset ι)
    (f : ι → (M ⟶ N)) (x : M) : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.moduleCat_sum_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.moduleCat_sum_apply target :: scope.openDecls } }

private theorem moduleCat_sum_sub_apply {ι : Type*} {M N : ModuleCat ℤ} (s : Finset ι)
    (f g : ι → (M ⟶ N)) (x : M) :
    (∑ i ∈ s, (f i - g i)) x = ∑ i ∈ s, (f i x - g i x) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.moduleCat_sum_sub_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.moduleCat_sum_sub_apply target :: scope.openDecls } }

abbrev cubeTetrahedralChain : (integralSingularChains (Fin 3 → unitInterval)).X 3 :=
  cubeChain (ULift.up (1 : ℤ) : DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.integralCoefficients)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeTetrahedralChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeTetrahedralChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeTetrahedralChain ``Submission.DifferentialGeometry.Topology.cubeTetrahedralChain

abbrev cubeTopFaceElement (i : Fin 3) : (integralSingularChains (Fin 3 → unitInterval)).X 2 :=
  cubeTopFaceChain i (ULift.up (1 : ℤ) : DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.integralCoefficients)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeTopFaceElement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeTopFaceElement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeTopFaceElement ``Submission.DifferentialGeometry.Topology.cubeTopFaceElement

abbrev cubeBottomFaceElement (i : Fin 3) : (integralSingularChains (Fin 3 → unitInterval)).X 2 :=
  cubeBottomFaceChain i (ULift.up (1 : ℤ) : DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.integralCoefficients)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeBottomFaceElement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeBottomFaceElement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeBottomFaceElement ``Submission.DifferentialGeometry.Topology.cubeBottomFaceElement

theorem cubeTopFaceMap_mem_boundary (e : Equiv.Perm (Fin 3))
    (q : stdSimplex ℝ (Fin 3)) :
    staircaseSimplex e (cubeFace 0 q) ∈ Cube.boundary (Fin 3) :=
  ⟨e 0, Or.inr (staircase_face_zero e q)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeTopFaceMap_mem_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeTopFaceMap_mem_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeTopFaceMap_mem_boundary ``Submission.DifferentialGeometry.Topology.cubeTopFaceMap_mem_boundary

theorem cubeBottomFaceMap_mem_boundary (e : Equiv.Perm (Fin 3))
    (q : stdSimplex ℝ (Fin 3)) :
    staircaseSimplex e (cubeFace 3 q) ∈ Cube.boundary (Fin 3) :=
  ⟨e 2, Or.inl (staircase_face_three e q)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeBottomFaceMap_mem_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeBottomFaceMap_mem_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeBottomFaceMap_mem_boundary ``Submission.DifferentialGeometry.Topology.cubeBottomFaceMap_mem_boundary

theorem cubeTetrahedralChain_boundary :
    (integralSingularChains (Fin 3 → unitInterval)).d 3 2 cubeTetrahedralChain =
      ∑ i : Fin 3, (cubeTopFaceElement i - cubeBottomFaceElement i) := by
  have h := congrArg (fun k => k (ULift.up (1 : ℤ) :
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.integralCoefficients)) cubeChain_boundary
  have h' : (integralSingularChains (Fin 3 → unitInterval)).d 3 2 cubeTetrahedralChain =
      (∑ i : Fin 3, (cubeTopFaceChain i - cubeBottomFaceChain i)) (ULift.up (1 : ℤ) :
        DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.integralCoefficients) := h
  erw [moduleCat_sum_sub_apply Finset.univ] at h'
  exact h'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeTetrahedralChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeTetrahedralChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeTetrahedralChain_boundary ``Submission.DifferentialGeometry.Topology.cubeTetrahedralChain_boundary

end DifferentialGeometry.Topology
