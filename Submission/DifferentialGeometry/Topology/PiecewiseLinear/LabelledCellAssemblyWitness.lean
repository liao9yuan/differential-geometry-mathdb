/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LabelledCellAssembly

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem eq_of_mem_stdSimplex_fin_one {x y : Fin 1 → ℝ} (hx : x ∈ stdSimplex ℝ (Fin 1))
    (hy : y ∈ stdSimplex ℝ (Fin 1)) : x = y := by
  have h1 : ∑ i, x i = 1 := hx.2
  have h2 : ∑ i, y i = 1 := hy.2
  rw [Fin.sum_univ_one] at h1 h2
  funext i
  induction i using Fin.cases with
  | zero => rw [h1, h2]
  | succ j => exact j.elim0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eq_of_mem_stdSimplex_fin_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eq_of_mem_stdSimplex_fin_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eq_of_mem_stdSimplex_fin_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eq_of_mem_stdSimplex_fin_one

theorem stdSimplexBoundary_zero : stdSimplexBoundary 0 = (∅ : Set (Fin 1 → ℝ)) := by
  rw [_root_.Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx, i, hi⟩
  have h1 : ∑ j, x j = 1 := hx.2
  rw [Fin.sum_univ_one] at h1
  induction i using Fin.cases with
  | zero =>
      rw [hi] at h1
      exact zero_ne_one h1
  | succ j => exact j.elim0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.stdSimplexBoundary_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.stdSimplexBoundary_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.stdSimplexBoundary_zero ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.stdSimplexBoundary_zero

theorem isPLHomeomorphOn_const_stdSimplex_fin_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (a : E) :
    IsPLHomeomorphOn (fun _ : Fin 1 → ℝ => a) (stdSimplex ℝ (Fin 1)) {a} := by
  have hmem : (Pi.single (0 : Fin 1) 1 : Fin 1 → ℝ) ∈ stdSimplex ℝ (Fin 1) :=
    single_mem_stdSimplex ℝ 0
  have hbij : _root_.Set.BijOn (fun _ : Fin 1 → ℝ => a) (stdSimplex ℝ (Fin 1)) {a} :=
    ⟨fun _ _ => rfl, fun x hx y hy _ => eq_of_mem_stdSimplex_fin_one hx hy,
      fun y hy => ⟨_, hmem, hy.symm⟩⟩
  refine ⟨hbij, ?_, ?_⟩
  · exact (isPiecewiseAffineOn_of_affine_of_isHPolytope (AffineMap.const ℝ (Fin 1 → ℝ) a)
      (isHPolytope_stdSimplex (Fin 1))).congr fun _ _ => rfl
  · refine (isPiecewiseAffineOn_of_affine_of_isHPolytope
      (AffineMap.const ℝ E (Pi.single (0 : Fin 1) 1 : Fin 1 → ℝ))
      (isHPolytope_singleton a)).congr ?_
    intro y hy
    exact eq_of_mem_stdSimplex_fin_one (hbij.surjOn.mapsTo_invFunOn hy) hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_const_stdSimplex_fin_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_const_stdSimplex_fin_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_const_stdSimplex_fin_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_const_stdSimplex_fin_one

theorem isPLHomeomorphInto_id_singleton (a : EuclideanSpace ℝ (Fin 3)) :
    IsPLHomeomorphInto 3 (id : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) {a} := by
  have hpl : IsPLOn 3 3 (id : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) {a} :=
    isPLOn_iff_isPiecewiseAffineOn.mpr
      (isHPolytope_singleton a).isPolyhedron.isPLHomeomorphOn_id.isPiecewiseAffineOn
  refine ⟨hpl, _root_.Set.injOn_id _, fun y hy => ⟨id, ?_, fun x _ => rfl⟩⟩
  rw [_root_.Set.image_id] at hy ⊢
  exact hpl y hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphInto_id_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphInto_id_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphInto_id_singleton ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphInto_id_singleton

theorem exists_isPLHomeomorphInto_singleton_of_labelledCells (a b : EuclideanSpace ℝ (Fin 3)) :
    ∃ f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphInto 3 f {a} ∧ f '' {a} = {b} := by
  obtain ⟨f, hf, hfim⟩ := exists_isPLHomeomorphInto_of_labelledCells
    (Λ := Unit) (M₁ := EuclideanSpace ℝ (Fin 3)) (M₂ := EuclideanSpace ℝ (Fin 3))
    (fun _ => 0) (fun _ => _root_.Set.univ) (fun _ => {a}) (fun _ => {b}) (fun _ _ => a) (fun _ _ => b)
    (fun _ => id) (fun _ => id) (fun _ => {a}) (fun _ => {b}) (fun _ => by omega)
    (fun _ => isPLHomeomorphOn_const_stdSimplex_fin_one a)
    (fun _ => isPLHomeomorphOn_const_stdSimplex_fin_one b)
    (fun _ => isPLHomeomorphInto_id_singleton a)
    (fun _ => isPLHomeomorphInto_id_singleton b)
    (fun _ => (_root_.Set.image_id {a}).symm) (fun _ => (_root_.Set.image_id {b}).symm)
    (fun l m _ => Or.inl (Subsingleton.elim m l))
    (fun l => by
      have hset : (_root_.Set.univ : Set Unit) \ {l} = ∅ := by
        rw [_root_.Set.eq_empty_iff_forall_notMem]
        rintro m ⟨-, hm⟩
        exact hm (mem_singleton_iff.mpr (Subsingleton.elim m l))
      rw [stdSimplexBoundary_zero, _root_.Set.image_empty, _root_.Set.image_empty, hset]
      simp)
    (fun l => by
      have hset : (_root_.Set.univ : Set Unit) \ {l} = ∅ := by
        rw [_root_.Set.eq_empty_iff_forall_notMem]
        rintro m ⟨-, hm⟩
        exact hm (mem_singleton_iff.mpr (Subsingleton.elim m l))
      rw [stdSimplexBoundary_zero, _root_.Set.image_empty, _root_.Set.image_empty, hset]
      simp)
    (fun _ _ => by simp) (fun _ _ => by simp)
    (fun x _ => ⟨univ, Filter.univ_mem, Set.toFinite _⟩)
    (fun y _ => ⟨univ, Filter.univ_mem, Set.toFinite _⟩)
  refine ⟨f, ?_, hfim ()⟩
  rwa [_root_.Set.iUnion_const] at hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphInto_singleton_of_labelledCells then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphInto_singleton_of_labelledCells"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphInto_singleton_of_labelledCells ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphInto_singleton_of_labelledCells

end DifferentialGeometry.Topology.PiecewiseLinear
