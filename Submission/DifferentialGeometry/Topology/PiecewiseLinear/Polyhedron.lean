/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Groupoid
import Submission.DifferentialGeometry.Topology.SimplicialComplex.GeometricLink
import Mathlib.Analysis.Convex.StdSimplex

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology
open scoped _root_.Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def IsPLHomeomorphOn (f : E → F) (P : Set E) (Q : Set F) : Prop :=
  _root_.Set.BijOn f P Q ∧ IsPiecewiseAffineOn f P ∧ IsPiecewiseAffineOn (Function.invFunOn f P) Q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn

theorem isHPolytope_stdSimplex (ι : Type) [Fintype ι] : IsHPolytope (stdSimplex ℝ ι) := by
  refine ⟨isCompact_stdSimplex ℝ ι, ι ⊕ Bool, inferInstance,
    Sum.elim (fun i => -(LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ))
      (fun b => if b then ∑ i, (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ)
        else -∑ i, (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ)),
    Sum.elim (fun _ => 0) (fun b => if b then 1 else -1), ?_⟩
  ext x
  simp only [stdSimplex, _root_.Set.mem_ofPred_eq, Sum.forall, Sum.elim_inl, Sum.elim_inr,
    LinearMap.neg_apply, LinearMap.proj_apply, Bool.forall_bool, Bool.false_eq_true, if_false,
    if_true, LinearMap.sum_apply, neg_le_neg_iff]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨fun i => by linarith [h0 i], h1.ge, h1.le⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨fun i => by linarith [h0 i], le_antisymm h2 h1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isHPolytope_stdSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isHPolytope_stdSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isHPolytope_stdSimplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isHPolytope_stdSimplex

theorem isPLHomeomorphOn_id_of_isHPolytope {P : Set E} (hP : IsHPolytope P) :
    IsPLHomeomorphOn (id : E → E) P P :=
  ⟨bijOn_id P, isPiecewiseAffineOn_of_affine_of_isHPolytope (AffineMap.id ℝ E) hP,
    (isPiecewiseAffineOn_of_affine_of_isHPolytope (AffineMap.id ℝ E) hP).congr
      fun _ hy => (_root_.Set.bijOn_id P).invOn_invFunOn.1 hy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_id_of_isHPolytope then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_id_of_isHPolytope"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_id_of_isHPolytope ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_id_of_isHPolytope

def stdSimplexBoundary (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {x | x ∈ stdSimplex ℝ (Fin (n + 1)) ∧ ∃ i, x i = 0}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.stdSimplexBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.stdSimplexBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.stdSimplexBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.stdSimplexBoundary

def IsPLBall (n : ℕ) (P : Set E) : Prop :=
  ∃ f : (Fin (n + 1) → ℝ) → E, IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 1))) P

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall

def IsPLSphere (n : ℕ) (P : Set E) : Prop :=
  ∃ f : (Fin (n + 2) → ℝ) → E, IsPLHomeomorphOn f (stdSimplexBoundary (n + 1)) P

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere

theorem IsPLBall.nonempty {n : ℕ} {P : Set E} (hP : IsPLBall n P) : P.Nonempty := by
  obtain ⟨f, hf⟩ := hP
  exact ⟨f (Pi.single (0 : Fin (n + 1)) 1), hf.1.mapsTo (single_mem_stdSimplex ℝ _)⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.nonempty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.nonempty

theorem IsPLSphere.nonempty {n : ℕ} {P : Set E} (hP : IsPLSphere n P) : P.Nonempty := by
  obtain ⟨f, hf⟩ := hP
  refine ⟨f (Pi.single (0 : Fin (n + 2)) 1), hf.1.mapsTo ⟨single_mem_stdSimplex ℝ _, 1, ?_⟩⟩
  simp

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.nonempty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.nonempty

theorem isPLBall_stdSimplex (n : ℕ) : IsPLBall n (stdSimplex ℝ (Fin (n + 1))) :=
  ⟨id, isPLHomeomorphOn_id_of_isHPolytope (isHPolytope_stdSimplex _)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_stdSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_stdSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_stdSimplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_stdSimplex

open _root_.Classical in
def IsCombinatorialManifold : ℕ → Geometry.SimplicialComplex ℝ E → Prop
  | 0, K => ∀ v, {v} ∈ K.faces → (SimplicialComplex.geometricLink K {v}).faces = ∅
  | n + 1, K => ∀ v, {v} ∈ K.faces → IsPLSphere n (SimplicialComplex.geometricLink K {v}).space

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold

universe u

open _root_.Classical in
def CombinatorialManifoldPLStructure (n : ℕ) : Prop :=
  ∀ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))), Finite K.faces →
    IsCombinatorialManifold n K →
    ∃ C : ChartedSpace (EuclideanSpace ℝ (Fin n)) K.space,
      letI := C
      HasGroupoid K.space (plGroupoid n) ∧
      ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) K.space,
        IsPiecewiseAffineOn (fun p => if h : p ∈ K.space then e ⟨p, h⟩ else 0)
          (Subtype.val '' e.source) ∧
        IsPiecewiseAffineOn (fun y => ((e.symm y : K.space) : EuclideanSpace ℝ (Fin N))) e.target

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialManifoldPLStructure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialManifoldPLStructure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialManifoldPLStructure ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialManifoldPLStructure

structure PLTriangulation (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] where
  ambientDim : ℕ
  complex : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin ambientDim))
  finite_faces : Finite complex.faces
  map : EuclideanSpace ℝ (Fin ambientDim) → X
  bijOn : _root_.Set.BijOn map complex.space _root_.Set.univ
  continuousOn : ContinuousOn map complex.space
  isPiecewiseAffineOn_chart : ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) X,
    IsPiecewiseAffineOn (e ∘ map) (complex.space ∩ map ⁻¹' e.source)
  isPiecewiseAffineOn_chart_symm : ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) X,
    IsPiecewiseAffineOn (Function.invFunOn map complex.space ∘ e.symm) e.target

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLTriangulation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLTriangulation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLTriangulation ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLTriangulation

def PLManifoldTriangulation (n : ℕ) : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [CompactSpace X]
    [Nonempty X] (C : ChartedSpace (EuclideanSpace ℝ (Fin n)) X),
    (letI := C; HasGroupoid X (plGroupoid n)) →
    letI := C
    ∃ T : PLTriangulation n X, IsCombinatorialManifold n T.complex

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLManifoldTriangulation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLManifoldTriangulation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLManifoldTriangulation ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLManifoldTriangulation

end DifferentialGeometry.Topology.PiecewiseLinear
