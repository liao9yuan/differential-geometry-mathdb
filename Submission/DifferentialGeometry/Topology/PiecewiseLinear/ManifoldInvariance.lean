/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialZero
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsomorphicSubdivision
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubdivision

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open _root_.Classical in
theorem isCombinatorialManifoldWithBoundary_of_isSubdivision [FiniteDimensional ℝ E] {n : ℕ}
    {K K' : Geometry.SimplicialComplex ℝ E} [Finite K'.faces]
    (hK' : IsSubdivision K' K) (h : IsCombinatorialManifoldWithBoundary n K') :
    IsCombinatorialManifoldWithBoundary n K := by
  classical
  cases n with
  | zero =>
    have hfin : K.space.Finite := by
      rw [← hK'.space_eq]
      exact space_finite_of_isCombinatorialManifold_zero K' h
    intro v _
    rw [Set.eq_empty_iff_forall_notMem]
    intro s hs
    obtain ⟨hne, hvs, hins⟩ := (SimplicialComplex.mem_geometricLink_singleton K v s).mp hs
    obtain ⟨w, hw⟩ := hne
    have hvw : v ≠ w := fun heq => hvs (heq ▸ hw)
    have hpair : ({v, w} : Set E) ⊆ (↑(_root_.Insert.insert v s) : Set E) := by
      intro y hy
      rcases hy with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem hw
    exact infinite_convexHull_pair hvw
      (hfin.subset ((convexHull_mono hpair).trans (K.convexHull_subset_space hins)))
  | succ n =>
    intro v hv
    obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_geometricLink_of_isSubdivision hK' hv
    rcases h v (hK'.singleton_mem hv) with hs | hb
    · exact Or.inl (hs.of_isPLHomeomorphOn hf)
    · exact Or.inr (hb.of_isPLHomeomorphOn hf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialManifoldWithBoundary_of_isSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialManifoldWithBoundary_of_isSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialManifoldWithBoundary_of_isSubdivision ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialManifoldWithBoundary_of_isSubdivision

open _root_.Classical in
theorem isCombinatorialManifold_of_isSubdivision [FiniteDimensional ℝ E] {n : ℕ}
    {K K' : Geometry.SimplicialComplex ℝ E} [Finite K'.faces]
    (hK' : IsSubdivision K' K) (h : IsCombinatorialManifold n K') :
    IsCombinatorialManifold n K := by
  classical
  cases n with
  | zero =>
    exact isCombinatorialManifoldWithBoundary_of_isSubdivision hK'
      h.isCombinatorialManifoldWithBoundary
  | succ n =>
    intro v hv
    obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_geometricLink_of_isSubdivision hK' hv
    exact (h v (hK'.singleton_mem hv)).of_isPLHomeomorphOn hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialManifold_of_isSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialManifold_of_isSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialManifold_of_isSubdivision ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialManifold_of_isSubdivision

open _root_.Classical in
theorem IsCombinatorialManifoldWithBoundary.of_isPLHomeomorphOn {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {n : ℕ} {K : Geometry.SimplicialComplex ℝ E}
    {L : Geometry.SimplicialComplex ℝ F} [Finite K.faces] [Finite L.faces]
    (h : IsCombinatorialManifoldWithBoundary n K) {f : E → F}
    (hf : IsPLHomeomorphOn f K.space L.space) : IsCombinatorialManifoldWithBoundary n L := by
  classical
  obtain ⟨K₁, L₁, φ', hK₁, hK₁fin, hL₁, hL₁fin, hiso, _⟩ :=
    exists_isGlueIso_of_isPLHomeomorphOn K L hf
  have : Finite K₁.faces := hK₁fin.to_subtype
  have : Finite L₁.faces := hL₁fin.to_subtype
  exact isCombinatorialManifoldWithBoundary_of_isSubdivision hL₁
    (hiso.isCombinatorialManifoldWithBoundary (h.of_isSubdivision hK₁))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.of_isPLHomeomorphOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.of_isPLHomeomorphOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.of_isPLHomeomorphOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.of_isPLHomeomorphOn

open _root_.Classical in
theorem IsCombinatorialManifold.of_isPLHomeomorphOn {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {n : ℕ} {K : Geometry.SimplicialComplex ℝ E}
    {L : Geometry.SimplicialComplex ℝ F} [Finite K.faces] [Finite L.faces]
    (h : IsCombinatorialManifold n K) {f : E → F}
    (hf : IsPLHomeomorphOn f K.space L.space) : IsCombinatorialManifold n L := by
  classical
  obtain ⟨K₁, L₁, φ', hK₁, hK₁fin, hL₁, hL₁fin, hiso, _⟩ :=
    exists_isGlueIso_of_isPLHomeomorphOn K L hf
  have : Finite K₁.faces := hK₁fin.to_subtype
  have : Finite L₁.faces := hL₁fin.to_subtype
  exact isCombinatorialManifold_of_isSubdivision hL₁
    (hiso.isCombinatorialManifold (h.of_isSubdivision hK₁))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.of_isPLHomeomorphOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.of_isPLHomeomorphOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.of_isPLHomeomorphOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.of_isPLHomeomorphOn

open _root_.Classical in
theorem IsPLBall.isCombinatorialManifoldWithBoundary [FiniteDimensional ℝ E] {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] (hK : IsPLBall (n + 1) K.space) :
    IsCombinatorialManifoldWithBoundary (n + 1) K := by
  intro v hv
  exact isPLSphere_or_isPLBall_geometricLink_of_isPLBall K hK hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isCombinatorialManifoldWithBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isCombinatorialManifoldWithBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isCombinatorialManifoldWithBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isCombinatorialManifoldWithBoundary

open _root_.Classical in
theorem IsPLSphere.isCombinatorialManifold [FiniteDimensional ℝ E] {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] (hK : IsPLSphere (n + 1) K.space) :
    IsCombinatorialManifold (n + 1) K := by
  intro v hv
  exact isPLSphere_geometricLink_of_isPLSphere K hK hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isCombinatorialManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isCombinatorialManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isCombinatorialManifold ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isCombinatorialManifold

end DifferentialGeometry.Topology.PiecewiseLinear
