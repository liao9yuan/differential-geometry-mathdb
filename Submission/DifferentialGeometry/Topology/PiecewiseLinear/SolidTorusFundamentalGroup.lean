/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SolidTorus
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallHomotopy
import Submission.DifferentialGeometry.Topology.FundamentalGroup.Circle
import Submission.DifferentialGeometry.Topology.FundamentalGroup.Nullhomotopy
import Mathlib.Geometry.Manifold.Instances.Sphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "S1" => Metric.sphere (0 : E2) 1

noncomputable def IsTopologicalSolidTorus.fundamentalGroupEquivInt
    {Y : Type*} [TopologicalSpace Y] {S : Set Y} (hS : IsTopologicalSolidTorus S) (x : S) :
    FundamentalGroup S x ≃* Multiplicative ℤ := by
  classical
  let φ : S ≃ₜ (Metric.closedBall (0 : E2) 1 × S1) := Classical.choice hS
  let D := Metric.closedBall (0 : E2) 1
  let p : D := ⟨0, by simp [D]⟩
  let a : Circle ≃ₜ S1 :=
    Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype fun z => by
      change z ∈ Metric.sphere (0 : ℂ) 1 ↔
        Complex.orthonormalBasisOneI.repr z ∈ Metric.sphere 0 1
      rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm,
        Complex.orthonormalBasisOneI.repr.norm_map]
  let ψ : S ≃ₜ (D × Circle) := φ.trans (Homeomorph.prodCongr (Homeomorph.refl D) a.symm)
  let _ : ContractibleSpace D := (convex_closedBall (0 : E2) 1).contractibleSpace
    ⟨0, by simp⟩
  exact (fundamentalGroupMulEquivOfHomotopyEquiv ψ.toHomotopyEquiv x (ψ x) rfl).trans
    ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (ψ x) (p, 1)).trans
      (fundamentalGroupProdCircleEquivIntOfSimplyConnected p))

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.fundamentalGroupEquivInt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.fundamentalGroupEquivInt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.fundamentalGroupEquivInt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.fundamentalGroupEquivInt

theorem IsTopologicalSolidTorus.nontrivial_fundamentalGroup
    {Y : Type*} [TopologicalSpace Y] {S : Set Y} (hS : IsTopologicalSolidTorus S) (x : S) :
    Nontrivial (FundamentalGroup S x) :=
  (hS.fundamentalGroupEquivInt x).toEquiv.nontrivial

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.nontrivial_fundamentalGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.nontrivial_fundamentalGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.nontrivial_fundamentalGroup ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.nontrivial_fundamentalGroup
theorem IsPLBall.not_surjective_fundamentalGroup_map_inclusion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} {D A S : Set E} (hD : IsPLBall n D) (hS : IsTopologicalSolidTorus S)
    (hAD : A ⊆ D) (hDS : D ⊆ S) (x : A) :
    ¬ Function.Surjective (FundamentalGroup.map
      (⟨Set.inclusion (hAD.trans hDS), continuous_inclusion _⟩ : C(A, S)) x) := by
  intro hsurj
  let i : C(A, S) := ⟨Set.inclusion (hAD.trans hDS), continuous_inclusion _⟩
  let _ : Nontrivial (FundamentalGroup S (i x)) := hS.nontrivial_fundamentalGroup (i x)
  obtain ⟨g, hg⟩ := exists_ne (1 : FundamentalGroup S (i x))
  obtain ⟨b, hb⟩ := hsurj g
  have hnull : FundamentalGroup.map i x b = 1 :=
    fundamentalGroup_map_eq_one_of_nullhomotopic i (hD.nullhomotopic_inclusion hAD hDS) x b
  exact hg (hb.symm.trans hnull)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.not_surjective_fundamentalGroup_map_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.not_surjective_fundamentalGroup_map_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.not_surjective_fundamentalGroup_map_inclusion ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.not_surjective_fundamentalGroup_map_inclusion

end DifferentialGeometry.Topology.PiecewiseLinear
