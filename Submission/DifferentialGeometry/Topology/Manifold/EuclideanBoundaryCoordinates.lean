/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.InnerProductSpace.PiL2

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Manifold _root_.Set _root_.Topology
open scoped _root_.Manifold _root_.ContDiff
noncomputable section

namespace DifferentialGeometry.Topology

def normalFirstEquiv (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  ((LinearEquiv.prodCongr (WithLp.linearEquiv 2 ℝ (Fin n → ℝ))
      (LinearEquiv.refl ℝ ℝ)).trans
    ((LinearEquiv.prodComm ℝ (Fin n → ℝ) ℝ).trans
      ((Fin.consLinearEquiv ℝ (fun _ : Fin (n + 1) ↦ ℝ)).trans
        (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).symm))).toContinuousLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.normalFirstEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.normalFirstEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.normalFirstEquiv ``Submission.DifferentialGeometry.Topology.normalFirstEquiv

@[simp]
theorem normalFirstEquiv_zero (n : ℕ) (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    normalFirstEquiv n p 0 = p.2 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.normalFirstEquiv_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.normalFirstEquiv_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.normalFirstEquiv_zero ``Submission.DifferentialGeometry.Topology.normalFirstEquiv_zero

def signedNormalFirstEquiv (n : ℕ) (positive : Bool) :
    (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  if positive then normalFirstEquiv n else
    (normalFirstEquiv n).trans (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.signedNormalFirstEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.signedNormalFirstEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.signedNormalFirstEquiv ``Submission.DifferentialGeometry.Topology.signedNormalFirstEquiv

@[simp]
theorem signedNormalFirstEquiv_zero (n : ℕ) (positive : Bool)
    (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    signedNormalFirstEquiv n positive p 0 = if positive then p.2 else -p.2 := by
  cases positive <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.signedNormalFirstEquiv_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.signedNormalFirstEquiv_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.signedNormalFirstEquiv_zero ``Submission.DifferentialGeometry.Topology.signedNormalFirstEquiv_zero

def signedNormalFirstDiffeomorph (n : ℕ) (positive : Bool) :
    Diffeomorph ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))).prod
      (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n + 1))))
      (EuclideanSpace ℝ (Fin n) × ℝ) (EuclideanSpace ℝ (Fin (n + 1))) ∞ where
  toEquiv := (signedNormalFirstEquiv n positive).toEquiv
  contMDiff_toFun := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact (signedNormalFirstEquiv n positive).contDiff.contMDiff
  contMDiff_invFun := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact (signedNormalFirstEquiv n positive).symm.contDiff.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.signedNormalFirstDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.signedNormalFirstDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.signedNormalFirstDiffeomorph ``Submission.DifferentialGeometry.Topology.signedNormalFirstDiffeomorph

def translateDiffeomorph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (v : E) :
    Diffeomorph (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) E E ∞ where
  toEquiv := Equiv.addRight v
  contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.translateDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.translateDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.translateDiffeomorph ``Submission.DifferentialGeometry.Topology.translateDiffeomorph

theorem exists_positiveChart_of_mem_open {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    {V : Set M} (hV : IsOpen V) {x : M} (hx : x ∈ V) :
    ∃ φ : _root_.PartialDiffeomorph
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M
        (EuclideanSpace ℝ (Fin n)) ∞,
      x ∈ φ.source ∧ φ.source ⊆ V ∧ ∀ y ∈ φ.source, 0 < φ y 0 := by
  let c := PartialDiffeomorph.extendedChart
    (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ ↦ 1) - c x
  let d := c.trans (translateDiffeomorph v).toPartialDiffeomorph
  have hxsource : x ∈ d.source := ⟨mem_extChartAt_source x, _root_.Set.mem_univ _⟩
  have hxpos : 0 < d x 0 := by
    change 0 < (c x + v) 0
    simp [v]
  let W := (d.source ∩ d ⁻¹' {z | 0 < z 0}) ∩ V
  have hW : IsOpen W :=
    (d.toOpenPartialHomeomorph.isOpen_inter_preimage
      (isOpen_lt continuous_const (by fun_prop))).inter hV
  refine ⟨PartialDiffeomorph.restrict d W hW,
    ⟨hxsource, ⟨hxsource, hxpos⟩, hx⟩, ?_, ?_⟩
  · exact fun _ hy ↦ hy.2.2
  · exact fun _ hy ↦ hy.2.1.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_positiveChart_of_mem_open then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_positiveChart_of_mem_open"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_positiveChart_of_mem_open ``Submission.DifferentialGeometry.Topology.exists_positiveChart_of_mem_open

end DifferentialGeometry.Topology
