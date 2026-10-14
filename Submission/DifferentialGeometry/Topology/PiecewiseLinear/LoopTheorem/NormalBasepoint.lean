/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaThree
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.EmbeddedDisk

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.CategoryTheory in
theorem fundamentalGroupChangeBasepoint_loopRepresentativeAlong
    {X : Type*} [TopologicalSpace X] {x y z : X}
    (β : Path x y) (q : Path y z) (γ : basedCircleLoop z) :
    fundamentalGroupChangeBasepoint β (loopRepresentativeAlong q γ) =
      loopRepresentativeAlong (β.trans q) γ := by
  let b : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y := ⟦β⟧
  let c : FundamentalGroupoid.mk y ⟶ FundamentalGroupoid.mk z := ⟦q⟧
  let g : FundamentalGroup X z := basedCircleFundamentalGroupClass γ
  change (b ≫ ((c ≫ g) ≫ Groupoid.inv c)) ≫ Groupoid.inv b =
    ((b ≫ c) ≫ g) ≫ Groupoid.inv (b ≫ c)
  simp [Category.assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fundamentalGroupChangeBasepoint_loopRepresentativeAlong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fundamentalGroupChangeBasepoint_loopRepresentativeAlong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fundamentalGroupChangeBasepoint_loopRepresentativeAlong ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fundamentalGroupChangeBasepoint_loopRepresentativeAlong

open _root_.Classical in
theorem normalSystemLoopConjugacyClass_comap_changeBasepoint_iff
    {X : Type*} [TopologicalSpace X] {x y : X}
    (β : Path x y) (γ : freeLoop X) (q : Path y (γ 0))
    (N : Subgroup (FundamentalGroup X x)) [N.Normal] :
    conjugacyClassMeets (normalSystemLoopConjugacyClass y γ q)
        (N.comap (fundamentalGroupChangeBasepoint β).toMonoidHom) ↔
      conjugacyClassMeets (normalSystemLoopConjugacyClass x γ (β.trans q)) N := by
  constructor
  · intro h
    have hmem := (conjugacyClassMeets_iff_carrier_subset _
      (N.comap (fundamentalGroupChangeBasepoint β).toMonoidHom)).mp h
        (ConjClasses.mem_carrier_iff_mk_eq.mpr rfl)
    change fundamentalGroupChangeBasepoint β (loopRepresentativeAlong q ⟨γ, rfl⟩) ∈ N at hmem
    rw [fundamentalGroupChangeBasepoint_loopRepresentativeAlong] at hmem
    exact ⟨_, ConjClasses.mem_carrier_iff_mk_eq.mpr rfl, hmem⟩
  · intro h
    have hmem := (conjugacyClassMeets_iff_carrier_subset _ N).mp h
      (ConjClasses.mem_carrier_iff_mk_eq.mpr rfl)
    refine ⟨loopRepresentativeAlong q ⟨γ, rfl⟩,
      ConjClasses.mem_carrier_iff_mk_eq.mpr rfl, ?_⟩
    change fundamentalGroupChangeBasepoint β (loopRepresentativeAlong q ⟨γ, rfl⟩) ∈ N
    rw [fundamentalGroupChangeBasepoint_loopRepresentativeAlong]
    exact hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.normalSystemLoopConjugacyClass_comap_changeBasepoint_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.normalSystemLoopConjugacyClass_comap_changeBasepoint_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.normalSystemLoopConjugacyClass_comap_changeBasepoint_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.normalSystemLoopConjugacyClass_comap_changeBasepoint_iff

namespace NormalSystem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open _root_.Classical in
noncomputable def atBoundaryLoop (S : NormalSystem E) : NormalSystem E := by
  let _ : S.normalSubgroup.Normal := S.normal
  refine { S with
    basepoint := S.boundaryLoop 0
    connector := Path.refl _
    normalSubgroup := S.normalSubgroup.comap
      (fundamentalGroupChangeBasepoint S.connector).toMonoidHom
    normal := inferInstance
    loopClass_avoids_normal := ?_ }
  intro h
  have h' := (normalSystemLoopConjugacyClass_comap_changeBasepoint_iff
    S.connector S.boundaryLoop (Path.refl _) S.normalSubgroup).mp h
  rw [S.loopConjugacyClass_eq_of_connector] at h'
  exact S.loopClass_avoids_normal h'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop

@[simp]
theorem atBoundaryLoop_basepoint (S : NormalSystem E) :
    S.atBoundaryLoop.basepoint = S.atBoundaryLoop.boundaryLoop 0 :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_basepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_basepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_basepoint ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_basepoint

@[simp]
theorem atBoundaryLoop_sourceComplex (S : NormalSystem E) :
    S.atBoundaryLoop.sourceComplex = S.sourceComplex :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_sourceComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_sourceComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_sourceComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_sourceComplex

@[simp]
theorem atBoundaryLoop_singularMap (S : NormalSystem E) :
    S.atBoundaryLoop.singularMap = S.singularMap :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_singularMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_singularMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_singularMap ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_singularMap

@[simp]
theorem atBoundaryLoop_complexity (S : NormalSystem E) :
    S.atBoundaryLoop.complexity = S.complexity :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_complexity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_complexity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_complexity ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_complexity

@[simp]
theorem atBoundaryLoop_boundaryComplex (S : NormalSystem E) :
    S.atBoundaryLoop.boundaryComplex = S.boundaryComplex :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_boundaryComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_boundaryComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_boundaryComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_boundaryComplex

@[simp]
theorem atBoundaryLoop_normalSubgroup (S : NormalSystem E) :
    S.atBoundaryLoop.normalSubgroup = S.normalSubgroup.comap
      (fundamentalGroupChangeBasepoint S.connector).toMonoidHom :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_normalSubgroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_normalSubgroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_normalSubgroup ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.atBoundaryLoop_normalSubgroup

open _root_.Classical in
noncomputable def NonsingularCell.ofAtBoundaryLoop {S : NormalSystem E}
    (D : NonsingularCell S.atBoundaryLoop) : NonsingularCell S := by
  let _ : S.normalSubgroup.Normal := S.normal
  refine { D with
    connector := S.connector.trans D.connector
    loopClass_avoids_normal := ?_ }
  intro h
  apply D.loopClass_avoids_normal
  exact (normalSystemLoopConjugacyClass_comap_changeBasepoint_iff
    S.connector D.boundaryLoop D.connector S.normalSubgroup).mpr h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.NonsingularCell.ofAtBoundaryLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.NonsingularCell.ofAtBoundaryLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.NonsingularCell.ofAtBoundaryLoop ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.NonsingularCell.ofAtBoundaryLoop

@[simp]
theorem NonsingularCell.ofAtBoundaryLoop_sourceComplex {S : NormalSystem E}
    (D : NonsingularCell S.atBoundaryLoop) : D.ofAtBoundaryLoop.sourceComplex = D.sourceComplex :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.NonsingularCell.ofAtBoundaryLoop_sourceComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.NonsingularCell.ofAtBoundaryLoop_sourceComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.NonsingularCell.ofAtBoundaryLoop_sourceComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.NonsingularCell.ofAtBoundaryLoop_sourceComplex

@[simp]
theorem NonsingularCell.ofAtBoundaryLoop_vertexMap {S : NormalSystem E}
    (D : NonsingularCell S.atBoundaryLoop) : D.ofAtBoundaryLoop.vertexMap = D.vertexMap :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.NonsingularCell.ofAtBoundaryLoop_vertexMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.NonsingularCell.ofAtBoundaryLoop_vertexMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.NonsingularCell.ofAtBoundaryLoop_vertexMap ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.NonsingularCell.ofAtBoundaryLoop_vertexMap

@[simp]
theorem NonsingularCell.ofAtBoundaryLoop_boundaryLoop {S : NormalSystem E}
    (D : NonsingularCell S.atBoundaryLoop) : D.ofAtBoundaryLoop.boundaryLoop = D.boundaryLoop :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.NonsingularCell.ofAtBoundaryLoop_boundaryLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.NonsingularCell.ofAtBoundaryLoop_boundaryLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.NonsingularCell.ofAtBoundaryLoop_boundaryLoop ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.NonsingularCell.ofAtBoundaryLoop_boundaryLoop

open _root_.Classical in
noncomputable def EmbeddedDisk.ofAtBoundaryLoop {S : NormalSystem E}
    (D : EmbeddedDisk S.atBoundaryLoop) : EmbeddedDisk S := by
  let _ : S.normalSubgroup.Normal := S.normal
  refine { D with
    connector := S.connector.trans D.connector
    loopClass_avoids_normal := ?_ }
  intro h
  apply D.loopClass_avoids_normal
  exact (normalSystemLoopConjugacyClass_comap_changeBasepoint_iff
    S.connector D.boundaryLoop D.connector S.normalSubgroup).mpr h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.EmbeddedDisk.ofAtBoundaryLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.EmbeddedDisk.ofAtBoundaryLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.EmbeddedDisk.ofAtBoundaryLoop ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.EmbeddedDisk.ofAtBoundaryLoop

@[simp]
theorem EmbeddedDisk.ofAtBoundaryLoop_domain {S : NormalSystem E}
    (D : EmbeddedDisk S.atBoundaryLoop) : D.ofAtBoundaryLoop.domain = D.domain :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.EmbeddedDisk.ofAtBoundaryLoop_domain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.EmbeddedDisk.ofAtBoundaryLoop_domain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.EmbeddedDisk.ofAtBoundaryLoop_domain ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.EmbeddedDisk.ofAtBoundaryLoop_domain

@[simp]
theorem EmbeddedDisk.ofAtBoundaryLoop_map {S : NormalSystem E}
    (D : EmbeddedDisk S.atBoundaryLoop) : D.ofAtBoundaryLoop.map = D.map :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.EmbeddedDisk.ofAtBoundaryLoop_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.EmbeddedDisk.ofAtBoundaryLoop_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.EmbeddedDisk.ofAtBoundaryLoop_map ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.EmbeddedDisk.ofAtBoundaryLoop_map

@[simp]
theorem EmbeddedDisk.ofAtBoundaryLoop_boundaryLoop {S : NormalSystem E}
    (D : EmbeddedDisk S.atBoundaryLoop) :
    D.ofAtBoundaryLoop.boundaryLoop = D.boundaryLoop :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.EmbeddedDisk.ofAtBoundaryLoop_boundaryLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.EmbeddedDisk.ofAtBoundaryLoop_boundaryLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.EmbeddedDisk.ofAtBoundaryLoop_boundaryLoop ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.EmbeddedDisk.ofAtBoundaryLoop_boundaryLoop

theorem nonempty_embeddedDisk_of_atBoundaryLoop {S : NormalSystem E}
    (h : Nonempty (EmbeddedDisk S.atBoundaryLoop)) : Nonempty (EmbeddedDisk S) :=
  h.map EmbeddedDisk.ofAtBoundaryLoop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.nonempty_embeddedDisk_of_atBoundaryLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.nonempty_embeddedDisk_of_atBoundaryLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.nonempty_embeddedDisk_of_atBoundaryLoop ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.nonempty_embeddedDisk_of_atBoundaryLoop

theorem nonempty_nonsingularCell_of_atBoundaryLoop {S : NormalSystem E}
    (h : Nonempty (NonsingularCell S.atBoundaryLoop)) : Nonempty (NonsingularCell S) :=
  h.map NonsingularCell.ofAtBoundaryLoop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.nonempty_nonsingularCell_of_atBoundaryLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.nonempty_nonsingularCell_of_atBoundaryLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.nonempty_nonsingularCell_of_atBoundaryLoop ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.nonempty_nonsingularCell_of_atBoundaryLoop

end NormalSystem

end DifferentialGeometry.Topology.PiecewiseLinear
