/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.FundamentalGroup.BasepointChange
import Submission.DifferentialGeometry.Topology.LoopSpace.FreeHomotopyInjection
import Submission.DifferentialGeometry.Topology.LoopSpace.FreeHomotopySurjection
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRetraction
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Manifold
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLMap
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.RelativeSimplexTriangulation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

structure SingularTwoCell (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] where
  domain : Set (EuclideanSpace ℝ (Fin 2))
  isPLBall_domain : IsPLBall 2 domain
  toFun : EuclideanSpace ℝ (Fin 2) → M
  isPLOn : IsPLOn 2 3 toFun domain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell

instance _root_.Submission.DifferentialGeometry.Topology.PiecewiseLinear.instCoeFunSingularTwoCellForallEuclideanSpaceRealFinOfNatNat {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    CoeFun (SingularTwoCell M) (fun _ => EuclideanSpace ℝ (Fin 2) → M) :=
  ⟨SingularTwoCell.toFun⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.instCoeFunSingularTwoCellForallEuclideanSpaceRealFinOfNatNat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.instCoeFunSingularTwoCellForallEuclideanSpaceRealFinOfNatNat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.instCoeFunSingularTwoCellForallEuclideanSpaceRealFinOfNatNat ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.instCoeFunSingularTwoCellForallEuclideanSpaceRealFinOfNatNat

namespace SingularTwoCell

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

def restrict (D : SingularTwoCell M) {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hP : IsPLBall 2 P) (hPD : P ⊆ D.domain) : SingularTwoCell M where
  domain := P
  isPLBall_domain := hP
  toFun := D
  isPLOn := D.isPLOn.mono_of_isPolyhedron hP.isPolyhedron hPD

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.restrict ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.restrict

@[simp]
theorem restrict_domain (D : SingularTwoCell M) {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hP : IsPLBall 2 P) (hPD : P ⊆ D.domain) :
    (D.restrict hP hPD).domain = P :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.restrict_domain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.restrict_domain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.restrict_domain ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.restrict_domain

@[simp]
theorem restrict_apply (D : SingularTwoCell M) {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hP : IsPLBall 2 P) (hPD : P ⊆ D.domain) (x : EuclideanSpace ℝ (Fin 2)) :
    D.restrict hP hPD x = D x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.restrict_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.restrict_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.restrict_apply ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.restrict_apply

theorem continuousOn (D : SingularTwoCell M) : ContinuousOn D D.domain :=
  fun x hx => (D.isPLOn x hx).continuousWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.continuousOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.continuousOn

theorem frontier_subset_domain (D : SingularTwoCell M) : frontier D.domain ⊆ D.domain := by
  have hclosed : IsClosed D.domain := D.isPLBall_domain.isPolyhedron.isCompact.isClosed
  simpa only [hclosed.closure_eq] using
    (frontier_subset_closure : frontier D.domain ⊆ closure D.domain)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.frontier_subset_domain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.frontier_subset_domain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.frontier_subset_domain ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.frontier_subset_domain

def boundary (D : SingularTwoCell M) : C(frontier D.domain, M) where
  toFun x := D x
  continuous_toFun :=
    continuousOn_iff_continuous_domRestrict.mp
      (D.continuousOn.mono D.frontier_subset_domain)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.boundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.boundary

@[simp]
theorem boundary_apply (D : SingularTwoCell M) (x : frontier D.domain) :
    D.boundary x = D x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.boundary_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.boundary_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.boundary_apply ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.boundary_apply

theorem isPLSphere_frontier (D : SingularTwoCell M) : IsPLSphere 1 (frontier D.domain) :=
  D.isPLBall_domain.isPLSphere_frontier

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.isPLSphere_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.isPLSphere_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.isPLSphere_frontier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.isPLSphere_frontier

def IsNonsingular (D : SingularTwoCell M) : Prop :=
  _root_.Set.InjOn D D.domain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.IsNonsingular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.IsNonsingular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.IsNonsingular ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.IsNonsingular

theorem isNonsingular_iff (D : SingularTwoCell M) :
    D.IsNonsingular ↔ _root_.Set.InjOn D D.domain :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.isNonsingular_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.isNonsingular_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.isNonsingular_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.isNonsingular_iff

theorem range_boundary_restrict (D : SingularTwoCell M)
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsPLBall 2 P) (hPD : P ⊆ D.domain) :
    Set.range (D.restrict hP hPD).boundary = D '' frontier P := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.range_boundary_restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.range_boundary_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.range_boundary_restrict ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.range_boundary_restrict

theorem restrict_isNonsingular_iff (D : SingularTwoCell M)
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsPLBall 2 P) (hPD : P ⊆ D.domain) :
    (D.restrict hP hPD).IsNonsingular ↔ _root_.Set.InjOn D P :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.restrict_isNonsingular_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.restrict_isNonsingular_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.restrict_isNonsingular_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.restrict_isNonsingular_iff

end SingularTwoCell

end DifferentialGeometry.Topology.PiecewiseLinear

namespace DifferentialGeometry.Topology

universe u

namespace FreeLoop

variable {X : Type u} [TopologicalSpace X]

open _root_.Classical in
noncomputable def basedRepresentative [PathConnectedSpace X] (γ : freeLoop X) (x : X) :
    basedCircleLoop x :=
  Classical.choose (exists_basedCircle_free_homotopic x γ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FreeLoop.basedRepresentative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FreeLoop.basedRepresentative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FreeLoop.basedRepresentative ``Submission.DifferentialGeometry.Topology.FreeLoop.basedRepresentative

theorem basedRepresentative_homotopic [PathConnectedSpace X] (γ : freeLoop X) (x : X) :
    (FreeLoop.basedRepresentative γ x).val.Homotopic γ :=
  Classical.choose_spec (exists_basedCircle_free_homotopic x γ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FreeLoop.basedRepresentative_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FreeLoop.basedRepresentative_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FreeLoop.basedRepresentative_homotopic ``Submission.DifferentialGeometry.Topology.FreeLoop.basedRepresentative_homotopic

open _root_.Classical in
noncomputable def fundamentalGroupRepresentative [PathConnectedSpace X]
    (γ : freeLoop X) (x : X) : FundamentalGroup X x :=
  Path.Homotopic.Quotient.mk (circleToPath (FreeLoop.basedRepresentative γ x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FreeLoop.fundamentalGroupRepresentative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FreeLoop.fundamentalGroupRepresentative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FreeLoop.fundamentalGroupRepresentative ``Submission.DifferentialGeometry.Topology.FreeLoop.fundamentalGroupRepresentative

open _root_.Classical in
noncomputable def conjugacyClass [PathConnectedSpace X] (γ : freeLoop X) (x : X) :
    ConjClasses (FundamentalGroup X x) :=
  ConjClasses.mk (FreeLoop.fundamentalGroupRepresentative γ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FreeLoop.conjugacyClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FreeLoop.conjugacyClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FreeLoop.conjugacyClass ``Submission.DifferentialGeometry.Topology.FreeLoop.conjugacyClass

end FreeLoop

def basedCircleFundamentalGroupClass {X : Type u} [TopologicalSpace X] {x : X}
    (γ : basedCircleLoop x) : FundamentalGroup X x :=
  Path.Homotopic.Quotient.mk (circleToPath γ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedCircleFundamentalGroupClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedCircleFundamentalGroupClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedCircleFundamentalGroupClass ``Submission.DifferentialGeometry.Topology.basedCircleFundamentalGroupClass

theorem isConj_circleToPath_of_freeHomotopic {X : Type u} [TopologicalSpace X] {x : X}
    (γ δ : basedCircleLoop x) (h : γ.val.Homotopic δ.val) :
    IsConj (basedCircleFundamentalGroupClass γ) (basedCircleFundamentalGroupClass δ) := by
  obtain ⟨H⟩ := h
  let r : FundamentalGroup X x :=
    Path.Homotopic.Quotient.mk (basedCircleHomotopyTrack γ δ H)
  have heq := Path.Homotopic.Quotient.eq.mpr
    (basedCircleHomotopyTrack_commutes γ δ H)
  change r * basedCircleFundamentalGroupClass γ =
    basedCircleFundamentalGroupClass δ * r at heq
  rw [isConj_iff]
  refine ⟨r, ?_⟩
  calc
    r * basedCircleFundamentalGroupClass γ * r⁻¹ =
        (basedCircleFundamentalGroupClass δ * r) * r⁻¹ :=
      congrArg (fun z => z * r⁻¹) heq
    _ = basedCircleFundamentalGroupClass δ := by
      rw [mul_assoc, mul_inv_cancel, mul_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isConj_circleToPath_of_freeHomotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isConj_circleToPath_of_freeHomotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isConj_circleToPath_of_freeHomotopic ``Submission.DifferentialGeometry.Topology.isConj_circleToPath_of_freeHomotopic

theorem FreeLoop.conjugacyClass_eq_mk_circleToPath
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (γ : freeLoop X) (x : X) (δ : basedCircleLoop x)
    (hδ : δ.val.Homotopic γ) :
    FreeLoop.conjugacyClass γ x =
      ConjClasses.mk (basedCircleFundamentalGroupClass δ) := by
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  exact isConj_circleToPath_of_freeHomotopic (FreeLoop.basedRepresentative γ x) δ
    ((FreeLoop.basedRepresentative_homotopic γ x).trans hδ.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FreeLoop.conjugacyClass_eq_mk_circleToPath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FreeLoop.conjugacyClass_eq_mk_circleToPath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FreeLoop.conjugacyClass_eq_mk_circleToPath ``Submission.DifferentialGeometry.Topology.FreeLoop.conjugacyClass_eq_mk_circleToPath

theorem FreeLoop.conjugacyClass_eq_of_homotopic
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    {γ δ : freeLoop X} (h : γ.Homotopic δ) (x : X) :
    FreeLoop.conjugacyClass γ x = FreeLoop.conjugacyClass δ x := by
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  exact isConj_circleToPath_of_freeHomotopic (FreeLoop.basedRepresentative γ x)
    (FreeLoop.basedRepresentative δ x) ((FreeLoop.basedRepresentative_homotopic γ x).trans
      (h.trans (FreeLoop.basedRepresentative_homotopic δ x).symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FreeLoop.conjugacyClass_eq_of_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FreeLoop.conjugacyClass_eq_of_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FreeLoop.conjugacyClass_eq_of_homotopic ``Submission.DifferentialGeometry.Topology.FreeLoop.conjugacyClass_eq_of_homotopic

open _root_.Classical in
noncomputable def loopRepresentativeAlong
    {X : Type u} [TopologicalSpace X] {x y : X}
    (q : Path x y) (γ : basedCircleLoop y) : FundamentalGroup X x :=
  DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
    (basedCircleFundamentalGroupClass γ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopRepresentativeAlong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopRepresentativeAlong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopRepresentativeAlong ``Submission.DifferentialGeometry.Topology.loopRepresentativeAlong

open _root_.Classical in
theorem loopRepresentativeAlong_pathToCircle
    {X : Type u} [TopologicalSpace X] {x y : X}
    (q : Path x y) (p : Path y y) :
    loopRepresentativeAlong q
        (⟨pathToCircle p, pathToCircle_zero p⟩ : basedCircleLoop y) =
      DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint q
        (Path.Homotopic.Quotient.mk p) := by
  unfold loopRepresentativeAlong basedCircleFundamentalGroupClass
  rw [show circleToPath
      (⟨pathToCircle p, pathToCircle_zero p⟩ : basedCircleLoop y) = p from
    (basedPathCircleHomeomorph y).left_inv p]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopRepresentativeAlong_pathToCircle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopRepresentativeAlong_pathToCircle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopRepresentativeAlong_pathToCircle ``Submission.DifferentialGeometry.Topology.loopRepresentativeAlong_pathToCircle

theorem loopRepresentativeAlong_connector
    {X : Type u} [TopologicalSpace X] {x y : X}
    (q q' : Path x y) (γ : basedCircleLoop y) :
    loopRepresentativeAlong q' γ =
      MulAut.conj (DifferentialGeometry.Topology.connectorLoop q q')⁻¹
        (loopRepresentativeAlong q γ) :=
  DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint_connector q q'
    (basedCircleFundamentalGroupClass γ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopRepresentativeAlong_connector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopRepresentativeAlong_connector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopRepresentativeAlong_connector ``Submission.DifferentialGeometry.Topology.loopRepresentativeAlong_connector

theorem loopRepresentativeAlong_isConj
    {X : Type u} [TopologicalSpace X] {x y : X}
    (q q' : Path x y) (γ : basedCircleLoop y) :
    IsConj (loopRepresentativeAlong q γ) (loopRepresentativeAlong q' γ) := by
  rw [isConj_iff]
  refine ⟨(connectorLoop q q')⁻¹, ?_⟩
  rw [loopRepresentativeAlong_connector q q' γ, MulAut.conj_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopRepresentativeAlong_isConj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopRepresentativeAlong_isConj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopRepresentativeAlong_isConj ``Submission.DifferentialGeometry.Topology.loopRepresentativeAlong_isConj

theorem FreeLoop.conjugacyClass_eq_mk_loopRepresentativeAlong
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    {x y : X} (q : Path x y) (γ : basedCircleLoop y) :
    FreeLoop.conjugacyClass γ.val x = ConjClasses.mk (loopRepresentativeAlong q γ) := by
  let p : Path x x := q.trans ((circleToPath γ).trans q.symm)
  let δ : basedCircleLoop x := basedPathCircleHomeomorph x p
  have hδ : δ.val.Homotopic γ.val := by
    change (pathToCircle p).Homotopic γ.val
    refine (pathToCircle_conjugate_homotopic q (circleToPath γ)).trans ?_
    rw [show pathToCircle (circleToPath γ) = γ.val from
      congrArg Subtype.val ((basedPathCircleHomeomorph y).apply_symm_apply γ)]
  calc
    FreeLoop.conjugacyClass γ.val x =
        ConjClasses.mk (basedCircleFundamentalGroupClass δ) :=
      FreeLoop.conjugacyClass_eq_mk_circleToPath γ.val x δ hδ
    _ = ConjClasses.mk (loopRepresentativeAlong q γ) := by
      congr 1
      rw [basedCircleFundamentalGroupClass,
        show circleToPath δ = p from (basedPathCircleHomeomorph x).left_inv p]
      unfold p loopRepresentativeAlong
      rw [fundamentalGroupChangeBasepoint_apply]
      simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
      exact (Path.Homotopic.Quotient.trans_assoc _ _ _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FreeLoop.conjugacyClass_eq_mk_loopRepresentativeAlong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FreeLoop.conjugacyClass_eq_mk_loopRepresentativeAlong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FreeLoop.conjugacyClass_eq_mk_loopRepresentativeAlong ``Submission.DifferentialGeometry.Topology.FreeLoop.conjugacyClass_eq_mk_loopRepresentativeAlong

def conjugacyClassMeets {G : Type*} [Group G]
    (C : ConjClasses G) (N : Subgroup G) : Prop :=
  ∃ g, g ∈ C.carrier ∧ g ∈ N

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.conjugacyClassMeets then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.conjugacyClassMeets"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.conjugacyClassMeets ``Submission.DifferentialGeometry.Topology.conjugacyClassMeets

theorem conjugacyClassMeets_iff_carrier_subset
    {G : Type*} [Group G] (C : ConjClasses G) (N : Subgroup G) [N.Normal] :
    conjugacyClassMeets C N ↔ C.carrier ⊆ (N : Set G) := by
  constructor
  · rintro ⟨g, hg, hgN⟩ h hh
    have hconj : IsConj g h := ConjClasses.mk_eq_mk_iff_isConj.mp
      ((ConjClasses.mem_carrier_iff_mk_eq.mp hg).trans
        (ConjClasses.mem_carrier_iff_mk_eq.mp hh).symm)
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    rw [← hc]
    exact ‹N.Normal›.conj_mem g hgN c
  · intro h
    obtain ⟨g, rfl⟩ := C.exists_rep
    refine ⟨g, ?_, h ?_⟩ <;> exact ConjClasses.mem_carrier_iff_mk_eq.mpr rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.conjugacyClassMeets_iff_carrier_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.conjugacyClassMeets_iff_carrier_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.conjugacyClassMeets_iff_carrier_subset ``Submission.DifferentialGeometry.Topology.conjugacyClassMeets_iff_carrier_subset

theorem conjugacyClass_subset_or_disjoint_normal
    {G : Type*} [Group G] (C : ConjClasses G) (N : Subgroup G) [N.Normal] :
    C.carrier ⊆ (N : Set G) ∨ Disjoint C.carrier (N : Set G) := by
  classical
  by_cases h : conjugacyClassMeets C N
  · exact Or.inl ((conjugacyClassMeets_iff_carrier_subset C N).mp h)
  · right
    exact Set.disjoint_left.mpr fun g hg hgN => h ⟨g, hg, hgN⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.conjugacyClass_subset_or_disjoint_normal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.conjugacyClass_subset_or_disjoint_normal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.conjugacyClass_subset_or_disjoint_normal ``Submission.DifferentialGeometry.Topology.conjugacyClass_subset_or_disjoint_normal

def loopClassMeets {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (γ : freeLoop X) (x : X) (N : Subgroup (FundamentalGroup X x)) : Prop :=
  conjugacyClassMeets (FreeLoop.conjugacyClass γ x) N

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopClassMeets then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopClassMeets"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopClassMeets ``Submission.DifferentialGeometry.Topology.loopClassMeets

theorem loopClassMeets_iff_carrier_subset
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (γ : freeLoop X) (x : X) (N : Subgroup (FundamentalGroup X x)) [N.Normal] :
    loopClassMeets γ x N ↔
      (FreeLoop.conjugacyClass γ x).carrier ⊆ (N : Set _) := by
  exact conjugacyClassMeets_iff_carrier_subset (FreeLoop.conjugacyClass γ x) N

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopClassMeets_iff_carrier_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopClassMeets_iff_carrier_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopClassMeets_iff_carrier_subset ``Submission.DifferentialGeometry.Topology.loopClassMeets_iff_carrier_subset

theorem loopConjugacyClass_subset_or_disjoint_normal
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (γ : freeLoop X) (x : X) (N : Subgroup (FundamentalGroup X x)) [N.Normal] :
    (FreeLoop.conjugacyClass γ x).carrier ⊆ (N : Set _) ∨
      Disjoint (FreeLoop.conjugacyClass γ x).carrier (N : Set _) := by
  exact conjugacyClass_subset_or_disjoint_normal (FreeLoop.conjugacyClass γ x) N

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopConjugacyClass_subset_or_disjoint_normal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopConjugacyClass_subset_or_disjoint_normal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopConjugacyClass_subset_or_disjoint_normal ``Submission.DifferentialGeometry.Topology.loopConjugacyClass_subset_or_disjoint_normal

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open _root_.Classical in
noncomputable def vertexCollisionPairs (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (f : E → F) : Finset (Finset E) :=
  ((simplicialComplexVertices K).powersetCard 2).filter
    (fun s => ¬ _root_.Set.InjOn f (s : Set E))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.vertexCollisionPairs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.vertexCollisionPairs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.vertexCollisionPairs ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.vertexCollisionPairs

@[simp]
theorem mem_vertexCollisionPairs (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (f : E → F) (s : Finset E) :
    s ∈ vertexCollisionPairs K f ↔
      (s : Set E) ⊆ K.vertices ∧ s.card = 2 ∧ ¬ _root_.Set.InjOn f (s : Set E) := by
  classical
  rw [vertexCollisionPairs, Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨hsub, hcard⟩, hinj⟩
    exact ⟨fun v hv => mem_simplicialComplexVertices K |>.mp (hsub hv), hcard, hinj⟩
  · rintro ⟨hsub, hcard, hinj⟩
    exact ⟨⟨fun v hv => mem_simplicialComplexVertices K |>.mpr (hsub hv), hcard⟩, hinj⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_vertexCollisionPairs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_vertexCollisionPairs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_vertexCollisionPairs ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_vertexCollisionPairs

open _root_.Classical in
noncomputable def simplicialComplexity (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (f : E → F) : ℕ :=
  (vertexCollisionPairs K f).card

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexity ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexity

open _root_.Classical in
theorem vertexCollisionPairs_image_subset_of_vertex_injection
    {E' F' X : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (K : Geometry.SimplicialComplex ℝ E') [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F') [Finite L.faces]
    (f : E' → X) (g : F' → X) (r : F' → E')
    (hr : _root_.Set.MapsTo r L.vertices K.vertices) (hinj : _root_.Set.InjOn r L.vertices)
    (hfactor : ∀ v ∈ L.vertices, f (r v) = g v) :
    (vertexCollisionPairs L g).image (fun s => s.image r) ⊆
      vertexCollisionPairs K f := by
  intro s hs
  rw [Finset.mem_image] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  rw [mem_vertexCollisionPairs] at ht ⊢
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact hr (ht.1 hv)
  · calc
      (t.image r).card = t.card := Finset.card_image_of_injOn (hinj.mono ht.1)
      _ = 2 := ht.2.1
  · intro hfinj
    apply ht.2.2
    intro v hv w hw hgw
    apply hinj (ht.1 hv) (ht.1 hw)
    apply hfinj
      (by exact Finset.mem_image.mpr ⟨v, hv, rfl⟩)
      (by exact Finset.mem_image.mpr ⟨w, hw, rfl⟩)
    calc
      f (r v) = g v := hfactor v (ht.1 hv)
      _ = g w := hgw
      _ = f (r w) := (hfactor w (ht.1 hw)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.vertexCollisionPairs_image_subset_of_vertex_injection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.vertexCollisionPairs_image_subset_of_vertex_injection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.vertexCollisionPairs_image_subset_of_vertex_injection ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.vertexCollisionPairs_image_subset_of_vertex_injection

open _root_.Classical in
theorem simplicialComplexity_lt_of_vertex_injection
    {E' F' X : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (K : Geometry.SimplicialComplex ℝ E') [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F') [Finite L.faces]
    (f : E' → X) (g : F' → X) (r : F' → E')
    (hr : _root_.Set.MapsTo r L.vertices K.vertices) (hinj : _root_.Set.InjOn r L.vertices)
    (hfactor : ∀ v ∈ L.vertices, f (r v) = g v)
    (hmissing : ∃ s ∈ vertexCollisionPairs K f,
      s ∉ (vertexCollisionPairs L g).image (fun t => t.image r)) :
    simplicialComplexity L g < simplicialComplexity K f := by
  have hsubset := vertexCollisionPairs_image_subset_of_vertex_injection
    K L f g r hr hinj hfactor
  have himageInj : _root_.Set.InjOn (fun s : Finset F' => s.image r)
      (vertexCollisionPairs L g : Set (Finset F')) := by
    intro a ha b hb hab
    have haVertices := (mem_vertexCollisionPairs L g a).mp ha |>.1
    have hbVertices := (mem_vertexCollisionPairs L g b).mp hb |>.1
    have habInj : _root_.Set.InjOn r ((a ∪ b : Finset F') : Set F') :=
      hinj.mono fun x hx => by
        rcases Finset.mem_union.mp hx with hxa | hxb
        · exact haVertices hxa
        · exact hbVertices hxb
    exact (Finset.image_eq_image_iff_of_injOn habInj
      Finset.subset_union_left Finset.subset_union_right).mp hab
  obtain ⟨s, hs, hsMissing⟩ := hmissing
  unfold simplicialComplexity
  calc
    (vertexCollisionPairs L g).card =
        ((vertexCollisionPairs L g).image (fun t => t.image r)).card :=
      (Finset.card_image_of_injOn himageInj).symm
    _ < (vertexCollisionPairs K f).card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨hsubset, ?_⟩
      intro heq
      exact hsMissing (by simpa only [heq] using hs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexity_lt_of_vertex_injection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexity_lt_of_vertex_injection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexity_lt_of_vertex_injection ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexity_lt_of_vertex_injection

open _root_.Classical in
theorem simplicialComplexity_lt_of_vertex_injection_of_missing_collision
    {E' F' X : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (K : Geometry.SimplicialComplex ℝ E') [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F') [Finite L.faces]
    (f : E' → X) (g : F' → X) (r : F' → E')
    (hr : _root_.Set.MapsTo r L.vertices K.vertices) (hinj : _root_.Set.InjOn r L.vertices)
    (hfactor : ∀ v ∈ L.vertices, f (r v) = g v)
    (hmissing : ∃ v ∈ K.vertices, ∃ w ∈ K.vertices,
      v ≠ w ∧ f v = f w ∧ w ∉ r '' L.vertices) :
    simplicialComplexity L g < simplicialComplexity K f := by
  apply simplicialComplexity_lt_of_vertex_injection K L f g r hr hinj hfactor
  obtain ⟨v, hv, w, hw, hvw, hfvw, hwRange⟩ := hmissing
  let s : Finset E' := {v, w}
  refine ⟨s, ?_, ?_⟩
  · rw [mem_vertexCollisionPairs]
    refine ⟨?_, by simp [s, hvw], ?_⟩
    · intro x hx
      simp only [s, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hv
      · exact hw
    · intro hfinj
      exact hvw (hfinj (by simp [s]) (by simp [s]) hfvw)
  · intro hs
    rw [Finset.mem_image] at hs
    obtain ⟨t, ht, hts⟩ := hs
    have hwImage : w ∈ t.image r := by
      rw [hts]
      simp [s]
    obtain ⟨z, hzt, hrz⟩ := Finset.mem_image.mp hwImage
    apply hwRange
    exact ⟨z, (mem_vertexCollisionPairs L g t).mp ht |>.1 hzt, hrz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexity_lt_of_vertex_injection_of_missing_collision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexity_lt_of_vertex_injection_of_missing_collision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexity_lt_of_vertex_injection_of_missing_collision ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexity_lt_of_vertex_injection_of_missing_collision

open _root_.Classical in
theorem simplicialComplexity_eq_zero_iff_injOn_vertices
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (f : E → F) :
    simplicialComplexity K f = 0 ↔ _root_.Set.InjOn f K.vertices := by
  constructor
  · intro h v hv w hw hvw
    by_contra hvw'
    have hp : ({v, w} : Finset E) ∈ vertexCollisionPairs K f := by
      rw [mem_vertexCollisionPairs]
      refine ⟨?_, by simp [hvw'], ?_⟩
      · intro z hz
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hv
        · exact hw
      · intro hinj
        exact hvw' (hinj (by simp) (by simp) hvw)
    have hempty : vertexCollisionPairs K f = ∅ := Finset.card_eq_zero.mp h
    rw [hempty] at hp
    simp at hp
  · intro hinj
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    have hdata := (mem_vertexCollisionPairs K f s).mp hs
    exact hdata.2.2 (hinj.mono hdata.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexity_eq_zero_iff_injOn_vertices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexity_eq_zero_iff_injOn_vertices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexity_eq_zero_iff_injOn_vertices ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexity_eq_zero_iff_injOn_vertices

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

open _root_.Classical in
theorem injOn_simplicialMap_of_injOn_vertices
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    (φ : E → F) (hφ : _root_.Set.InjOn φ K.vertices)
    (hfaces : ∀ s ∈ K.faces, s.image φ ∈ L.faces) :
    InjOn (simplicialMap K φ) K.space := by
  let ψ : F → E := Function.invFunOn φ K.vertices
  have hψφ : ∀ s ∈ K.faces, ∀ v ∈ s, ψ (φ v) = v := by
    intro s hs v hv
    apply hφ.leftInvOn_invFunOn
    exact K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v)
  have hleft : ∀ x ∈ K.space, simplicialMap L ψ (simplicialMap K φ x) = x :=
    fun x hx => simplicialMap_simplicialMap K L φ ψ hfaces hψφ hx
  intro x hx y hy hxy
  rw [← hleft x hx, ← hleft y hy, hxy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.injOn_simplicialMap_of_injOn_vertices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.injOn_simplicialMap_of_injOn_vertices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.injOn_simplicialMap_of_injOn_vertices ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.injOn_simplicialMap_of_injOn_vertices

theorem injOn_vertices_of_injOn_simplicialMap
    (K : Geometry.SimplicialComplex ℝ E) (φ : E → F)
    (hφ : _root_.Set.InjOn (simplicialMap K φ) K.space) : _root_.Set.InjOn φ K.vertices := by
  intro v hv w hw hvw
  apply hφ (K.vertices_subset_space hv) (K.vertices_subset_space hw)
  rw [simplicialMap_vertex K φ hv, simplicialMap_vertex K φ hw, hvw]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.injOn_vertices_of_injOn_simplicialMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.injOn_vertices_of_injOn_simplicialMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.injOn_vertices_of_injOn_simplicialMap ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.injOn_vertices_of_injOn_simplicialMap

open _root_.Classical in
theorem simplicialComplexity_eq_zero_iff_injOn_simplicialMap
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F) (φ : E → F)
    (hfaces : ∀ s ∈ K.faces, s.image φ ∈ L.faces) :
    simplicialComplexity K φ = 0 ↔ _root_.Set.InjOn (simplicialMap K φ) K.space := by
  rw [simplicialComplexity_eq_zero_iff_injOn_vertices]
  exact ⟨fun h => injOn_simplicialMap_of_injOn_vertices K L φ h hfaces,
    injOn_vertices_of_injOn_simplicialMap K φ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexity_eq_zero_iff_injOn_simplicialMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexity_eq_zero_iff_injOn_simplicialMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexity_eq_zero_iff_injOn_simplicialMap ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexity_eq_zero_iff_injOn_simplicialMap

open _root_.Classical in
noncomputable def normalSystemManifoldComplex
    {K L : Geometry.SimplicialComplex ℝ E} (T : DerivedNeighborhoodTriangulation K L) :
    Geometry.SimplicialComplex ℝ E :=
  T.complex

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.normalSystemManifoldComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.normalSystemManifoldComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.normalSystemManifoldComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.normalSystemManifoldComplex

open _root_.Classical in
noncomputable def normalSystemBoundaryComplex
    {K L : Geometry.SimplicialComplex ℝ E} (T : DerivedNeighborhoodTriangulation K L) :
    Geometry.SimplicialComplex ℝ E :=
  boundaryComplex 3 (normalSystemManifoldComplex T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.normalSystemBoundaryComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.normalSystemBoundaryComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.normalSystemBoundaryComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.normalSystemBoundaryComplex

open _root_.Classical in
noncomputable def normalSystemBoundaryNeighborhood
    {K L : Geometry.SimplicialComplex ℝ E} (T : DerivedNeighborhoodTriangulation K L)
    (C : Geometry.SimplicialComplex ℝ E) : Geometry.SimplicialComplex ℝ E :=
  derivedNeighborhood (normalSystemBoundaryComplex T) C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.normalSystemBoundaryNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.normalSystemBoundaryNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.normalSystemBoundaryNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.normalSystemBoundaryNeighborhood

open _root_.Classical in
abbrev normalSystemBoundaryNeighborhoodSpace
    {K L : Geometry.SimplicialComplex ℝ E} (T : DerivedNeighborhoodTriangulation K L)
    (C : Geometry.SimplicialComplex ℝ E) :=
  (normalSystemBoundaryNeighborhood T C).space

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.normalSystemBoundaryNeighborhoodSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.normalSystemBoundaryNeighborhoodSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.normalSystemBoundaryNeighborhoodSpace ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.normalSystemBoundaryNeighborhoodSpace

open _root_.Classical in
noncomputable def normalSystemLoopConjugacyClass
    {Y : Type*} [TopologicalSpace Y] (x : Y) (γ : freeLoop Y) (q : Path x (γ 0)) :
    ConjClasses (FundamentalGroup Y x) :=
  ConjClasses.mk (loopRepresentativeAlong q (⟨γ, rfl⟩ : basedCircleLoop (γ 0)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.normalSystemLoopConjugacyClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.normalSystemLoopConjugacyClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.normalSystemLoopConjugacyClass ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.normalSystemLoopConjugacyClass

open _root_.Classical in
structure NormalSystem (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  ambientComplex : Geometry.SimplicialComplex ℝ E
  imageComplex : Geometry.SimplicialComplex ℝ E
  loopComplex : Geometry.SimplicialComplex ℝ E
  sourceComplex : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))
  finite_ambient : ambientComplex.faces.Finite
  finite_source : sourceComplex.faces.Finite
  source_isPLBall : IsPLBall 2 sourceComplex.space
  vertexMap : EuclideanSpace ℝ (Fin 2) → E
  source_faces_map : ∀ s ∈ sourceComplex.faces, s.image vertexMap ∈ imageComplex.faces
  image_space : imageComplex.space = simplicialMap sourceComplex vertexMap '' sourceComplex.space
  image_faces_subset_ambient : imageComplex.faces ⊆ ambientComplex.faces
  neighborhood : DerivedNeighborhoodTriangulation ambientComplex imageComplex
  isManifold : IsCombinatorialManifoldWithBoundary 3
    (normalSystemManifoldComplex neighborhood)
  loop_space : loopComplex.space =
    simplicialMap sourceComplex vertexMap '' frontier sourceComplex.space
  loop_faces_subset_boundary : loopComplex.faces ⊆
    (normalSystemBoundaryComplex neighborhood).faces
  image_inter_boundary : imageComplex.space ∩
    (normalSystemBoundaryComplex neighborhood).space = loopComplex.space
  basepoint : normalSystemBoundaryNeighborhoodSpace neighborhood loopComplex
  boundaryLoop : freeLoop
    (normalSystemBoundaryNeighborhoodSpace neighborhood loopComplex)
  boundaryParam : loopCircle ≃ₜ frontier sourceComplex.space
  boundaryLoop_eq : ∀ θ, (boundaryLoop θ : E) =
    simplicialMap sourceComplex vertexMap (boundaryParam θ)
  connector : Path basepoint (boundaryLoop 0)
  normalSubgroup : Subgroup (FundamentalGroup
    (normalSystemBoundaryNeighborhoodSpace neighborhood loopComplex) basepoint)
  normal : normalSubgroup.Normal
  loopClass_avoids_normal : ¬conjugacyClassMeets
    (normalSystemLoopConjugacyClass basepoint boundaryLoop connector) normalSubgroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem

namespace NormalSystem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem boundaryLoop_range (S : NormalSystem E) :
    Set.range (fun θ => (S.boundaryLoop θ : E)) = S.loopComplex.space := by
  rw [S.loop_space]
  apply Subset.antisymm
  · rintro _ ⟨θ, rfl⟩
    change (S.boundaryLoop θ : E) ∈ _
    rw [S.boundaryLoop_eq θ]
    exact ⟨S.boundaryParam θ, (S.boundaryParam θ).property, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨θ, hθ⟩ := S.boundaryParam.surjective ⟨x, hx⟩
    refine ⟨θ, ?_⟩
    change (S.boundaryLoop θ : E) = _
    rw [S.boundaryLoop_eq θ]
    exact congrArg (simplicialMap S.sourceComplex S.vertexMap)
      (congrArg Subtype.val hθ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryLoop_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryLoop_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryLoop_range ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryLoop_range

open _root_.Classical in
noncomputable def manifoldComplex (S : NormalSystem E) : Geometry.SimplicialComplex ℝ E :=
  normalSystemManifoldComplex S.neighborhood

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.manifoldComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.manifoldComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.manifoldComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.manifoldComplex

open _root_.Classical in
theorem manifold_space (S : NormalSystem E) :
    S.manifoldComplex.space = (derivedNeighborhood S.ambientComplex S.imageComplex).space :=
  S.neighborhood.space_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.manifold_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.manifold_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.manifold_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.manifold_space

open _root_.Classical in
noncomputable def boundaryComplex (S : NormalSystem E) : Geometry.SimplicialComplex ℝ E :=
  normalSystemBoundaryComplex S.neighborhood

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryComplex

open _root_.Classical in
noncomputable def boundaryNeighborhood (S : NormalSystem E) :
    Geometry.SimplicialComplex ℝ E :=
  normalSystemBoundaryNeighborhood S.neighborhood S.loopComplex

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryNeighborhood

open _root_.Classical in
abbrev boundaryNeighborhoodSpace (S : NormalSystem E) :=
  normalSystemBoundaryNeighborhoodSpace S.neighborhood S.loopComplex

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryNeighborhoodSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryNeighborhoodSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryNeighborhoodSpace ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryNeighborhoodSpace

open _root_.Classical in
noncomputable def singularMap (S : NormalSystem E) : EuclideanSpace ℝ (Fin 2) → E :=
  simplicialMap S.sourceComplex S.vertexMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.singularMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.singularMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.singularMap ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.singularMap

def boundaryBasedLoop (S : NormalSystem E) : basedCircleLoop (S.boundaryLoop 0) :=
  ⟨S.boundaryLoop, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryBasedLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryBasedLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryBasedLoop ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryBasedLoop

open _root_.Classical in
noncomputable def loopRepresentative (S : NormalSystem E) :
    FundamentalGroup S.boundaryNeighborhoodSpace S.basepoint :=
  loopRepresentativeAlong S.connector S.boundaryBasedLoop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopRepresentative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopRepresentative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopRepresentative ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopRepresentative

open _root_.Classical in
noncomputable def loopConjugacyClass (S : NormalSystem E) :
    ConjClasses (FundamentalGroup S.boundaryNeighborhoodSpace S.basepoint) :=
  normalSystemLoopConjugacyClass S.basepoint S.boundaryLoop S.connector

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopConjugacyClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopConjugacyClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopConjugacyClass ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopConjugacyClass

def loopClassMeetsNormal (S : NormalSystem E) : Prop :=
  conjugacyClassMeets S.loopConjugacyClass S.normalSubgroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopClassMeetsNormal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopClassMeetsNormal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopClassMeetsNormal ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopClassMeetsNormal

def IsNonsingular (S : NormalSystem E) : Prop :=
  _root_.Set.InjOn S.singularMap S.sourceComplex.space

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.IsNonsingular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.IsNonsingular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.IsNonsingular ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.IsNonsingular

open _root_.Classical in
noncomputable def complexity (S : NormalSystem E) : ℕ := by
  let _ : Finite S.sourceComplex.faces := S.finite_source.to_subtype
  exact simplicialComplexity S.sourceComplex S.vertexMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.complexity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.complexity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.complexity ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.complexity

open _root_.Classical in
theorem complexity_eq_zero_iff_isNonsingular (S : NormalSystem E) :
    S.complexity = 0 ↔ S.IsNonsingular := by
  let _ : Finite S.sourceComplex.faces := S.finite_source.to_subtype
  exact simplicialComplexity_eq_zero_iff_injOn_simplicialMap
    S.sourceComplex S.imageComplex S.vertexMap S.source_faces_map

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.complexity_eq_zero_iff_isNonsingular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.complexity_eq_zero_iff_isNonsingular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.complexity_eq_zero_iff_isNonsingular ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.complexity_eq_zero_iff_isNonsingular

open _root_.Classical in
theorem singularMap_mapsTo_image (S : NormalSystem E) :
    MapsTo S.singularMap S.sourceComplex.space S.imageComplex.space :=
  simplicialMap_mapsTo S.sourceComplex S.imageComplex S.vertexMap S.source_faces_map

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.singularMap_mapsTo_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.singularMap_mapsTo_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.singularMap_mapsTo_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.singularMap_mapsTo_image

open _root_.Classical in
theorem image_faces_subset_manifoldComplex (S : NormalSystem E) :
    S.imageComplex.faces ⊆ S.manifoldComplex.faces :=
  S.neighborhood.faces_subset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.image_faces_subset_manifoldComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.image_faces_subset_manifoldComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.image_faces_subset_manifoldComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.image_faces_subset_manifoldComplex

open _root_.Classical in
theorem image_space_subset_manifoldComplex (S : NormalSystem E) :
    S.imageComplex.space ⊆ S.manifoldComplex.space := by
  exact space_mono_of_faces_subset S.image_faces_subset_manifoldComplex

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.image_space_subset_manifoldComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.image_space_subset_manifoldComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.image_space_subset_manifoldComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.image_space_subset_manifoldComplex

open _root_.Classical in
theorem image_space_subset_regularNeighborhood (S : NormalSystem E) :
    S.imageComplex.space ⊆
      (derivedNeighborhood S.ambientComplex S.imageComplex).space := by
  let _ : Finite S.ambientComplex.faces := S.finite_ambient.to_subtype
  exact subcomplex_space_subset_derivedNeighborhood S.image_faces_subset_ambient

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.image_space_subset_regularNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.image_space_subset_regularNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.image_space_subset_regularNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.image_space_subset_regularNeighborhood

open _root_.Classical in
theorem singularMap_mapsTo_manifoldComplex (S : NormalSystem E) :
    MapsTo S.singularMap S.sourceComplex.space S.manifoldComplex.space :=
  S.singularMap_mapsTo_image.mono_right S.image_space_subset_manifoldComplex

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.singularMap_mapsTo_manifoldComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.singularMap_mapsTo_manifoldComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.singularMap_mapsTo_manifoldComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.singularMap_mapsTo_manifoldComplex

open _root_.Classical in
theorem manifoldComplex_faces_finite (S : NormalSystem E) : S.manifoldComplex.faces.Finite :=
  S.neighborhood.finite_faces

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.manifoldComplex_faces_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.manifoldComplex_faces_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.manifoldComplex_faces_finite ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.manifoldComplex_faces_finite

open _root_.Classical in
theorem boundaryComplex_faces_finite (S : NormalSystem E) : S.boundaryComplex.faces.Finite := by
  let _ : Finite S.manifoldComplex.faces := S.manifoldComplex_faces_finite.to_subtype
  exact PiecewiseLinear.boundaryComplex_faces_finite 3 S.manifoldComplex

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryComplex_faces_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryComplex_faces_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryComplex_faces_finite ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryComplex_faces_finite

open _root_.Classical in
theorem boundaryNeighborhood_faces_finite (S : NormalSystem E) :
    S.boundaryNeighborhood.faces.Finite := by
  let _ : Finite S.boundaryComplex.faces := S.boundaryComplex_faces_finite.to_subtype
  exact derivedNeighborhood_faces_finite S.boundaryComplex S.loopComplex

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryNeighborhood_faces_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryNeighborhood_faces_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryNeighborhood_faces_finite ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.boundaryNeighborhood_faces_finite

open _root_.Classical in
noncomputable def imageStrongDeformationRetract [FiniteDimensional ℝ E]
    (S : NormalSystem E) :
    DifferentialGeometry.Topology.Homotopy.StrongDeformationRetract
      (derivedNeighborhoodSubcomplex S.ambientComplex S.imageComplex) := by
  let _ : Finite S.ambientComplex.faces := S.finite_ambient.to_subtype
  exact derivedNeighborhoodStrongDeformationRetract S.image_faces_subset_ambient

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.imageStrongDeformationRetract then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.imageStrongDeformationRetract"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.imageStrongDeformationRetract ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.imageStrongDeformationRetract

open _root_.Classical in
noncomputable def imageFundamentalGroupInclusionEquiv [FiniteDimensional ℝ E]
    (S : NormalSystem E)
    (x : derivedNeighborhoodSubcomplex S.ambientComplex S.imageComplex) :
    FundamentalGroup (derivedNeighborhoodSubcomplex S.ambientComplex S.imageComplex) x ≃*
      FundamentalGroup (derivedNeighborhoodSpace S.ambientComplex S.imageComplex) x.1 := by
  let _ : Finite S.ambientComplex.faces := S.finite_ambient.to_subtype
  exact derivedNeighborhoodFundamentalGroupInclusionEquiv
    (K := S.ambientComplex) (L := S.imageComplex)
    S.image_faces_subset_ambient x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.imageFundamentalGroupInclusionEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.imageFundamentalGroupInclusionEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.imageFundamentalGroupInclusionEquiv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.imageFundamentalGroupInclusionEquiv

open _root_.Classical in
noncomputable def loopStrongDeformationRetract [FiniteDimensional ℝ E]
    (S : NormalSystem E) :
    DifferentialGeometry.Topology.Homotopy.StrongDeformationRetract
      (derivedNeighborhoodSubcomplex S.boundaryComplex S.loopComplex) := by
  let _ : Finite S.boundaryComplex.faces := S.boundaryComplex_faces_finite.to_subtype
  exact derivedNeighborhoodStrongDeformationRetract S.loop_faces_subset_boundary

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopStrongDeformationRetract then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopStrongDeformationRetract"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopStrongDeformationRetract ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopStrongDeformationRetract

open _root_.Classical in
noncomputable def loopFundamentalGroupInclusionEquiv [FiniteDimensional ℝ E]
    (S : NormalSystem E)
    (x : derivedNeighborhoodSubcomplex S.boundaryComplex S.loopComplex) :
    FundamentalGroup (derivedNeighborhoodSubcomplex S.boundaryComplex S.loopComplex) x ≃*
      FundamentalGroup (derivedNeighborhoodSpace S.boundaryComplex S.loopComplex) x.1 := by
  let _ : Finite S.boundaryComplex.faces := S.boundaryComplex_faces_finite.to_subtype
  exact derivedNeighborhoodFundamentalGroupInclusionEquiv
    (K := S.boundaryComplex) (L := S.loopComplex)
    S.loop_faces_subset_boundary x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopFundamentalGroupInclusionEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopFundamentalGroupInclusionEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopFundamentalGroupInclusionEquiv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopFundamentalGroupInclusionEquiv

open _root_.Classical in
theorem loopConjugacyClass_eq_of_connector (S : NormalSystem E)
    (q : Path S.basepoint (S.boundaryLoop 0)) :
    normalSystemLoopConjugacyClass S.basepoint S.boundaryLoop q =
      S.loopConjugacyClass := by
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  exact loopRepresentativeAlong_isConj q S.connector S.boundaryBasedLoop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopConjugacyClass_eq_of_connector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopConjugacyClass_eq_of_connector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopConjugacyClass_eq_of_connector ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopConjugacyClass_eq_of_connector

open _root_.Classical in
theorem loopConjugacyClass_disjoint_normal (S : NormalSystem E) :
    Disjoint S.loopConjugacyClass.carrier (S.normalSubgroup : Set _) := by
  let _ : S.normalSubgroup.Normal := S.normal
  rcases conjugacyClass_subset_or_disjoint_normal
    S.loopConjugacyClass S.normalSubgroup with hsub | hdis
  · exact (S.loopClass_avoids_normal
      ((conjugacyClassMeets_iff_carrier_subset
        S.loopConjugacyClass S.normalSubgroup).mpr hsub)).elim
  · exact hdis

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopConjugacyClass_disjoint_normal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopConjugacyClass_disjoint_normal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopConjugacyClass_disjoint_normal ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem.loopConjugacyClass_disjoint_normal

end NormalSystem

end DifferentialGeometry.Topology.PiecewiseLinear
