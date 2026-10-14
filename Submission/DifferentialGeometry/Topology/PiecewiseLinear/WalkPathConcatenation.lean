/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.FundamentalGroup.LoopPower
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.AmbientPolygonOrientation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.WalkArcPath
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.WalkMonodromyHomotopy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Set _root_.SimpleGraph _root_.Submission.SimpleGraph

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Geometry.SimplicialComplex ℝ E}

open _root_.Classical in
theorem edgePath_symm {a b : K.vertices} (hab : (SimplicialComplex.edgeGraph K).Adj a b) :
    edgePath hab.symm = (edgePath hab).symm := by
  refine Path.ext (funext fun t => Subtype.ext ?_)
  have h1 : ((edgePath hab.symm t : K.space) : E) =
      (1 - (t : ℝ)) • (b : E) + (t : ℝ) • (a : E) := edgePath_apply hab.symm t
  have h2 : (((edgePath hab).symm t : K.space) : E) =
      (1 - ((unitInterval.symm t : unitInterval) : ℝ)) • (a : E) +
        ((unitInterval.symm t : unitInterval) : ℝ) • (b : E) :=
    edgePath_apply hab (unitInterval.symm t)
  rw [h1, h2, unitInterval.coe_symm_eq]
  module

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.edgePath_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.edgePath_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.edgePath_symm ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.edgePath_symm

open _root_.Classical in
theorem walkPath_append : ∀ {u v w : K.vertices}
    (p : (SimplicialComplex.edgeGraph K).Walk u v)
    (q : (SimplicialComplex.edgeGraph K).Walk v w),
    (walkPath (p.append q)).Homotopic ((walkPath p).trans (walkPath q)) := by
  intro u v w p
  induction p with
  | nil => intro q; exact (Path.Homotopic.refl_trans (walkPath q)).symm
  | @cons u v w h p ih =>
      intro q
      exact ((Path.Homotopic.refl (edgePath h)).hcomp (ih q)).trans
        (Path.Homotopic.trans_assoc (edgePath h) (walkPath p) (walkPath q)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.walkPath_append then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.walkPath_append"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.walkPath_append ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.walkPath_append

open _root_.Classical in
theorem walkPath_reverse : ∀ {u v : K.vertices} (p : (SimplicialComplex.edgeGraph K).Walk u v),
    (walkPath p.reverse).Homotopic (walkPath p).symm := by
  intro u v p
  induction p with
  | nil => exact Path.Homotopic.refl _
  | @cons u v w h p ih =>
      rw [Walk.reverse_cons, walkPath_cons, Path.trans_symm]
      refine (walkPath_append p.reverse (Walk.cons h.symm Walk.nil)).trans (ih.hcomp ?_)
      rw [← edgePath_symm]
      exact Path.Homotopic.trans_refl _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.walkPath_reverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.walkPath_reverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.walkPath_reverse ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.walkPath_reverse

open _root_.Classical in
theorem walkPath_closedWalkPow {u : K.vertices}
    (γ : (SimplicialComplex.edgeGraph K).Walk u u) (k : ℕ) :
    (walkPath (closedWalkPow γ k)).Homotopic (loopPow (walkPath γ) k) := by
  induction k with
  | zero => exact Path.Homotopic.refl _
  | succ k ih =>
      exact (walkPath_append γ (closedWalkPow γ k)).trans
        ((Path.Homotopic.refl (walkPath γ)).hcomp ih)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.walkPath_closedWalkPow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.walkPath_closedWalkPow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.walkPath_closedWalkPow ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.walkPath_closedWalkPow

open _root_.Classical in
theorem walkPath_closedWalkZPow {u : K.vertices}
    (γ : (SimplicialComplex.edgeGraph K).Walk u u) (k : ℤ) :
    (walkPath (closedWalkZPow γ k)).Homotopic (loopZPow (walkPath γ) k) := by
  cases k with
  | ofNat k => exact walkPath_closedWalkPow γ k
  | negSucc k =>
      exact (walkPath_closedWalkPow γ.reverse (k + 1)).trans
        (loopPow_homotopic (walkPath_reverse γ) (k + 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.walkPath_closedWalkZPow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.walkPath_closedWalkZPow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.walkPath_closedWalkZPow ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.walkPath_closedWalkZPow

theorem quotient_conjugate {X : Type*} [TopologicalSpace X] {a b : X}
    (P : Path.Homotopic.Quotient a a) (R : Path.Homotopic.Quotient a b) :
    R.trans ((R.symm.trans (P.trans R)).trans R.symm) = P := by
  rw [Path.Homotopic.Quotient.trans_assoc R.symm (P.trans R) R.symm,
    ← Path.Homotopic.Quotient.trans_assoc R R.symm ((P.trans R).trans R.symm),
    Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans,
    Path.Homotopic.Quotient.trans_assoc P R R.symm,
    Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.trans_refl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.quotient_conjugate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.quotient_conjugate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.quotient_conjugate ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.quotient_conjugate

theorem homotopic_conjugate {X : Type*} [TopologicalSpace X] {a b : X}
    (p : Path a a) (r : Path a b) :
    p.Homotopic (r.trans ((r.symm.trans (p.trans r)).trans r.symm)) :=
  Path.Homotopic.Quotient.eq.mp
    (quotient_conjugate (Path.Homotopic.Quotient.mk p) (Path.Homotopic.Quotient.mk r)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.homotopic_conjugate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.homotopic_conjugate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.homotopic_conjugate ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.homotopic_conjugate

open _root_.Classical in
theorem exists_zpow_conjugate_homotopic_walkPath
    (hconn : (SimplicialComplex.edgeGraph K).Preconnected) {v₀ : K.vertices}
    (γ : (SimplicialComplex.edgeGraph K).Walk v₀ v₀)
    (hgen : ∀ ℓ : Path (vertexPoint K v₀) (vertexPoint K v₀),
      ∃ k : ℤ, ℓ.Homotopic (loopZPow (walkPath γ) k))
    (u : K.vertices) (p : (SimplicialComplex.edgeGraph K).Walk u u) :
    ∃ (q : (SimplicialComplex.edgeGraph K).Walk u v₀) (k : ℤ),
      (walkPath p).Homotopic (walkPath (q.append ((closedWalkZPow γ k).append q.reverse))) := by
  obtain ⟨q⟩ := hconn u v₀
  obtain ⟨k, hk⟩ := hgen ((walkPath q).symm.trans ((walkPath p).trans (walkPath q)))
  refine ⟨q, k, ?_⟩
  have hmid : (((walkPath q).symm.trans ((walkPath p).trans (walkPath q)))).Homotopic
      (walkPath (closedWalkZPow γ k)) := hk.trans (walkPath_closedWalkZPow γ k).symm
  have hkey := (homotopic_conjugate (walkPath p) (walkPath q)).trans
    ((Path.Homotopic.refl (walkPath q)).hcomp
      (hmid.hcomp (Path.Homotopic.refl (walkPath q).symm)))
  refine hkey.trans ?_
  refine (Path.Homotopic.symm ?_)
  exact (walkPath_append q ((closedWalkZPow γ k).append q.reverse)).trans
    ((Path.Homotopic.refl (walkPath q)).hcomp
      ((walkPath_append (closedWalkZPow γ k) q.reverse).trans
        ((Path.Homotopic.refl (walkPath (closedWalkZPow γ k))).hcomp (walkPath_reverse q))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_zpow_conjugate_homotopic_walkPath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_zpow_conjugate_homotopic_walkPath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_zpow_conjugate_homotopic_walkPath ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_zpow_conjugate_homotopic_walkPath

theorem space_subset_space_of_faces_subset {L : Geometry.SimplicialComplex ℝ E}
    (hLK : L.faces ⊆ K.faces) : L.space ⊆ K.space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
  exact Geometry.SimplicialComplex.convexHull_subset_space (hLK hs) hxs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.space_subset_space_of_faces_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.space_subset_space_of_faces_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.space_subset_space_of_faces_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.space_subset_space_of_faces_subset

def spaceInclusion {L : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces) :
    C(L.space, K.space) :=
  ⟨fun x => ⟨(x : E), space_subset_space_of_faces_subset hLK x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spaceInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spaceInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spaceInclusion ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spaceInclusion

open _root_.Classical in
theorem edgePath_map {L : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces)
    {a b : L.vertices} (hab : (SimplicialComplex.edgeGraph L).Adj a b) :
    edgePath ((edgeGraphHom hLK).map_adj hab) =
      (edgePath hab).map (spaceInclusion hLK).continuous := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.edgePath_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.edgePath_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.edgePath_map ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.edgePath_map

open _root_.Classical in
theorem walkPath_map {L : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces) :
    ∀ {u w : L.vertices} (p : (SimplicialComplex.edgeGraph L).Walk u w),
      walkPath (p.map (edgeGraphHom hLK)) = (walkPath p).map (spaceInclusion hLK).continuous := by
  intro u w p
  induction p with
  | nil => rfl
  | @cons u v w h q ih =>
      rw [Walk.map_cons, walkPath_cons, ih, walkPath_cons, Path.map_trans, edgePath_map hLK h]
      rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.walkPath_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.walkPath_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.walkPath_map ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.walkPath_map

end DifferentialGeometry.Topology.PiecewiseLinear
