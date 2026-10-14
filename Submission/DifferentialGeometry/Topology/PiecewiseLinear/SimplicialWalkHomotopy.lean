/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolygonNeighborhoodOrientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.SimpleGraph _root_.Submission.SimpleGraph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open _root_.Classical in
inductive SimplicialHomotopic (K : Geometry.SimplicialComplex ℝ E) :
    ∀ {u w : K.vertices}, (SimplicialComplex.edgeGraph K).Walk u w →
      (SimplicialComplex.edgeGraph K).Walk u w → Prop
  | refl {u w : K.vertices} (p : (SimplicialComplex.edgeGraph K).Walk u w) :
      SimplicialHomotopic K p p
  | symm {u w : K.vertices} {p q : (SimplicialComplex.edgeGraph K).Walk u w} :
      SimplicialHomotopic K p q → SimplicialHomotopic K q p
  | trans {u w : K.vertices} {p q r : (SimplicialComplex.edgeGraph K).Walk u w} :
      SimplicialHomotopic K p q → SimplicialHomotopic K q r → SimplicialHomotopic K p r
  | cons {u v w : K.vertices} (h : (SimplicialComplex.edgeGraph K).Adj u v)
      {p q : (SimplicialComplex.edgeGraph K).Walk v w} :
      SimplicialHomotopic K p q →
        SimplicialHomotopic K (Walk.cons h p) (Walk.cons h q)
  | backtrack {u v w : K.vertices} (h : (SimplicialComplex.edgeGraph K).Adj u v)
      (p : (SimplicialComplex.edgeGraph K).Walk u w) :
      SimplicialHomotopic K (Walk.cons h (Walk.cons h.symm p)) p
  | triangle {u v w x : K.vertices} (huv : (SimplicialComplex.edgeGraph K).Adj u v)
      (hvw : (SimplicialComplex.edgeGraph K).Adj v w)
      (huw : (SimplicialComplex.edgeGraph K).Adj u w)
      (hface : {(u : E), (v : E), (w : E)} ∈ K.faces)
      (p : (SimplicialComplex.edgeGraph K).Walk w x) :
      SimplicialHomotopic K (Walk.cons huv (Walk.cons hvw p)) (Walk.cons huw p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialHomotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SimplicialHomotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialHomotopic ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplicialHomotopic

variable {K : Geometry.SimplicialComplex ℝ E}

namespace SimplicialBoolCocycle

variable (ε : SimplicialBoolCocycle K)

open _root_.Classical in
theorem walkMonodromy_eq_of_simplicialHomotopic {u w : K.vertices}
    {p q : (SimplicialComplex.edgeGraph K).Walk u w} (h : SimplicialHomotopic K p q) :
    ε.walkMonodromy p = ε.walkMonodromy q := by
  induction h with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | cons hadj _ ih => rw [ε.walkMonodromy_cons, ε.walkMonodromy_cons, ih]
  | backtrack hadj r =>
      rw [ε.walkMonodromy_cons, ε.walkMonodromy_cons, ε.parity_symm_of_adj hadj,
        ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  | triangle huv hvw huw hface r =>
      rw [ε.walkMonodromy_cons, ε.walkMonodromy_cons, ε.walkMonodromy_cons, ← add_assoc,
        ← boolZMod2_xor, ε.cocycle _ _ _ hface]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_of_simplicialHomotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_of_simplicialHomotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_of_simplicialHomotopic ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_of_simplicialHomotopic

theorem walkMonodromy_eq_zero_of_simplicialHomotopic_nil {v₀ : K.vertices}
    {γ : (SimplicialComplex.edgeGraph K).Walk v₀ v₀}
    (h : SimplicialHomotopic K γ Walk.nil) : ε.walkMonodromy γ = 0 := by
  rw [ε.walkMonodromy_eq_of_simplicialHomotopic h, ε.walkMonodromy_nil]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_zero_of_simplicialHomotopic_nil then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_zero_of_simplicialHomotopic_nil"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_zero_of_simplicialHomotopic_nil ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_zero_of_simplicialHomotopic_nil

open _root_.Classical in
theorem isCoboundary_of_polygon_contraction
    (hconn : (SimplicialComplex.edgeGraph K).Preconnected) {v₀ : K.vertices}
    (γ : (SimplicialComplex.edgeGraph K).Walk v₀ v₀)
    (hgen : ∀ (u : K.vertices) (p : (SimplicialComplex.edgeGraph K).Walk u u),
      ε.walkMonodromy p = 0 ∨ ε.walkMonodromy p = ε.walkMonodromy γ)
    (hcontract : SimplicialHomotopic K γ Walk.nil) : ε.IsCoboundary :=
  ε.isCoboundary_of_walkMonodromy_generated hconn γ hgen
    (ε.walkMonodromy_eq_zero_of_simplicialHomotopic_nil hcontract)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.isCoboundary_of_polygon_contraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.isCoboundary_of_polygon_contraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.isCoboundary_of_polygon_contraction ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.isCoboundary_of_polygon_contraction

end SimplicialBoolCocycle

variable [FiniteDimensional ℝ E] [Finite K.faces] {n : ℕ}

local instance finite_faceStarComplex_faces_walkHomotopy
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] (s : Finset E) :
    Finite (faceStarComplex L s).faces := (faceStarComplex_faces_finite L s).to_subtype

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.finite_faceStarComplex_faces_walkHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.finite_faceStarComplex_faces_walkHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.finite_faceStarComplex_faces_walkHomotopy ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.finite_faceStarComplex_faces_walkHomotopy

open _root_.Classical in
theorem isOrientable_of_polygon_contraction
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    (hconn : (SimplicialComplex.edgeGraph (barycentricSubdivision K)).Preconnected)
    {v₀ : (barycentricSubdivision K).vertices}
    (γ : (SimplicialComplex.edgeGraph (barycentricSubdivision K)).Walk v₀ v₀)
    (hgen : ∀ (u : (barycentricSubdivision K).vertices)
      (p : (SimplicialComplex.edgeGraph (barycentricSubdivision K)).Walk u u),
      (orientationCocycle hK o).walkMonodromy p = 0 ∨
        (orientationCocycle hK o).walkMonodromy p =
          (orientationCocycle hK o).walkMonodromy γ)
    (hcontract : SimplicialHomotopic (barycentricSubdivision K) γ Walk.nil) :
    IsOrientable n K :=
  isOrientable_of_polygon_walkMonodromy_eq_zero hK o hconn γ hgen
    ((orientationCocycle hK o).walkMonodromy_eq_zero_of_simplicialHomotopic_nil hcontract)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_polygon_contraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_polygon_contraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_polygon_contraction ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_polygon_contraction

end DifferentialGeometry.Topology.PiecewiseLinear
