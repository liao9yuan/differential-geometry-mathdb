/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Integral
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CellMapTriangulation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ControlledInwardPush
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.TameNestedCells

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe v

section Label

inductive Section34BoundedLabel (Vx Tt Ed Fc Pa Ar Eg Mk Ov Oe : Type v) : Type v
  | vertexBall (v : Vx)
  | tetraBall (t : Tt)
  | splitDisk (e : Ed)
  | faceDisk (s : Fc)
  | patch (x : Pa)
  | faceArc (a : Ar)
  | edgeArc (i : Eg)
  | markedPoint (p : Mk)
  | outerFace (o : Ov)
  | outerArc (q : Oe)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34BoundedLabel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34BoundedLabel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34BoundedLabel ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34BoundedLabel

variable {Vx Tt Ed Fc Pa Ar Eg Mk Ov Oe : Type v}

def section34BoundedDim : Section34BoundedLabel Vx Tt Ed Fc Pa Ar Eg Mk Ov Oe → ℕ
  | .vertexBall _ => 3
  | .tetraBall _ => 3
  | .splitDisk _ => 2
  | .faceDisk _ => 2
  | .patch _ => 2
  | .faceArc _ => 1
  | .edgeArc _ => 1
  | .markedPoint _ => 0
  | .outerFace _ => 2
  | .outerArc _ => 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedDim then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedDim"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedDim ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedDim

def section34BoundedCell {M : Type*} (cV : Vx → Set M) (cT : Tt → Set M) (cE : Ed → Set M)
    (cF : Fc → Set M) (cP : Pa → Set M) (cA : Ar → Set M) (cG : Eg → Set M) (cM : Mk → Set M)
    (cO : Ov → Set M) (cQ : Oe → Set M) :
    Section34BoundedLabel Vx Tt Ed Fc Pa Ar Eg Mk Ov Oe → Set M
  | .vertexBall v => cV v
  | .tetraBall t => cT t
  | .splitDisk e => cE e
  | .faceDisk s => cF s
  | .patch x => cP x
  | .faceArc a => cA a
  | .edgeArc i => cG i
  | .markedPoint p => cM p
  | .outerFace o => cO o
  | .outerArc q => cQ q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedCell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedCell

theorem section34BoundedDim_le_three (l : Section34BoundedLabel Vx Tt Ed Fc Pa Ar Eg Mk Ov Oe) :
    section34BoundedDim l ≤ 3 := by
  cases l <;> simp [section34BoundedDim]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedDim_le_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedDim_le_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedDim_le_three ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedDim_le_three

theorem section34BoundedDim_eq_three {l : Section34BoundedLabel Vx Tt Ed Fc Pa Ar Eg Mk Ov Oe}
    (hl : section34BoundedDim l = 3) : (∃ v, l = .vertexBall v) ∨ ∃ t, l = .tetraBall t := by
  cases l <;> first
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr ⟨_, rfl⟩
    | simp [section34BoundedDim] at hl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedDim_eq_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedDim_eq_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedDim_eq_three ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedDim_eq_three

def section34BoundedEncode : Section34BoundedLabel Vx Tt Ed Fc Pa Ar Eg Mk Ov Oe →
    Option Vx × Option Tt × Option Ed × Option Fc × Option Pa × Option Ar × Option Eg ×
      Option Mk × Option Ov × Option Oe
  | .vertexBall v => (_root_.Option.some v, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none)
  | .tetraBall t => (_root_.Option.none, _root_.Option.some t, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none)
  | .splitDisk e => (_root_.Option.none, _root_.Option.none, _root_.Option.some e, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none)
  | .faceDisk s => (_root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.some s, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none)
  | .patch x => (_root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.some x, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none)
  | .faceArc a => (_root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.some a, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none)
  | .edgeArc i => (_root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.some i, _root_.Option.none, _root_.Option.none, _root_.Option.none)
  | .markedPoint p => (_root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.some p, _root_.Option.none, _root_.Option.none)
  | .outerFace o => (_root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.some o, _root_.Option.none)
  | .outerArc q => (_root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.none, _root_.Option.some q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedEncode then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedEncode"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedEncode ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedEncode

theorem section34BoundedEncode_injective :
    Function.Injective (section34BoundedEncode (Vx := Vx) (Tt := Tt) (Ed := Ed) (Fc := Fc)
      (Pa := Pa) (Ar := Ar) (Eg := Eg) (Mk := Mk) (Ov := Ov) (Oe := Oe)) := by
  intro l m hlm
  cases l <;> cases m <;>
    simp only [section34BoundedEncode, Prod.mk.injEq, Option.some.injEq, reduceCtorEq,
      and_true, true_and, and_false] at hlm <;>
    rw [hlm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedEncode_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedEncode_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedEncode_injective ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34BoundedEncode_injective

instance _root_.Submission.DifferentialGeometry.Topology.PiecewiseLinear.instFiniteSection34BoundedLabel [Finite Vx] [Finite Tt] [Finite Ed] [Finite Fc] [Finite Pa] [Finite Ar] [Finite Eg]
    [Finite Mk] [Finite Ov] [Finite Oe] :
    Finite (Section34BoundedLabel Vx Tt Ed Fc Pa Ar Eg Mk Ov Oe) :=
  Finite.of_injective _ section34BoundedEncode_injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.instFiniteSection34BoundedLabel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.instFiniteSection34BoundedLabel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.instFiniteSection34BoundedLabel ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.instFiniteSection34BoundedLabel

end Label

section Vocabulary

variable {K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}

def section34CompactGraphSkeleton (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  ⋃ t ∈ {t : Finset (EuclideanSpace ℝ (Fin 3)) | t ∈ K.faces ∧ t.card ≤ 2},
    convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin 3)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactGraphSkeleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34CompactGraphSkeleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactGraphSkeleton ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34CompactGraphSkeleton

def section34CompactSimplexRim (t : Finset (EuclideanSpace ℝ (Fin 3))) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  ⋃ s ∈ {s : Finset (EuclideanSpace ℝ (Fin 3)) | s ⊂ t},
    convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 3)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactSimplexRim then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34CompactSimplexRim"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactSimplexRim ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34CompactSimplexRim

def section34CompactCarrierSupport (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (t : Finset (EuclideanSpace ℝ (Fin 3))) : Set (EuclideanSpace ℝ (Fin 3)) :=
  ⋃ w ∈ (t : Set (EuclideanSpace ℝ (Fin 3))),
    ⋃ s ∈ {s : Finset (EuclideanSpace ℝ (Fin 3)) | s ∈ K.faces ∧ w ∈ s},
      convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 3)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactCarrierSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34CompactCarrierSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactCarrierSupport ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34CompactCarrierSupport

theorem section34CompactSimplexRim_subset (t : Finset (EuclideanSpace ℝ (Fin 3))) :
    section34CompactSimplexRim t ⊆ convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin 3))) :=
  _root_.Set.iUnion₂_subset fun _ hs => convexHull_mono (Finset.coe_subset.mpr hs.subset)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactSimplexRim_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34CompactSimplexRim_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactSimplexRim_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34CompactSimplexRim_subset

abbrev Section34CompactSimplexIndex
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) (k : ℕ) :=
  {t : Finset (EuclideanSpace ℝ (Fin 3)) // t ∈ K.faces ∧ t.card = k}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactSimplexIndex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactSimplexIndex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactSimplexIndex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactSimplexIndex

abbrev Section34CompactGraphIndex
    (K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (Γ : Set (EuclideanSpace ℝ (Fin 3))) (k : ℕ) :=
  {t : Finset (EuclideanSpace ℝ (Fin 3)) //
    t ∈ K'.faces ∧ t.card = k ∧ convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Γ}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGraphIndex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGraphIndex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGraphIndex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGraphIndex

abbrev Section34CompactVertexIndex
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) :=
  Section34CompactGraphIndex K' (section34CompactGraphSkeleton K) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVertexIndex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVertexIndex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVertexIndex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVertexIndex

abbrev Section34CompactEdgeIndex
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) :=
  Section34CompactGraphIndex K' (section34CompactGraphSkeleton K) 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactEdgeIndex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactEdgeIndex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactEdgeIndex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactEdgeIndex

abbrev Section34CompactPatchIndex
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) :=
  {p : Section34CompactSimplexIndex K 4 × Section34CompactVertexIndex K K' //
    Section34Incident p.2.1 p.1.1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactPatchIndex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactPatchIndex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactPatchIndex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactPatchIndex

abbrev Section34CompactArcIndex
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) :=
  {p : Section34CompactSimplexIndex K 3 × Section34CompactVertexIndex K K' //
    Section34Incident p.2.1 p.1.1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactArcIndex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactArcIndex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactArcIndex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactArcIndex

abbrev Section34CompactEdgeArcIndex
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) :=
  {p : Section34CompactSimplexIndex K 4 × Section34CompactEdgeIndex K K' //
    Section34Incident p.2.1 p.1.1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactEdgeArcIndex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactEdgeArcIndex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactEdgeArcIndex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactEdgeArcIndex

abbrev Section34CompactMarkIndex
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) :=
  {p : Section34CompactSimplexIndex K 3 × Section34CompactEdgeIndex K K' //
    Section34Incident p.2.1 p.1.1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactMarkIndex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactMarkIndex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactMarkIndex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactMarkIndex

abbrev Section34CompactOuterVertexIndex
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) :=
  {w : Section34CompactVertexIndex K K' //
    (w.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ frontier K.space}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactOuterVertexIndex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactOuterVertexIndex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactOuterVertexIndex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactOuterVertexIndex

abbrev Section34CompactOuterEdgeIndex
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) :=
  {e : Section34CompactEdgeIndex K K' //
    convexHull ℝ (e.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ frontier K.space}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactOuterEdgeIndex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactOuterEdgeIndex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactOuterEdgeIndex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactOuterEdgeIndex

abbrev Section34CompactLabelOf
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) :=
  Section34BoundedLabel (Section34CompactVertexIndex K K') (Section34CompactSimplexIndex K 4)
    (Section34CompactEdgeIndex K K') (Section34CompactSimplexIndex K 3)
    (Section34CompactPatchIndex K K') (Section34CompactArcIndex K K')
    (Section34CompactEdgeArcIndex K K') (Section34CompactMarkIndex K K')
    (Section34CompactOuterVertexIndex K K') (Section34CompactOuterEdgeIndex K K')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactLabelOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactLabelOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactLabelOf ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactLabelOf

theorem finite_section34CompactSimplexIndex (hK : K.faces.Finite) (k : ℕ) :
    Finite (Section34CompactSimplexIndex K k) :=
  (hK.subset fun _ ht => ht.1).to_subtype

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.finite_section34CompactSimplexIndex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.finite_section34CompactSimplexIndex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.finite_section34CompactSimplexIndex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.finite_section34CompactSimplexIndex

theorem finite_section34CompactGraphIndex (hK' : K'.faces.Finite)
    (Γ : Set (EuclideanSpace ℝ (Fin 3))) (k : ℕ) :
    Finite (Section34CompactGraphIndex K' Γ k) :=
  (hK'.subset fun _ ht => ht.1).to_subtype

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.finite_section34CompactGraphIndex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.finite_section34CompactGraphIndex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.finite_section34CompactGraphIndex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.finite_section34CompactGraphIndex

theorem finite_section34CompactLabelOf (hK : K.faces.Finite) (hK' : K'.faces.Finite) :
    Finite (Section34CompactLabelOf K K') := by
  have h3 := finite_section34CompactSimplexIndex hK 3
  have h4 := finite_section34CompactSimplexIndex hK 4
  have hv := finite_section34CompactGraphIndex hK' (section34CompactGraphSkeleton K) 1
  have he := finite_section34CompactGraphIndex hK' (section34CompactGraphSkeleton K) 2
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.finite_section34CompactLabelOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.finite_section34CompactLabelOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.finite_section34CompactLabelOf ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.finite_section34CompactLabelOf

theorem exists_face_of_section34CompactVertexIndex (w : Section34CompactVertexIndex K K') :
    ∃ t ∈ K.faces, (w.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin 3))) := by
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp w.2.2.1
  have hvΓ : v ∈ section34CompactGraphSkeleton K :=
    w.2.2.2 (subset_convexHull ℝ _ (by rw [hv]; simp))
  simp only [section34CompactGraphSkeleton, _root_.Set.mem_iUnion, _root_.Set.mem_ofPred_eq, exists_prop] at hvΓ
  obtain ⟨t, ⟨ht, -⟩, hvt⟩ := hvΓ
  refine ⟨t, ht, ?_⟩
  rw [hv, Finset.coe_singleton, _root_.Set.singleton_subset_iff]
  exact hvt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_face_of_section34CompactVertexIndex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_face_of_section34CompactVertexIndex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_face_of_section34CompactVertexIndex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_face_of_section34CompactVertexIndex

def Section34CompactCutStep :
    Section34CompactLabelOf K K' → Section34CompactLabelOf K K' → Prop
  | .splitDisk e, .vertexBall w => w.1 ⊆ e.1
  | .patch x, .vertexBall w => x.1.2 = w
  | .outerFace o, .vertexBall w => o.1 = w
  | .faceDisk s, .tetraBall t => Section34Incident s.1 t.1
  | .patch x, .tetraBall t => x.1.1 = t
  | .edgeArc i, .splitDisk e => i.1.2 = e
  | .outerArc q, .splitDisk e => q.1 = e
  | .faceArc a, .faceDisk s => a.1.1 = s
  | .faceArc a, .patch x => a.1.2 = x.1.2 ∧ Section34Incident a.1.1.1 x.1.1.1
  | .edgeArc i, .patch x => i.1.1 = x.1.1 ∧ x.1.2.1 ⊆ i.1.2.1
  | .faceArc a, .outerFace o =>
    a.1.2 = o.1 ∧ convexHull ℝ (a.1.1.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ frontier K.space
  | .outerArc q, .outerFace o => o.1.1 ⊆ q.1.1
  | .markedPoint p, .faceArc a => p.1.1 = a.1.1 ∧ a.1.2.1 ⊆ p.1.2.1
  | .markedPoint p, .edgeArc i => p.1.2 = i.1.2 ∧ Section34Incident p.1.1.1 i.1.1.1
  | .markedPoint p, .outerArc q =>
    p.1.2 = q.1 ∧ convexHull ℝ (p.1.1.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ frontier K.space
  | _, _ => False

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCutStep then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCutStep"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCutStep ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCutStep

def Section34CompactCutLe :
    Section34CompactLabelOf K K' → Section34CompactLabelOf K K' → Prop :=
  Relation.ReflTransGen Section34CompactCutStep

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCutLe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCutLe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCutLe ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCutLe

def section34CompactCutNeighborhood
    (src : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  ⋃ w : Section34CompactVertexIndex K K', src (.vertexBall w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactCutNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34CompactCutNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactCutNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34CompactCutNeighborhood

def section34CompactFaceTorus
    (V : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (s : Section34CompactSimplexIndex K 3) : Set (EuclideanSpace ℝ (Fin 3)) :=
  ⋃ (a : Section34CompactArcIndex K K') (_ : a.1.1 = s), V a.1.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactFaceTorus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34CompactFaceTorus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactFaceTorus ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34CompactFaceTorus

def section34CompactVertexBallImage
    (c : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (w : Section34CompactVertexIndex K K') : Set (EuclideanSpace ℝ (Fin 3)) :=
  g '' c (.vertexBall w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactVertexBallImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34CompactVertexBallImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactVertexBallImage ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34CompactVertexBallImage

def section34CompactSplitDiskImage
    (c : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (e : Section34CompactEdgeIndex K K') : Set (EuclideanSpace ℝ (Fin 3)) :=
  g '' c (.splitDisk e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactSplitDiskImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34CompactSplitDiskImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactSplitDiskImage ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34CompactSplitDiskImage

open _root_.Classical in
def Section34CompactLinkCondition
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin 3), {v} ∈ K.faces →
    ∀ e ∈ (SimplicialComplex.geometricLink K {v}).faces, e.card = 2 →
    ∀ a b : EuclideanSpace ℝ (Fin 3), {a} ∈ (SimplicialComplex.geometricLink K {v}).faces →
      {b} ∈ (SimplicialComplex.geometricLink K {v}).faces →
      b ∈ connectedComponentIn ((SimplicialComplex.geometricLink K {v}).space \
        (convexHull ℝ (e : Set (EuclideanSpace ℝ (Fin 3))) \ (e : Set (EuclideanSpace ℝ (Fin 3)))))
        a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactLinkCondition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactLinkCondition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactLinkCondition ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactLinkCondition

def Section34CompactCutFrame (C : Set (EuclideanSpace ℝ (Fin 3)))
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (src srcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  K.space = C ∧
  K.faces.Finite ∧
  K'.faces.Finite ∧
  IsCombinatorialManifoldWithBoundary 3 K ∧
  IsSubdivision K' K ∧
  Section34CompactLinkCondition K ∧
  (∀ l, IsPLCellOn (section34BoundedDim l) (src l) (srcBd l)) ∧
  (∀ l, srcBd l = ⋃ m ∈ section34Face src l \ {l}, src m) ∧
  (∀ l m, src l ∩ src m = ⋃ k ∈ section34Face src l ∩ section34Face src m, src k) ∧
  (∀ l m, src m ⊆ src l → m = l ∨ section34BoundedDim m < section34BoundedDim l) ∧
  (⋃ l, src l) = C ∪ section34CompactCutNeighborhood src ∧
  (∀ a : Section34CompactArcIndex K K',
    src (.faceArc a) = src (.vertexBall a.1.2) ∩ src (.faceDisk a.1.1)) ∧
  (∀ p : Section34CompactMarkIndex K K',
    src (.markedPoint p) = src (.splitDisk p.1.2) ∩ src (.faceDisk p.1.1)) ∧
  (∀ x : Section34CompactPatchIndex K K',
    src (.patch x) = src (.tetraBall x.1.1) ∩ src (.vertexBall x.1.2)) ∧
  (∀ i : Section34CompactEdgeArcIndex K K',
    src (.edgeArc i) = src (.tetraBall i.1.1) ∩ src (.splitDisk i.1.2)) ∧
  (∀ o : Section34CompactOuterVertexIndex K K', src (.outerFace o) =
    closure (srcBd (.vertexBall o.1) \
      (C ∪ ⋃ e : Section34CompactEdgeIndex K K', src (.splitDisk e)))) ∧
  (∀ q : Section34CompactOuterEdgeIndex K K',
    src (.outerArc q) = closure (srcBd (.splitDisk q.1) \ C)) ∧
  (∀ s : Section34CompactSimplexIndex K 3, src (.faceDisk s) =
    closure (convexHull ℝ (s.1 : Set (EuclideanSpace ℝ (Fin 3))) \
      section34CompactCutNeighborhood src)) ∧
  (∀ t : Section34CompactSimplexIndex K 4, src (.tetraBall t) =
    closure (convexHull ℝ (t.1 : Set (EuclideanSpace ℝ (Fin 3))) \
      section34CompactCutNeighborhood src)) ∧
  (∀ (s : Section34CompactSimplexIndex K 3) (w : Section34CompactVertexIndex K K'),
    ¬ Section34Incident w.1 s.1 → src (.faceDisk s) ∩ src (.vertexBall w) = ∅) ∧
  (∀ (s : Section34CompactSimplexIndex K 3) (e : Section34CompactEdgeIndex K K'),
    ¬ Section34Incident e.1 s.1 → src (.faceDisk s) ∩ src (.splitDisk e) = ∅) ∧
  (∀ (t : Section34CompactSimplexIndex K 4) (w : Section34CompactVertexIndex K K'),
    ¬ Section34Incident w.1 t.1 → src (.tetraBall t) ∩ src (.vertexBall w) = ∅) ∧
  (∀ (t : Section34CompactSimplexIndex K 4) (e : Section34CompactEdgeIndex K K'),
    ¬ Section34Incident e.1 t.1 → src (.tetraBall t) ∩ src (.splitDisk e) = ∅) ∧
  (∀ l, ∃ m, section34BoundedDim m = 3 ∧ src l ⊆ src m) ∧
  (∀ w : Section34CompactVertexIndex K K',
    (w.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ src (.vertexBall w)) ∧
  (∀ (w : Section34CompactVertexIndex K K') (e : Section34CompactEdgeIndex K K'),
    (src (.vertexBall w) ∩ src (.splitDisk e)).Nonempty → w.1 ⊆ e.1) ∧
  (∀ e : Section34CompactEdgeIndex K K', ∃ w w' : Section34CompactVertexIndex K K', w ≠ w' ∧
    (e.1 : Set (EuclideanSpace ℝ (Fin 3))) =
      (w.1 : Set (EuclideanSpace ℝ (Fin 3))) ∪ (w'.1 : Set (EuclideanSpace ℝ (Fin 3))) ∧
    src (.splitDisk e) = src (.vertexBall w) ∩ src (.vertexBall w')) ∧
  (∀ (t : Section34CompactSimplexIndex K 4) (s : Section34CompactSimplexIndex K 3),
    Section34Incident s.1 t.1 → src (.faceDisk s) ⊆ src (.tetraBall t)) ∧
  ∀ s : Section34CompactSimplexIndex K 3, ∃ t : Section34CompactSimplexIndex K 4,
    Section34Incident s.1 t.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCutFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCutFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCutFrame ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCutFrame

def Section34CompactCarrierControl
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (ε : ℝ)
    (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  (∀ t ∈ K.faces, h '' section34CompactCarrierSupport K t ⊆ interior (H t)) ∧
  (∀ t ∈ K.faces, ∀ y ∈ H t, ∀ z ∈ H t, _root_.Dist.dist y z < ε) ∧
  ∀ t ∈ K.faces, IsPLCellOn 3 (H t) (frontier (H t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCarrierControl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCarrierControl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCarrierControl ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCarrierControl

def section34CompactTetraObstacle
    (tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (fbl : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (t : Section34CompactSimplexIndex K 4) : Set (EuclideanSpace ℝ (Fin 3)) :=
  (⋃ (x : Section34CompactPatchIndex K K') (_ : x.1.1 = t), tgtV x.1.2) ∪
    ⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1), fbl s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactTetraObstacle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34CompactTetraObstacle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactTetraObstacle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34CompactTetraObstacle

def Section34CompactExterior
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (fbl : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ (t : Section34CompactSimplexIndex K 4) (w : Section34CompactVertexIndex K K'),
    ¬ Section34Incident w.1 t.1 → ∀ y ∈ h '' (w.1 : Set (EuclideanSpace ℝ (Fin 3))),
      ¬ Bornology.IsBounded
        (connectedComponentIn (section34CompactTetraObstacle tgtV fbl t)ᶜ y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactExterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactExterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactExterior ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactExterior

theorem section34CompactExterior_mono
    {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {fbl fbl' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hsub : ∀ s, fbl s ⊆ fbl' s) (hext : Section34CompactExterior K K' h tgtV fbl') :
    Section34CompactExterior K K' h tgtV fbl := by
  intro t w hw y hy hb
  have hobs : section34CompactTetraObstacle tgtV fbl t ⊆
      section34CompactTetraObstacle tgtV fbl' t :=
    _root_.Set.union_subset_union Subset.rfl (_root_.Set.iUnion₂_mono fun s _ => hsub s)
  exact hext t w hw y hy
    (hb.subset (connectedComponentIn_mono y (compl_subset_compl.mpr hobs)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactExterior_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34CompactExterior_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactExterior_mono ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34CompactExterior_mono

def Section34CompactGraphFrame (V : Set (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (ε : ℝ)
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (src : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (f₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) : Prop :=
  section34CompactCutNeighborhood src ⊆ V ∧
  IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
    (f₁ '' section34CompactCutNeighborhood src) ∧
  f₁ '' section34CompactCutNeighborhood src ∈ nhdsSet (h '' section34CompactGraphSkeleton K) ∧
  (∀ x ∈ section34CompactCutNeighborhood src, _root_.Dist.dist (f₁ x) (h x) < ε / 3) ∧
  (∀ w : Section34CompactVertexIndex K K', h '' (w.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆
    interior (section34CompactVertexBallImage src f₁ w)) ∧
  (∀ (e : Section34CompactEdgeIndex K K') (s : Section34CompactSimplexIndex K 3),
    (section34CompactSplitDiskImage src f₁ e ∩
      h '' convexHull ℝ (s.1 : Set (EuclideanSpace ℝ (Fin 3)))).Nonempty →
      Section34Incident e.1 s.1) ∧
  (∀ (w : Section34CompactVertexIndex K K') (s : Section34CompactSimplexIndex K 3),
    (section34CompactVertexBallImage src f₁ w ∩
      h '' convexHull ℝ (s.1 : Set (EuclideanSpace ℝ (Fin 3)))).Nonempty →
      Section34Incident w.1 s.1) ∧
  (∀ s : Section34CompactSimplexIndex K 3, h '' section34CompactSimplexRim s.1 ⊆
    interior (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s)) ∧
  (∀ s : Section34CompactSimplexIndex K 3, ∃ S₁ S₂ : Set (EuclideanSpace ℝ (Fin 3)),
    IsTopologicalSolidTorus S₁ ∧ IsTopologicalSolidTorus S₂ ∧
    IsCombinatorialSolidTorus
      (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) ∧
    S₁ ⊆ interior (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) ∧
    section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s ⊆ interior S₂ ∧
    IsToroidalShell (closure (S₂ \ S₁)) (frontier S₁) (frontier S₂) ∧
    IsSpine S₁ (h '' section34CompactSimplexRim s.1)) ∧
  (∀ (w : Section34CompactVertexIndex K K') (t : Finset (EuclideanSpace ℝ (Fin 3))),
    t ∈ K.faces → (w.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin 3))) →
    h '' src (.vertexBall w) ∪ section34CompactVertexBallImage src f₁ w ⊆ interior (H t)) ∧
  Section34CompactExterior K K' h (section34CompactVertexBallImage src f₁)
    (fun s => h '' convexHull ℝ (s.1 : Set (EuclideanSpace ℝ (Fin 3))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGraphFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGraphFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGraphFrame ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGraphFrame

theorem Section34CompactGraphFrame.carriesFundamentalGroupOnto
    {V : Set (EuclideanSpace ℝ (Fin 3))}
    {h f₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {ε : ℝ}
    {src : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (s : Section34CompactSimplexIndex K 3) :
    CarriesFundamentalGroupOnto (h '' section34CompactSimplexRim s.1)
      (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) := by
  obtain ⟨-, -, -, -, -, -, -, hrim, hnest, -, -⟩ := hgraph
  obtain ⟨S₁, S₂, hS₁, hS₂, hT, h₁T, hT₂, hshell, hspine⟩ := hnest s
  have hsub := (hrim s).trans interior_subset
  exact carriesFundamentalGroupOnto_of_nestedSolidTorus hsub (Homeomorph.refl _)
    (fun _ => Iff.rfl) hS₁ hS₂ hT h₁T hT₂ hshell hspine hsub

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGraphFrame
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGraphFrame.carriesFundamentalGroupOnto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGraphFrame.carriesFundamentalGroupOnto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGraphFrame.carriesFundamentalGroupOnto ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGraphFrame.carriesFundamentalGroupOnto

end Vocabulary

section CurveCrossing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def HasPLSurfaceCurveCrossingAt (S A B : Set E) (x : E) : Prop :=
  ∃ (U V : Set E) (φ : E → E) (T P Q : Submodule ℝ E),
    IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ IsPLHomeomorphOn φ U V ∧ φ x = 0 ∧
      Module.finrank ℝ T = 2 ∧ Module.finrank ℝ P = 1 ∧ Module.finrank ℝ Q = 1 ∧
      P ≤ T ∧ Q ≤ T ∧ P ⊓ Q = ⊥ ∧ ∀ᶠ y in 𝓝 x,
        (y ∈ S ↔ φ y ∈ T) ∧ (y ∈ A ↔ φ y ∈ P) ∧ (y ∈ B ↔ φ y ∈ Q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.HasPLSurfaceCurveCrossingAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.HasPLSurfaceCurveCrossingAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.HasPLSurfaceCurveCrossingAt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.HasPLSurfaceCurveCrossingAt

end CurveCrossing

section FirstHomology

variable {Y : Type} [TopologicalSpace Y]

def CarriesIntegralFirstHomologyOnto (J T : Set Y) : Prop :=
  J ⊆ T ∧ ∀ hJT : J ⊆ T,
    Function.Surjective
      (integralSingularHomologyMap 1 (⟨inclusion hJT, continuous_inclusion hJT⟩ : C(J, T)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CarriesIntegralFirstHomologyOnto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CarriesIntegralFirstHomologyOnto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CarriesIntegralFirstHomologyOnto ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CarriesIntegralFirstHomologyOnto

theorem carriesIntegralFirstHomologyOnto_self (T : Set Y) :
    CarriesIntegralFirstHomologyOnto T T := by
  refine ⟨Subset.rfl, fun hJT => ?_⟩
  have hid : (⟨inclusion hJT, continuous_inclusion hJT⟩ : C(T, T)) = ContinuousMap.id T :=
    ContinuousMap.ext fun _ => rfl
  rw [hid, integralSingularHomologyMap_id]
  exact fun x => ⟨x, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.carriesIntegralFirstHomologyOnto_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.carriesIntegralFirstHomologyOnto_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.carriesIntegralFirstHomologyOnto_self ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.carriesIntegralFirstHomologyOnto_self

end FirstHomology

section Invariants

variable {K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}

def section34CompactTraceComponents
    (tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (s : Section34CompactSimplexIndex K 3) : Set (Set (EuclideanSpace ℝ (Fin 3))) :=
  (fun y => connectedComponentIn (fblBd s ∩ frontier (⋃ w, tgtV w)) y) ''
    (fblBd s ∩ frontier (⋃ w, tgtV w))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactTraceComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34CompactTraceComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactTraceComponents ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34CompactTraceComponents

noncomputable def section34CompactTraceCount
    (tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (s : Section34CompactSimplexIndex K 3) : ℕ :=
  (section34CompactTraceComponents tgtV fblBd s).ncard

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactTraceCount then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34CompactTraceCount"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactTraceCount ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34CompactTraceCount

noncomputable def section34CompactCrossingCount
    (tgtEBd : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (s : Section34CompactSimplexIndex K 3) : ℕ :=
  (fblBd s ∩ ⋃ e : Section34CompactEdgeIndex K K', tgtEBd e).ncard

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactCrossingCount then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34CompactCrossingCount"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactCrossingCount ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34CompactCrossingCount

noncomputable def section34CompactFaceBallRank
    (tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtEBd : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (s : Section34CompactSimplexIndex K 3) : ℕ :=
  section34CompactTraceCount tgtV fblBd s + section34CompactCrossingCount tgtEBd fblBd s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactFaceBallRank then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34CompactFaceBallRank"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactFaceBallRank ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34CompactFaceBallRank

theorem section34CompactFaceBallRank_congr
    {tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {tgtEBd : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {fblBd fblBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    {s : Section34CompactSimplexIndex K 3} (hs : fblBd s = fblBd' s) :
    section34CompactFaceBallRank tgtV tgtEBd fblBd s =
      section34CompactFaceBallRank tgtV tgtEBd fblBd' s := by
  simp only [section34CompactFaceBallRank, section34CompactTraceCount,
    section34CompactCrossingCount, section34CompactTraceComponents, hs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactFaceBallRank_congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34CompactFaceBallRank_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactFaceBallRank_congr ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34CompactFaceBallRank_congr

theorem section34CompactFaceBallRank_lt_of_compression
    {tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {tgtEBd : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {fblBd fblBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    {s : Section34CompactSimplexIndex K 3}
    (hc : section34CompactTraceCount tgtV fblBd' s + 1 ≤ section34CompactTraceCount tgtV fblBd s)
    (hp : section34CompactCrossingCount tgtEBd fblBd' s ≤
      section34CompactCrossingCount tgtEBd fblBd s) :
    section34CompactFaceBallRank tgtV tgtEBd fblBd' s <
      section34CompactFaceBallRank tgtV tgtEBd fblBd s := by
  simp only [section34CompactFaceBallRank]
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactFaceBallRank_lt_of_compression then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34CompactFaceBallRank_lt_of_compression"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactFaceBallRank_lt_of_compression ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34CompactFaceBallRank_lt_of_compression

theorem section34CompactFaceBallRank_lt_of_bigonSlide
    {tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {tgtEBd : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
    {fblBd fblBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    {s : Section34CompactSimplexIndex K 3}
    (hc : section34CompactTraceCount tgtV fblBd' s = section34CompactTraceCount tgtV fblBd s)
    (hp : section34CompactCrossingCount tgtEBd fblBd' s + 2 =
      section34CompactCrossingCount tgtEBd fblBd s) :
    section34CompactFaceBallRank tgtV tgtEBd fblBd' s <
      section34CompactFaceBallRank tgtV tgtEBd fblBd s := by
  simp only [section34CompactFaceBallRank]
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactFaceBallRank_lt_of_bigonSlide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34CompactFaceBallRank_lt_of_bigonSlide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34CompactFaceBallRank_lt_of_bigonSlide ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34CompactFaceBallRank_lt_of_bigonSlide

def Section34CompactFaceBallInvariants
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtEBd : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (fbl fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  (∀ s, IsPLCellOn 3 (fbl s) (fblBd s)) ∧
  (∀ s : Section34CompactSimplexIndex K 3,
    h '' section34CompactSimplexRim s.1 ⊆ interior (fbl s)) ∧
  (∀ (s : Section34CompactSimplexIndex K 3) (w : Section34CompactVertexIndex K K'),
    ¬ Section34Incident w.1 s.1 → fbl s ∩ tgtV w = ∅) ∧
  (∀ s s', s ≠ s' → fbl s ∩ fbl s' ⊆ interior (⋃ w, tgtV w)) ∧
  (∀ s, ∀ y ∈ fblBd s ∩ frontier (⋃ w, tgtV w),
    HasPLCrossingAt (fblBd s) (frontier (⋃ w, tgtV w)) y) ∧
  (∀ (s : Section34CompactSimplexIndex K 3) (e : Section34CompactEdgeIndex K K'),
    ∀ y ∈ fblBd s ∩ tgtEBd e,
      HasPLSurfaceCurveCrossingAt (frontier (⋃ w, tgtV w))
        (fblBd s ∩ frontier (⋃ w, tgtV w)) (tgtEBd e) y) ∧
  (∀ s, CarriesIntegralFirstHomologyOnto
    (fblBd s ∩ frontier (section34CompactFaceTorus tgtV s)) (section34CompactFaceTorus tgtV s)) ∧
  (∀ s, (fblBd s ∩ ⋃ e : Section34CompactEdgeIndex K K', tgtEBd e).Finite) ∧
  (∀ s, (section34CompactTraceComponents tgtV fblBd s).Finite) ∧
  (∀ (s : Section34CompactSimplexIndex K 3) (t : Section34CompactSimplexIndex K 4),
    Section34Incident s.1 t.1 → fbl s ⊆ interior (H t.1)) ∧
  Section34CompactExterior K K' h tgtV fbl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceBallInvariants then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceBallInvariants"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceBallInvariants ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceBallInvariants

def Section34CompactFaceEnvelopes
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (env : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  (∀ s, IsOpen (env s)) ∧
  (∀ s : Section34CompactSimplexIndex K 3,
    h '' convexHull ℝ (s.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ env s) ∧
  (∀ (s : Section34CompactSimplexIndex K 3) (w : Section34CompactVertexIndex K K'),
    ¬ Section34Incident w.1 s.1 → env s ∩ tgtV w = ∅) ∧
  (∀ s s', s ≠ s' → env s ∩ env s' ⊆ interior (⋃ w, tgtV w)) ∧
  (∀ (s : Section34CompactSimplexIndex K 3) (t : Section34CompactSimplexIndex K 4),
    Section34Incident s.1 t.1 → env s ⊆ interior (H t.1)) ∧
  (∀ s : Section34CompactSimplexIndex K 3, ∃ A : Set (EuclideanSpace ℝ (Fin 3)),
    IsPLBall 3 A ∧ h '' section34CompactSimplexRim s.1 ⊆ interior A ∧
      env s ∩ A ⊆ interior (section34CompactFaceTorus tgtV s)) ∧
  Section34CompactExterior K K' h tgtV (fun s => closure (env s))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceEnvelopes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceEnvelopes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceEnvelopes ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceEnvelopes

def Section34CompactCompression
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (tgtVBd : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtE : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (fbl fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (s : Section34CompactSimplexIndex K 3) : Prop :=
  ∃ (w : Section34CompactVertexIndex K K') (Dj Jd : Set (EuclideanSpace ℝ (Fin 3))),
    IsPLCellOn 2 Dj Jd ∧ Dj ⊆ tgtVBd w ∧ Jd ⊆ fblBd s ∧ Dj ∩ fblBd s = Jd ∧
      (∀ e : Section34CompactEdgeIndex K K', Disjoint Dj (tgtE e)) ∧
      ∀ s' : Section34CompactSimplexIndex K 3, s' ≠ s → Disjoint (Dj \ Jd) (fbl s')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCompression then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCompression"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCompression ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCompression

def Section34CompactBigonSlide
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (tgtV tgtVBd : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtE tgtEBd : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (s : Section34CompactSimplexIndex K 3) : Prop :=
  ∃ (w : Section34CompactVertexIndex K K') (e : Section34CompactEdgeIndex K K')
    (B B' Bb Dj Jd : Set (EuclideanSpace ℝ (Fin 3))),
    IsPLCellOn 1 B Bb ∧ B ⊆ fblBd s ∧ B ⊆ tgtVBd w ∧ Bb ⊆ tgtEBd e ∧
      B ∩ (⋃ e' : Section34CompactEdgeIndex K K', tgtE e') = Bb ∧
      IsPLCellOn 1 B' Bb ∧ B' ⊆ tgtEBd e ∧ B ∩ B' = Bb ∧
      IsPLCellOn 2 Dj Jd ∧ Dj ⊆ tgtVBd w ∩ frontier (⋃ w, tgtV w) ∧ Jd = B ∪ B' ∧
      ∀ s' : Section34CompactSimplexIndex K 3, Disjoint (Dj \ Jd) (fblBd s')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactBigonSlide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactBigonSlide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactBigonSlide ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactBigonSlide

def Section34CompactTrace
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtEBd : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∃ (r : Section34CompactSimplexIndex K 3 → ℕ)
    (J : Section34CompactSimplexIndex K 3 → ℕ → Set (EuclideanSpace ℝ (Fin 3))),
    (∀ s, 0 < r s) ∧
    (∀ s, ∀ i < r s, IsPLSphere 1 (J s i)) ∧
    (∀ s, ∀ i < r s, ∀ j < r s, i ≠ j → Disjoint (J s i) (J s j)) ∧
    (∀ s, fblBd s ∩ frontier (⋃ w : Section34CompactVertexIndex K K', tgtV w) =
      ⋃ i < r s, J s i) ∧
    (∀ s, fblBd s ∩ frontier (section34CompactFaceTorus tgtV s) = ⋃ i < r s, J s i) ∧
    (∀ s, ∀ i < r s, ∀ e : Section34CompactEdgeIndex K K', Section34Incident e.1 s.1 →
      ∃ p, J s i ∩ tgtEBd e = {p}) ∧
    ∀ s, ∀ i < r s, ∀ hsub : J s i ⊆ section34CompactFaceTorus tgtV s,
      integralSingularHomologyMap 1
        (⟨inclusion hsub, continuous_inclusion hsub⟩ :
          C(J s i, section34CompactFaceTorus tgtV s)) ≠ 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTrace ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTrace

def Section34CompactFaceDiskFamily
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (tgtV : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtE tgtEBd : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtD tgtDBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtA tgtABd : Section34CompactArcIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtP : Section34CompactMarkIndex K K' → Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  (∀ s, IsPLCellOn 2 (tgtD s) (tgtDBd s)) ∧
  (∀ s, tgtD s ⊆ fblBd s) ∧
  (∀ s, tgtD s ∩ (⋃ w : Section34CompactVertexIndex K K', tgtV w) = tgtDBd s) ∧
  (∀ s, tgtDBd s ⊆ frontier (⋃ w : Section34CompactVertexIndex K K', tgtV w)) ∧
  (∀ s s', s ≠ s' → Disjoint (tgtD s) (tgtD s')) ∧
  (∀ a, IsPLCellOn 1 (tgtA a) (tgtABd a)) ∧
  (∀ a : Section34CompactArcIndex K K', tgtDBd a.1.1 ∩ tgtV a.1.2 = tgtA a) ∧
  (∀ (s : Section34CompactSimplexIndex K 3) (w : Section34CompactVertexIndex K K'),
    ¬ Section34Incident w.1 s.1 → tgtD s ∩ tgtV w = ∅) ∧
  (∀ p, IsPLCellOn 0 (tgtP p) ∅) ∧
  (∀ p : Section34CompactMarkIndex K K', tgtDBd p.1.1 ∩ tgtEBd p.1.2 = tgtP p) ∧
  (∀ (s : Section34CompactSimplexIndex K 3) (e : Section34CompactEdgeIndex K K'),
    ¬ Section34Incident e.1 s.1 → tgtDBd s ∩ tgtEBd e = ∅) ∧
  ∀ a : Section34CompactArcIndex K K',
    tgtABd a = tgtA a ∩ ⋃ e : Section34CompactEdgeIndex K K', tgtE e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceDiskFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceDiskFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceDiskFamily ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceDiskFamily

def Section34CompactResidualPlus
    (K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtV tgtVBd : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtE tgtEBd : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtD : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtA : Section34CompactArcIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtP : Section34CompactMarkIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtR tgtRBd : Section34CompactSimplexIndex K 4 → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtX tgtXBd : Section34CompactPatchIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtI tgtIBd : Section34CompactEdgeArcIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtO tgtOBd : Section34CompactOuterVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3)))
    (tgtQ tgtQBd : Section34CompactOuterEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3))) :
    Prop :=
  (∀ t, IsPLCellOn 3 (tgtR t) (tgtRBd t)) ∧
  (∀ x, IsPLCellOn 2 (tgtX x) (tgtXBd x)) ∧
  (∀ i, IsPLCellOn 1 (tgtI i) (tgtIBd i)) ∧
  (∀ o, IsPLCellOn 2 (tgtO o) (tgtOBd o)) ∧
  (∀ q, IsPLCellOn 1 (tgtQ q) (tgtQBd q)) ∧
  (∀ x : Section34CompactPatchIndex K K', tgtR x.1.1 ∩ tgtV x.1.2 = tgtX x) ∧
  (∀ (t : Section34CompactSimplexIndex K 4) (w : Section34CompactVertexIndex K K'),
    ¬ Section34Incident w.1 t.1 → tgtR t ∩ tgtV w = ∅) ∧
  (∀ (t : Section34CompactSimplexIndex K 4) (s : Section34CompactSimplexIndex K 3),
    Section34Incident s.1 t.1 → tgtR t ∩ tgtD s = tgtD s) ∧
  (∀ (t : Section34CompactSimplexIndex K 4) (s : Section34CompactSimplexIndex K 3),
    ¬ Section34Incident s.1 t.1 → tgtR t ∩ tgtD s = ∅) ∧
  (∀ t t', t ≠ t' → tgtR t ∩ tgtR t' ⊆ ⋃ s, tgtD s) ∧
  (∀ i : Section34CompactEdgeArcIndex K K', tgtR i.1.1 ∩ tgtE i.1.2 = tgtI i) ∧
  (∀ (t : Section34CompactSimplexIndex K 4) (e : Section34CompactEdgeIndex K K'),
    ¬ Section34Incident e.1 t.1 → tgtR t ∩ tgtE e = ∅) ∧
  (∀ i : Section34CompactEdgeArcIndex K K', tgtI i ⊆ tgtEBd i.1.2) ∧
  (∀ t : Section34CompactSimplexIndex K 4, tgtRBd t =
    (⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1), tgtD s) ∪
      ⋃ (x : Section34CompactPatchIndex K K') (_ : x.1.1 = t), tgtX x) ∧
  (∀ i : Section34CompactEdgeArcIndex K K', tgtIBd i =
    ⋃ (p : Section34CompactMarkIndex K K')
      (_ : p.1.2 = i.1.2 ∧ Section34Incident p.1.1.1 i.1.1.1), tgtP p) ∧
  (∀ x : Section34CompactPatchIndex K K', tgtXBd x =
    (⋃ (a : Section34CompactArcIndex K K')
      (_ : a.1.2 = x.1.2 ∧ Section34Incident a.1.1.1 x.1.1.1), tgtA a) ∪
    ⋃ (i : Section34CompactEdgeArcIndex K K')
      (_ : i.1.1 = x.1.1 ∧ x.1.2.1 ⊆ i.1.2.1), tgtI i) ∧
  (∀ (i : Section34CompactEdgeArcIndex K K') (p : Section34CompactMarkIndex K K'),
    p.1.2 = i.1.2 → tgtP p ⊆ tgtI i → tgtP p ⊆ tgtIBd i) ∧
  (∀ t : Section34CompactSimplexIndex K 4, tgtR t ⊆ H t.1) ∧
  (∀ o : Section34CompactOuterVertexIndex K K', tgtO o =
    closure (tgtVBd o.1 \ ((⋃ e, tgtE e) ∪ ⋃ x, tgtX x))) ∧
  (∀ q : Section34CompactOuterEdgeIndex K K', tgtQ q = closure (tgtEBd q.1 \ ⋃ i, tgtI i)) ∧
  (∀ w : Section34CompactVertexIndex K K', tgtVBd w =
    (⋃ (e : Section34CompactEdgeIndex K K') (_ : w.1 ⊆ e.1), tgtE e) ∪
    (⋃ (x : Section34CompactPatchIndex K K') (_ : x.1.2 = w), tgtX x) ∪
    ⋃ (o : Section34CompactOuterVertexIndex K K') (_ : o.1 = w), tgtO o) ∧
  (∀ e : Section34CompactEdgeIndex K K', tgtEBd e =
    (⋃ (i : Section34CompactEdgeArcIndex K K') (_ : i.1.2 = e), tgtI i) ∪
    ⋃ (q : Section34CompactOuterEdgeIndex K K') (_ : q.1 = e), tgtQ q) ∧
  (∀ o : Section34CompactOuterVertexIndex K K', tgtOBd o =
    (⋃ (a : Section34CompactArcIndex K K')
      (_ : a.1.2 = o.1 ∧
        convexHull ℝ (a.1.1.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ frontier K.space), tgtA a) ∪
    ⋃ (q : Section34CompactOuterEdgeIndex K K') (_ : o.1.1 ⊆ q.1.1), tgtQ q) ∧
  ∀ q : Section34CompactOuterEdgeIndex K K', tgtQBd q =
    ⋃ (p : Section34CompactMarkIndex K K')
      (_ : p.1.2 = q.1 ∧
        convexHull ℝ (p.1.1.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ frontier K.space), tgtP p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualPlus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualPlus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualPlus ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualPlus

end Invariants

section Model

theorem IsPLCellOn.isPolyhedron {d : ℕ} {S B : Set (EuclideanSpace ℝ (Fin 3))}
    (hS : IsPLCellOn d S B) : IsPolyhedron S := by
  obtain ⟨P, r, u, hr, hu, rfl, -⟩ := hS
  exact (isPLOn_iff_isPiecewiseAffineOn.mp hu.isPLOn).isPolyhedron_image
    (IsPLBall.isPolyhedron ⟨r, hr⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isPolyhedron then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isPolyhedron"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isPolyhedron ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isPolyhedron

theorem isPLHomeomorphInto_of_isPLHomeomorphOn_of_subset
    {f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {N P : Set (EuclideanSpace ℝ (Fin 3))} (hf : IsPLHomeomorphOn f N (f '' N))
    (hP : IsPolyhedron P) (hPN : P ⊆ N) : IsPLHomeomorphInto 3 f P := by
  have hpl : IsPiecewiseAffineOn f P := hf.isPiecewiseAffineOn.mono_of_isPolyhedron hP hPN
  have hinj : _root_.Set.InjOn f P := hf.bijOn.injOn.mono hPN
  have hfP : IsPLHomeomorphOn f P (f '' P) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP hpl hinj.bijOn_image
  have hinv : IsPLOn 3 3 (Function.invFunOn f P) (f '' P) :=
    isPLOn_iff_isPiecewiseAffineOn.mpr hfP.isPiecewiseAffineOn_invFunOn
  exact ⟨isPLOn_iff_isPiecewiseAffineOn.mpr hpl, hinj,
    fun y hy => ⟨Function.invFunOn f P, hinv y hy, hinj.leftInvOn_invFunOn⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphInto_of_isPLHomeomorphOn_of_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphInto_of_isPLHomeomorphOn_of_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphInto_of_isPLHomeomorphOn_of_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphInto_of_isPLHomeomorphOn_of_subset

theorem exists_isPLBall_subset_interior_dist_lt {C : Set (EuclideanSpace ℝ (Fin 3))}
    (hC : IsPLBall 3 C) {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hh : ContinuousOn h C) {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn p C (p '' C) ∧ p '' C ⊆ interior C ∧
        ∀ x ∈ C, _root_.Dist.dist (h (p x)) (h x) < δ := by
  classical
  obtain ⟨K, hKfin, hKC⟩ := hC.isPolyhedron.exists_simplicialComplex
  subst hKC
  have _ : Finite K.faces := hKfin.to_subtype
  have hKman : IsCombinatorialManifoldWithBoundary 3 K :=
    IsPLBall.isCombinatorialManifoldWithBoundary (n := 2) hC
  obtain ⟨f, -, hfpl, hfinj, hfmap, hfB, -, -, -, hdist⟩ :=
    IsCombinatorialManifoldWithBoundary.exists_piecewiseAffineOn_inward_dist_lt K hKman hh
      (continuousOn_const (c := δ)) (fun _ _ => hδ)
  have hfr := frontier_space_eq_boundaryComplex_space (n := 2) hKman
  refine ⟨f, isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hC.isPolyhedron hfpl
    hfinj.bijOn_image, ?_, hdist⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [← self_sdiff_frontier, hfr]
  exact ⟨hfmap hx, hfB x hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLBall_subset_interior_dist_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLBall_subset_interior_dist_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLBall_subset_interior_dist_lt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLBall_subset_interior_dist_lt

theorem isEmbedding_domRestrict_interior_of_continuousOn_injOn
    {C : Set (EuclideanSpace ℝ (Fin 3))} (hC : IsCompact C)
    {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} (hcont : ContinuousOn h C)
    (hinj : _root_.Set.InjOn h C) : Topology.IsEmbedding ((interior C).domRestrict h) := by
  have hCemb : Topology.IsEmbedding (C.domRestrict h) := by
    let _ : CompactSpace C := isCompact_iff_compactSpace.mp hC
    exact (hcont.domRestrict.isClosedEmbedding (Set.injOn_iff_injective.mp hinj)).isEmbedding
  simpa only [Set.domRestrict_eq, Function.comp_def] using
    hCemb.comp (Topology.IsEmbedding.inclusion (interior_subset : interior C ⊆ C))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isEmbedding_domRestrict_interior_of_continuousOn_injOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isEmbedding_domRestrict_interior_of_continuousOn_injOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isEmbedding_domRestrict_interior_of_continuousOn_injOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isEmbedding_domRestrict_interior_of_continuousOn_injOn

end Model

end DifferentialGeometry.Topology.PiecewiseLinear
