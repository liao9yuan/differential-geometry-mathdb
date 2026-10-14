import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandard

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

universe u

def poincareStandardSumClosed : Prop :=
  ∀ L : List (ConnectedClosedOrientedManifold.{u} 3),
    (∀ F ∈ L, isPoincareStandard F.Carrier) → isPoincareStandard (finiteConnectedSum L).Carrier

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.poincareStandardSumClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.poincareStandardSumClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.poincareStandardSumClosed ``Submission.DifferentialGeometry.Topology.poincareStandardSumClosed

def isSphereTwoTimesCircleFactor (F : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∃ f : F.Carrier ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯ SphereTwoTimesCircle,
    f.preservesOrientation F.orientation sphereTwoTimesCircleOrientation

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor ``Submission.DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor

theorem isStandardFactor_of_isSphereTwoTimesCircleFactor
    {F : ConnectedClosedOrientedManifold.{u} 3} (h : isSphereTwoTimesCircleFactor F) :
    isStandardFactor F :=
  Or.inr h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isStandardFactor_of_isSphereTwoTimesCircleFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isStandardFactor_of_isSphereTwoTimesCircleFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isStandardFactor_of_isSphereTwoTimesCircleFactor ``Submission.DifferentialGeometry.Topology.isStandardFactor_of_isSphereTwoTimesCircleFactor

theorem isSphereTwoTimesCircleFactor_of_orientedDiffeomorph
    {F F' : ConnectedClosedOrientedManifold.{u} 3}
    (h : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      F'.toClosedOrientedManifold F.toClosedOrientedManifold))
    (hF : isSphereTwoTimesCircleFactor F) : isSphereTwoTimesCircleFactor F' := by
  obtain ⟨g⟩ := h
  obtain ⟨f, hf⟩ := hF
  exact ⟨g.1.trans f, Diffeomorph.preservesOrientation_trans g.2 hf⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor_of_orientedDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor_of_orientedDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor_of_orientedDiffeomorph ``Submission.DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor_of_orientedDiffeomorph

theorem isSphereTwoTimesCircleFactor_iff_of_orientedDiffeomorph
    {F F' : ConnectedClosedOrientedManifold.{u} 3}
    (h : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      F'.toClosedOrientedManifold F.toClosedOrientedManifold)) :
    isSphereTwoTimesCircleFactor F ↔ isSphereTwoTimesCircleFactor F' :=
  ⟨isSphereTwoTimesCircleFactor_of_orientedDiffeomorph h,
    isSphereTwoTimesCircleFactor_of_orientedDiffeomorph
      (h.map ClosedOrientedManifold.OrientedDiffeomorph.symm)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor_iff_of_orientedDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor_iff_of_orientedDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor_iff_of_orientedDiffeomorph ``Submission.DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor_iff_of_orientedDiffeomorph

namespace ClosedOrientedManifold

variable (M : ClosedOrientedManifold.{u} 3) [ConnectedSpace M.Carrier]

theorem isPoincareStandard_of_component (C : ConnectedComponents M.Carrier)
    (h : isPoincareStandard (M.component C).Carrier) : isPoincareStandard M.Carrier :=
  isPoincareStandard_of_diffeomorph (componentDiffeomorph M C) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.isPoincareStandard_of_component then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.isPoincareStandard_of_component"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.isPoincareStandard_of_component ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.isPoincareStandard_of_component

end ClosedOrientedManifold

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

def cutIndices (C : ConnectedComponents M.Carrier) : Finset E.tubes.Index := by
  classical
  exact Finset.univ.filter fun a =>
    ∀ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Set.Icc (-2 : ℝ) 2,
      (E.tubes.tube a) z ∈ ClosedOrientedManifold.componentSet M C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cutIndices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cutIndices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cutIndices ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cutIndices

local instance instLocallyConnectedQ : LocallyConnectedSpace Q.Carrier :=
  ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.instLocallyConnectedQ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.instLocallyConnectedQ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.instLocallyConnectedQ ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.instLocallyConnectedQ

local instance instLocallyConnectedDiscarded : LocallyConnectedSpace E.discarded.Carrier :=
  ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.instLocallyConnectedDiscarded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.instLocallyConnectedDiscarded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.instLocallyConnectedDiscarded ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.instLocallyConnectedDiscarded

local instance instLocallyConnectedCapped : LocallyConnectedSpace E.capped.Carrier :=
  ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.instLocallyConnectedCapped then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.instLocallyConnectedCapped"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.instLocallyConnectedCapped ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.instLocallyConnectedCapped

def outgoingFactor : (Q.Carrier ⊕ E.discarded.Carrier) →
    ConnectedClosedOrientedManifold.{u} 3
  | Sum.inl q => Q.component (ConnectedComponents.mk q)
  | Sum.inr d => E.discarded.component (ConnectedComponents.mk d)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.outgoingFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.outgoingFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.outgoingFactor ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.outgoingFactor

def associatedFactor (x : E.tubes.core) : ConnectedClosedOrientedManifold.{u} 3 :=
  E.outgoingFactor (E.presentation (E.capping.coreInclusion x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor

theorem associatedFactor_eq_of_presentation_eq_inl (x : E.tubes.core) (q : Q.Carrier)
    (h : E.presentation (E.capping.coreInclusion x) = Sum.inl q) :
    E.associatedFactor x = Q.component (ConnectedComponents.mk q) := by
  rw [associatedFactor, h]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor_eq_of_presentation_eq_inl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor_eq_of_presentation_eq_inl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor_eq_of_presentation_eq_inl ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor_eq_of_presentation_eq_inl

theorem associatedFactor_eq_of_presentation_eq_inr (x : E.tubes.core) (d : E.discarded.Carrier)
    (h : E.presentation (E.capping.coreInclusion x) = Sum.inr d) :
    E.associatedFactor x = E.discarded.component (ConnectedComponents.mk d) := by
  rw [associatedFactor, h]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor_eq_of_presentation_eq_inr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor_eq_of_presentation_eq_inr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor_eq_of_presentation_eq_inr ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor_eq_of_presentation_eq_inr

theorem associatedFactor_eq_of_mk_coreInclusion_eq (x x' : E.tubes.core)
    (h : ConnectedComponents.mk (E.capping.coreInclusion x) =
      ConnectedComponents.mk (E.capping.coreInclusion x')) :
    E.associatedFactor x = E.associatedFactor x' := by
  have hpres : ConnectedComponents.mk (E.presentation (E.capping.coreInclusion x)) =
      ConnectedComponents.mk (E.presentation (E.capping.coreInclusion x')) := by
    simpa only [Continuous.connectedComponentsMap_mk] using
      congrArg E.presentation.continuous.connectedComponentsMap h
  rcases hx : E.presentation (E.capping.coreInclusion x) with q | d
  · rcases hx' : E.presentation (E.capping.coreInclusion x') with q' | d'
    · rw [E.associatedFactor_eq_of_presentation_eq_inl x q hx,
        E.associatedFactor_eq_of_presentation_eq_inl x' q' hx']
      refine congrArg Q.component ?_
      have hsum : ConnectedComponents.mk (Sum.inl q : Q.Carrier ⊕ E.discarded.Carrier) =
          ConnectedComponents.mk (Sum.inl q') := by rw [← hx, ← hx']; exact hpres
      let retr : Q.Carrier ⊕ E.discarded.Carrier → Q.Carrier := Sum.elim id fun _ => q
      have hcont : Continuous retr := continuous_sum_dom.2 ⟨continuous_id, continuous_const⟩
      simpa [retr] using congrArg hcont.connectedComponentsMap hsum
    · exfalso
      have hsum : ConnectedComponents.mk (Sum.inl q : Q.Carrier ⊕ E.discarded.Carrier) =
          ConnectedComponents.mk (Sum.inr d') := by rw [← hx, ← hx']; exact hpres
      have hmem : (Sum.inr d' : Q.Carrier ⊕ E.discarded.Carrier) ∈
          connectedComponent (Sum.inl q) := ConnectedComponents.coe_eq_coe'.mp hsum.symm
      have hsub := isPreconnected_connectedComponent.subset_isClopen
        (isClopen_range_inl (X := Q.Carrier) (Y := E.discarded.Carrier))
        ⟨Sum.inl q, mem_connectedComponent, ⟨q, rfl⟩⟩
      obtain ⟨y, hy⟩ := hsub hmem
      exact Sum.inl_ne_inr hy
  · rcases hx' : E.presentation (E.capping.coreInclusion x') with q' | d'
    · exfalso
      have hsum : ConnectedComponents.mk (Sum.inr d : Q.Carrier ⊕ E.discarded.Carrier) =
          ConnectedComponents.mk (Sum.inl q') := by rw [← hx, ← hx']; exact hpres
      have hmem : (Sum.inl q' : Q.Carrier ⊕ E.discarded.Carrier) ∈
          connectedComponent (Sum.inr d) := ConnectedComponents.coe_eq_coe'.mp hsum.symm
      have hsub := isPreconnected_connectedComponent.subset_isClopen
        (isClopen_range_inr (X := Q.Carrier) (Y := E.discarded.Carrier))
        ⟨Sum.inr d, mem_connectedComponent, ⟨d, rfl⟩⟩
      obtain ⟨y, hy⟩ := hsub hmem
      exact Sum.inr_ne_inl hy
    · rw [E.associatedFactor_eq_of_presentation_eq_inr x d hx,
        E.associatedFactor_eq_of_presentation_eq_inr x' d' hx']
      refine congrArg E.discarded.component ?_
      have hsum : ConnectedComponents.mk (Sum.inr d : Q.Carrier ⊕ E.discarded.Carrier) =
          ConnectedComponents.mk (Sum.inr d') := by rw [← hx, ← hx']; exact hpres
      let retr : Q.Carrier ⊕ E.discarded.Carrier → E.discarded.Carrier :=
        Sum.elim (fun _ => d) id
      have hcont : Continuous retr := continuous_sum_dom.2 ⟨continuous_const, continuous_id⟩
      simpa [retr] using congrArg hcont.connectedComponentsMap hsum

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor_eq_of_mk_coreInclusion_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor_eq_of_mk_coreInclusion_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor_eq_of_mk_coreInclusion_eq ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactor_eq_of_mk_coreInclusion_eq

def associatedFactors (C : ConnectedComponents M.Carrier) :
    Set (ConnectedClosedOrientedManifold.{u} 3) :=
  {N | ∃ x : E.tubes.core, ConnectedComponents.mk x.1 = C ∧ E.associatedFactor x = N}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactors then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactors"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactors ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactors

def cappedCutComponents (C : ConnectedComponents M.Carrier) :
    Set (ConnectedComponents E.capped.Carrier) :=
  {D | ∃ x : E.tubes.core, ConnectedComponents.mk x.1 = C ∧
    ConnectedComponents.mk (E.capping.coreInclusion x) = D}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cappedCutComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cappedCutComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cappedCutComponents ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cappedCutComponents

noncomputable def cappedFactor (C : ConnectedComponents M.Carrier)
    (D : E.cappedCutComponents C) : ConnectedClosedOrientedManifold.{u} 3 :=
  E.associatedFactor (Classical.choose D.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cappedFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cappedFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cappedFactor ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cappedFactor

theorem cappedFactor_eq_of_mem (C : ConnectedComponents M.Carrier)
    (D : E.cappedCutComponents C) (x : E.tubes.core)
    (h : ConnectedComponents.mk (E.capping.coreInclusion x) = D.1) :
    E.cappedFactor C D = E.associatedFactor x :=
  E.associatedFactor_eq_of_mk_coreInclusion_eq (Classical.choose D.2) x
    ((Classical.choose_spec D.2).2.trans h.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.cappedFactor_eq_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.cappedFactor_eq_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.cappedFactor_eq_of_mem ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.cappedFactor_eq_of_mem

theorem associatedFactors_eq_range_cappedFactor (C : ConnectedComponents M.Carrier) :
    E.associatedFactors C = Set.range (E.cappedFactor C) := by
  ext N
  constructor
  · rintro ⟨x, hxC, rfl⟩
    exact ⟨⟨ConnectedComponents.mk (E.capping.coreInclusion x), x, hxC, rfl⟩,
      (E.cappedFactor_eq_of_mem C _ x rfl).trans rfl⟩
  · rintro ⟨D, rfl⟩
    exact ⟨Classical.choose D.2, (Classical.choose_spec D.2).1, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactors_eq_range_cappedFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactors_eq_range_cappedFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactors_eq_range_cappedFactor ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactors_eq_range_cappedFactor

def CompleteEnumeration (C : ConnectedComponents M.Carrier)
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) : Prop :=
  L.Nodup ∧ (∀ F ∈ L, F ∈ E.associatedFactors C) ∧
    (∀ F ∈ E.associatedFactors C, F ∈ L)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.CompleteEnumeration then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.CompleteEnumeration"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.CompleteEnumeration ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.CompleteEnumeration

def localReconstruction : Prop :=
  ∀ (C : ConnectedComponents M.Carrier)
    (L : List (ConnectedClosedOrientedManifold.{u} 3)),
    E.CompleteEnumeration C L →
      ∃ (b : ℕ) (K : List (ConnectedClosedOrientedManifold.{u} 3)),
        K.length = b ∧
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        b + L.length = (E.cutIndices C).card + 1 ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (L ++ K)).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.localReconstruction

theorem associatedFactors_finite (C : ConnectedComponents M.Carrier) :
    (E.associatedFactors C).Finite := by
  classical
  refine (Set.finite_range fun s : ConnectedComponents Q.Carrier ⊕
      ConnectedComponents E.discarded.Carrier =>
      match s with
      | Sum.inl c => Q.component c
      | Sum.inr c => E.discarded.component c).subset ?_
  rintro N ⟨x, -, rfl⟩
  cases h : E.presentation (E.capping.coreInclusion x) with
  | inl q => exact ⟨Sum.inl (ConnectedComponents.mk q), by
      rw [associatedFactor, h]; rfl⟩
  | inr d => exact ⟨Sum.inr (ConnectedComponents.mk d), by
      rw [associatedFactor, h]; rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactors_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactors_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactors_finite ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.associatedFactors_finite

theorem exists_completeEnumeration (C : ConnectedComponents M.Carrier) :
    ∃ L : List (ConnectedClosedOrientedManifold.{u} 3), E.CompleteEnumeration C L := by
  classical
  obtain ⟨s, hs⟩ := (E.associatedFactors_finite C).exists_finset
  exact ⟨s.toList, s.nodup_toList, fun F hF => (hs F).mp (Finset.mem_toList.mp hF),
    fun F hF => Finset.mem_toList.mpr ((hs F).mpr hF)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_completeEnumeration then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.exists_completeEnumeration"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_completeEnumeration ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.exists_completeEnumeration

theorem componentwise_isPoincareStandard (h : E.localReconstruction)
    (hctrl : E.poincareControlled)
    (hnext : ∀ C : ConnectedComponents Q.Carrier, isPoincareStandard (Q.component C).Carrier)
    (hsum : poincareStandardSumClosed.{u}) :
    ∀ C : ConnectedComponents M.Carrier, isPoincareStandard (M.component C).Carrier := by
  intro C
  obtain ⟨L, hL⟩ := E.exists_completeEnumeration C
  obtain ⟨b, K, hKlen, hKfac, -, ⟨ρ⟩⟩ := h C L hL
  refine isPoincareStandard_of_diffeomorph ρ.1 (hsum (L ++ K) ?_)
  intro F hF
  rcases List.mem_append.mp hF with hF | hF
  · obtain ⟨x, -, rfl⟩ := hL.2.1 F hF
    rcases hx : E.presentation (E.capping.coreInclusion x) with q | d
    · rw [E.associatedFactor_eq_of_presentation_eq_inl x q hx]
      exact hnext (ConnectedComponents.mk q)
    · rw [E.associatedFactor_eq_of_presentation_eq_inr x d hx]
      exact hctrl (ConnectedComponents.mk d)
  · exact isPoincareStandard_of_standard_factor F
      (isStandardFactor_of_isSphereTwoTimesCircleFactor (hKfac F hF))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentwise_isPoincareStandard then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentwise_isPoincareStandard"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentwise_isPoincareStandard ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentwise_isPoincareStandard

end SphericalCutCapTransition

namespace FiniteCutCapTrace

variable (T : FiniteCutCapTrace.{u})

theorem componentwise_isPoincareStandard
    (h : ∀ i : Fin T.eventCount, (T.transition i).localReconstruction)
    (hctrl : T.poincareControlled) (hext : T.extinct) (hsum : poincareStandardSumClosed.{u}) :
    ∀ i : Fin (T.eventCount + 1), ∀ C : ConnectedComponents (T.stage i).Carrier,
      isPoincareStandard ((T.stage i).component C).Carrier := by
  have hbase : ∀ C : ConnectedComponents (T.stage (Fin.last T.eventCount)).Carrier,
      isPoincareStandard ((T.stage (Fin.last T.eventCount)).component C).Carrier := by
    have hEmpty : IsEmpty (ConnectedComponents (T.stage (Fin.last T.eventCount)).Carrier) :=
      ConnectedComponents.isEmpty_iff_isEmpty.mpr hext
    intro C
    exact hEmpty.elim C
  refine Fin.reverseInduction (motive := fun j => ∀ C : ConnectedComponents (T.stage j).Carrier,
    isPoincareStandard ((T.stage j).component C).Carrier) hbase ?_
  intro j ih
  exact (T.transition j).componentwise_isPoincareStandard (h j) (hctrl j) ih hsum

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.componentwise_isPoincareStandard then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.componentwise_isPoincareStandard"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.componentwise_isPoincareStandard ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.componentwise_isPoincareStandard

theorem isPoincareStandard_of_initialIdentification
    (h : ∀ i : Fin T.eventCount, (T.transition i).localReconstruction)
    (hctrl : T.poincareControlled) (hext : T.extinct) (hsum : poincareStandardSumClosed.{u})
    (M : ClosedOrientedManifold.{u} 3) [ConnectedSpace M.Carrier]
    (Φ : T.InitialIdentification M) : isPoincareStandard M.Carrier := by
  have hcomp := T.componentwise_isPoincareStandard h hctrl hext hsum 0
  have : ConnectedSpace (T.stage 0).Carrier :=
    Φ.1.toHomeomorph.connectedSpace_iff.mp inferInstance
  let C : ConnectedComponents (T.stage 0).Carrier :=
    ConnectedComponents.mk (Φ.1 (Classical.choice inferInstance))
  exact isPoincareStandard_of_diffeomorph Φ.1
    ((T.stage 0).isPoincareStandard_of_component C (hcomp C))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.isPoincareStandard_of_initialIdentification then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.isPoincareStandard_of_initialIdentification"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.isPoincareStandard_of_initialIdentification ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.isPoincareStandard_of_initialIdentification

end FiniteCutCapTrace

end DifferentialGeometry.Topology
