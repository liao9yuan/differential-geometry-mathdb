import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.OpenExcision

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Actual integral local homology and open-neighborhood excision -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- Local homology is the ORIGINAL relative singular homology of
(X, X minus the specified point). -/
abbrev integralLocalHomology (n : ℕ) (x : X) : ModuleCat.{u} ℤ :=
  integralRelativeHomology n ({x}ᶜ : Set X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralLocalHomology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralLocalHomology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralLocalHomology ``Submission.DifferentialGeometry.Topology.integralLocalHomology

omit [TopologicalSpace X] in
/-- Removing the SAME point in an original subspace is exactly the
preimage of the ambient point complement. -/
theorem subspaceIntersection_point_complement (x : X) (U : Set X) (hx : x ∈ U) :
    subspaceIntersection ({x}ᶜ : Set X) U = ({(⟨x, hx⟩ : U)}ᶜ : Set U) := by
  ext y
  simp [subspaceIntersection, Subtype.ext_iff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subspaceIntersection_point_complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subspaceIntersection_point_complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subspaceIntersection_point_complement ``Submission.DifferentialGeometry.Topology.subspaceIntersection_point_complement

/-- The original neighborhood inclusion is a map of the SAME punctured pairs. -/
theorem neighborhoodPointComplement_mapsTo (x : X) (U : Set X) (hx : x ∈ U) :
    MapsTo (singularSubspaceInclusion U) ({(⟨x, hx⟩ : U)}ᶜ : Set U) ({x}ᶜ : Set X) := by
  rw [← subspaceIntersection_point_complement x U hx]
  exact subspaceIntersection_mapsTo _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.neighborhoodPointComplement_mapsTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.neighborhoodPointComplement_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.neighborhoodPointComplement_mapsTo ``Submission.DifferentialGeometry.Topology.neighborhoodPointComplement_mapsTo

/-- Open-neighborhood excision applies to the ORIGINAL punctured pair
map at the SAME point, with no manifold or local-homology conclusion assumed. -/
theorem integralLocalChainMap_quasiIso [T1Space X] (x : X) (U : Set X)
    (hU : IsOpen U) (hx : x ∈ U) :
    QuasiIso (integralRelativeChainMap (singularSubspaceInclusion U)
      (neighborhoodPointComplement_mapsTo x U hx)) := by
  have hc : ({x}ᶜ : Set X) ∪ U = univ := by
    apply _root_.Set.eq_univ_of_forall
    intro y
    by_cases hy : y = x
    · exact Or.inr (hy.symm ▸ hx)
    · exact Or.inl hy
  have h := integralRelativeChainMap_openExcision ({x}ᶜ : Set X) U isClosed_singleton.isOpen_compl hU hc
  have H : ∀ hf : _root_.Set.MapsTo (singularSubspaceInclusion U) (subspaceIntersection ({x}ᶜ : Set X) U) ({x}ᶜ : Set X),
      QuasiIso (integralRelativeChainMap (singularSubspaceInclusion U) hf) := fun _ => h
  rw [subspaceIntersection_point_complement x U hx] at H
  exact H _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralLocalChainMap_quasiIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralLocalChainMap_quasiIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralLocalChainMap_quasiIso ``Submission.DifferentialGeometry.Topology.integralLocalChainMap_quasiIso

/-- The induced original pair map identifies actual neighborhood local
homology with actual ambient local homology, in EVERY degree. -/
def integralLocalHomologyNeighborhoodIso [T1Space X] (n : ℕ) (x : X) (U : Set X)
    (hU : IsOpen U) (hx : x ∈ U) :
    integralLocalHomology n (⟨x, hx⟩ : U) ≅ integralLocalHomology n x := by
  letI := integralLocalChainMap_quasiIso x U hU hx
  exact _root_.CategoryTheory.asIso (HomologicalComplex.homologyMap
    (integralRelativeChainMap (singularSubspaceInclusion U) (neighborhoodPointComplement_mapsTo x U hx)) n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralLocalHomologyNeighborhoodIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralLocalHomologyNeighborhoodIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralLocalHomologyNeighborhoodIso ``Submission.DifferentialGeometry.Topology.integralLocalHomologyNeighborhoodIso

end DifferentialGeometry.Topology
