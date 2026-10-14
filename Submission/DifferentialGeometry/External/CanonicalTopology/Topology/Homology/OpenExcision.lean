import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ExcisionQuotient

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Excision for the original integral relative singular homology -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- For two original open subspaces covering X, the SAME original pair
inclusion (B,B ∩ A) → (X,A) is a quasi-isomorphism of relative complexes.
This is proved by the exact quotient identification and actual subdivision. -/
theorem integralRelativeChainMap_openExcision (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = _root_.Set.univ) :
    QuasiIso (integralRelativeChainMap (singularSubspaceInclusion B) (subspaceIntersection_mapsTo A B)) := by
  have hU : ∀ i, IsOpen (twoSetCover A B i) := by
    intro i
    cases i with
    | false => exact hA
    | true => exact hB
  have hc : ∀ x, ∃ i, x ∈ twoSetCover A B i := by
    intro x
    have hx : x ∈ A ∪ B := hcover.symm ▸ _root_.Set.mem_univ x
    rcases hx with hx | hx
    · exact ⟨false, hx⟩
    · exact ⟨true, hx⟩
  let := integralSmallRelativeComparison_quasiIso (twoSetCover A B) _root_.Bool.false hU hc
  rw [← integralExcisionSmallMap_comparison]
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeChainMap_openExcision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeChainMap_openExcision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeChainMap_openExcision ``Submission.DifferentialGeometry.Topology.integralRelativeChainMap_openExcision

/-- The excision isomorphism is induced by the SAME actual relative pair
map, in every degree of the original integral singular homology. -/
def integralRelativeOpenExcisionIso (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = _root_.Set.univ) :
    integralRelativeHomology n (subspaceIntersection A B) ≅ integralRelativeHomology n A := by
  letI := integralRelativeChainMap_openExcision A B hA hB hcover
  exact _root_.CategoryTheory.asIso (HomologicalComplex.homologyMap
    (integralRelativeChainMap (singularSubspaceInclusion B) (subspaceIntersection_mapsTo A B)) n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeOpenExcisionIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeOpenExcisionIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeOpenExcisionIso ``Submission.DifferentialGeometry.Topology.integralRelativeOpenExcisionIso

/-- Its homomorphism is the original relative homology map, exactly. -/
theorem integralRelativeOpenExcisionIso_hom (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = _root_.Set.univ) :
    (integralRelativeOpenExcisionIso n A B hA hB hcover).hom.hom =
      integralRelativeHomologyMap n (singularSubspaceInclusion B) (subspaceIntersection_mapsTo A B) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeOpenExcisionIso_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeOpenExcisionIso_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeOpenExcisionIso_hom ``Submission.DifferentialGeometry.Topology.integralRelativeOpenExcisionIso_hom

end DifferentialGeometry.Topology
