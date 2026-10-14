import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Submission.DifferentialGeometry.Topology.SphereSeparation.ComponentCount
import Submission.DifferentialGeometry.Topology.SphereSeparation.EuclideanComponents
import Submission.DifferentialGeometry.Topology.SphereSeparation.Incidence
import Submission.DifferentialGeometry.Topology.SphereSeparation.LocalTwoSided
import Submission.DifferentialGeometry.Topology.SphereSeparation.ReducedH0
import Submission.DifferentialGeometry.Topology.SphereSeparation.Sides

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.SphereSeparation

def HasTwoComplementComponents (e : SphereTwo → EuclideanThree) : Prop :=
  Nonempty
    (ConnectedComponents
      ({x : EuclideanThree | x ∉ Set.range e} : Set EuclideanThree) ≃ Fin 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.HasTwoComplementComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.HasTwoComplementComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.HasTwoComplementComponents ``Submission.DifferentialGeometry.Topology.SphereSeparation.HasTwoComplementComponents

def HasAlexanderDualityH0Certificate
    (e : SphereTwo → EuclideanThree) : Prop :=
  Nonempty
    (reducedSingularH0
        (TopCat.of {x : EuclideanThree | x ∉ Set.range e}) ≅
      ModuleCat.of ℤ ℤ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.HasAlexanderDualityH0Certificate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.HasAlexanderDualityH0Certificate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.HasAlexanderDualityH0Certificate ``Submission.DifferentialGeometry.Topology.SphereSeparation.HasAlexanderDualityH0Certificate

theorem hasTwoComplementComponents_of_isCompact_of_alexanderDualityH0Certificate
    (e : SphereTwo → EuclideanThree) (hcompact : IsCompact (Set.range e))
    (hAD : HasAlexanderDualityH0Certificate e) :
    HasTwoComplementComponents e := by
  have hne : Set.range e ≠ (Set.univ : Set EuclideanThree) := by
    intro hrange
    have huniv : IsCompact (Set.univ : Set EuclideanThree) := by
      rw [← hrange]
      exact hcompact
    exact (not_compactSpace_iff.mpr
      (inferInstance : NoncompactSpace EuclideanThree))
      (isCompact_univ_iff.mp huniv)
  let X := ({x : EuclideanThree | x ∉ Set.range e} : Set EuclideanThree)
  let _ : Nonempty X :=
    Set.Nonempty.to_subtype (Set.nonempty_compl.mpr hne)
  let _ : LocallyPathConnectedSpace X :=
    hcompact.isClosed.isOpen_compl.locallyPathConnectedSpace
  exact connectedComponents_equiv_fin_two_of_reducedSingularH0_iso_int
    (TopCat.of X) hAD

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.hasTwoComplementComponents_of_isCompact_of_alexanderDualityH0Certificate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.hasTwoComplementComponents_of_isCompact_of_alexanderDualityH0Certificate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.hasTwoComplementComponents_of_isCompact_of_alexanderDualityH0Certificate ``Submission.DifferentialGeometry.Topology.SphereSeparation.hasTwoComplementComponents_of_isCompact_of_alexanderDualityH0Certificate

theorem hasTwoComplementComponents_of_alexanderDualityH0Certificate
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (hAD : HasAlexanderDualityH0Certificate e) :
    HasTwoComplementComponents e := by
  have hcompact : IsCompact (Set.range e) :=
    isCompact_range he.contMDiff.continuous
  have hne : Set.range e ≠ (Set.univ : Set EuclideanThree) := by
    intro hrange
    have huniv : IsCompact (Set.univ : Set EuclideanThree) := by
      rw [← hrange]
      exact hcompact
    exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace EuclideanThree))
      (isCompact_univ_iff.mp huniv)
  let X := ({x : EuclideanThree | x ∉ Set.range e} : Set EuclideanThree)
  let _ : Nonempty X :=
    Set.Nonempty.to_subtype (Set.nonempty_compl.mpr hne)
  let _ : LocallyPathConnectedSpace X :=
    hcompact.isClosed.isOpen_compl.locallyPathConnectedSpace
  exact connectedComponents_equiv_fin_two_of_reducedSingularH0_iso_int
    (TopCat.of X) hAD

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.hasTwoComplementComponents_of_alexanderDualityH0Certificate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.hasTwoComplementComponents_of_alexanderDualityH0Certificate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.hasTwoComplementComponents_of_alexanderDualityH0Certificate ``Submission.DifferentialGeometry.Topology.SphereSeparation.hasTwoComplementComponents_of_alexanderDualityH0Certificate

noncomputable def BothComponentsApproachSphere
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (hcount : HasTwoComplementComponents e) : Prop :=
  let p := complementPairOfComponentCount
    ((isCompact_range he.contMDiff.continuous).isClosed.isOpen_compl)
    hcount
  Set.range e ⊆ closure p.left ∧ Set.range e ⊆ closure p.right

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.BothComponentsApproachSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.BothComponentsApproachSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.BothComponentsApproachSphere ``Submission.DifferentialGeometry.Topology.SphereSeparation.BothComponentsApproachSphere

noncomputable def topologicalSphereSidesOfComponentCount
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (hcount : HasTwoComplementComponents e)
    (happroach : BothComponentsApproachSphere e he hcount) :
    SphereSides (Set.range e) := by
  have hcompact : IsCompact (Set.range e) :=
    isCompact_range he.contMDiff.continuous
  let p : ComplementPair (Set.range e) :=
    complementPairOfComponentCount hcompact.isClosed.isOpen_compl hcount
  exact sphereSidesOfComplementPair hcompact p happroach.1 happroach.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOfComponentCount then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOfComponentCount"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOfComponentCount ``Submission.DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOfComponentCount

noncomputable def topologicalSphereSidesOfComponentCount_of_locallyTwoSided
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (hcount : HasTwoComplementComponents e)
    (hlocal : LocallyTwoSided (Set.range e)) :
    SphereSides (Set.range e) := by
  have hcompact : IsCompact (Set.range e) :=
    isCompact_range he.contMDiff.continuous
  let p : ComplementPair (Set.range e) :=
    complementPairOfComponentCount hcompact.isClosed.isOpen_compl hcount
  have hconnected : IsConnected (Set.range e) :=
    by simpa only [_root_.Set.image_univ] using
      isConnected_sphereTwo.image e he.contMDiff.continuous.continuousOn
  have happroach :
      Set.range e ⊆ closure p.left ∧ Set.range e ⊆ closure p.right :=
    p.both_components_approach_of_locallyTwoSided hconnected hlocal
  exact sphereSidesOfComplementPair hcompact p happroach.1 happroach.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOfComponentCount_of_locallyTwoSided then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOfComponentCount_of_locallyTwoSided"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOfComponentCount_of_locallyTwoSided ``Submission.DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOfComponentCount_of_locallyTwoSided

noncomputable def topologicalSphereSidesOfAlexanderDualityData
    (e : SphereTwo → EuclideanThree)
    (hcompact : IsCompact (Set.range e))
    (hconnected : IsConnected (Set.range e))
    (hlocal : LocallyTwoSided (Set.range e))
    (hAD : HasAlexanderDualityH0Certificate e) :
    SphereSides (Set.range e) := by
  let hcount : HasTwoComplementComponents e :=
    hasTwoComplementComponents_of_isCompact_of_alexanderDualityH0Certificate
      e hcompact hAD
  let p : ComplementPair (Set.range e) :=
    complementPairOfComponentCount hcompact.isClosed.isOpen_compl hcount
  have happroach :
      Set.range e ⊆ closure p.left ∧ Set.range e ⊆ closure p.right :=
    p.both_components_approach_of_locallyTwoSided hconnected hlocal
  exact sphereSidesOfComplementPair hcompact p happroach.1 happroach.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOfAlexanderDualityData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOfAlexanderDualityData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOfAlexanderDualityData ``Submission.DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOfAlexanderDualityData

noncomputable def topologicalSphereSidesOfAlexanderDuality
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (hAD : HasAlexanderDualityH0Certificate e) :
    SphereSides (Set.range e) :=
  topologicalSphereSidesOfComponentCount_of_locallyTwoSided e he
    (hasTwoComplementComponents_of_alexanderDualityH0Certificate e he hAD)
    (locallyTwoSided_range_of_isSmoothEmbedding he)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOfAlexanderDuality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOfAlexanderDuality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOfAlexanderDuality ``Submission.DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOfAlexanderDuality

theorem topologicalSphereSidesOfComponentCount_unique
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (hcount : HasTwoComplementComponents e)
    (happroach : BothComponentsApproachSphere e he hcount)
    (d : SphereSides (Set.range e)) :
    d = topologicalSphereSidesOfComponentCount e he hcount happroach :=
  SphereSides.unique _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOfComponentCount_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOfComponentCount_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOfComponentCount_unique ``Submission.DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOfComponentCount_unique

end DifferentialGeometry.Topology.SphereSeparation
