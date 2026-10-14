import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ConnectedZeroHomology
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeMaps
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Actual relative H0 for a path-connected pair -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- The actual absolute-to-relative map is surjective in degree zero,
since the original chain quotient is degreewise surjective and has no
outgoing differential in degree zero. -/
theorem integralAbsoluteToRelative_zero_epi (A : Set X) :
    Epi (HomologicalComplex.homologyMap (integralRelativeChainSequence A).g 0) := by
  have := (integralRelativeChainSequence_shortExact A).epi_g
  exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
    (integralRelativeChainSequence A).g 0 (by intro j; simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralAbsoluteToRelative_zero_epi then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralAbsoluteToRelative_zero_epi"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralAbsoluteToRelative_zero_epi ``Submission.DifferentialGeometry.Topology.integralAbsoluteToRelative_zero_epi

theorem integralRelativeHomologyMap_zero_eq_of_joined
    {Y : Type u} [TopologicalSpace Y]
    (f g : C(X, Y)) (A : Set X) (B : Set Y)
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (h : ∀ x, Joined (f x) (g x)) :
    integralRelativeHomologyMap 0 f hf = integralRelativeHomologyMap 0 g hg := by
  have hsurj : Function.Surjective (integralAbsoluteToRelative 0 A) :=
    (ModuleCat.epi_iff_surjective _).mp (integralAbsoluteToRelative_zero_epi A)
  have habs := integralSingularHomologyMap_zero_eq_of_joined f g h
  have hcomp : (integralRelativeHomologyMap 0 f hf).comp (integralAbsoluteToRelative 0 A) =
      (integralRelativeHomologyMap 0 g hg).comp (integralAbsoluteToRelative 0 A) := by
    rw [← integralAbsoluteToRelative_natural, ← integralAbsoluteToRelative_natural, habs]
  apply LinearMap.ext
  intro a
  obtain ⟨b, rfl⟩ := hsurj a
  exact LinearMap.congr_fun hcomp b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeHomologyMap_zero_eq_of_joined then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeHomologyMap_zero_eq_of_joined"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeHomologyMap_zero_eq_of_joined ``Submission.DifferentialGeometry.Topology.integralRelativeHomologyMap_zero_eq_of_joined

/-- For a path-connected original pair, actual relative H0 vanishes by
the actual exact sequence and the proved H0 inclusion isomorphism. -/
theorem integralRelativeZero_subsingleton [PathConnectedSpace X]
    (A : Set X) [PathConnectedSpace A] : Subsingleton (integralRelativeHomology 0 A) := by
  have hi := integralSingularHomologyZeroMap_isIso (singularSubspaceInclusion A)
  have hs := (integralRelativeChainSequence_shortExact A).homology_exact₂ 0
  have hz := hs.epi_f_iff.mp (IsIso.epi_of_iso
    (HomologicalComplex.homologyMap (integralSingularChainMap (singularSubspaceInclusion A)) 0))
  exact ModuleCat.subsingleton_of_isZero (@IsZero.of_epi_eq_zero _ _ _ _ _
    (HomologicalComplex.homologyMap (integralRelativeChainSequence A).g 0)
      (integralAbsoluteToRelative_zero_epi A) hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeZero_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeZero_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeZero_subsingleton ``Submission.DifferentialGeometry.Topology.integralRelativeZero_subsingleton

end DifferentialGeometry.Topology
