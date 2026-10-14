import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeCochains
import Mathlib.Algebra.Homology.Opposite

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace DifferentialGeometry.Topology

theorem integralRelativeHomologyMap_bijective_of_absolute_and_subspace
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : ContinuousMap X Y) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B)
    (habs : ∀ n, Function.Bijective (integralSingularHomologyMap n f))
    (hsub : ∀ n, Function.Bijective (integralSingularHomologyMap n (singularPairRestriction f hf)))
    (n : ℕ) : Function.Bijective (integralRelativeHomologyMap n f hf) := by
  have h₂ : QuasiIso (integralSingularChainMap f) := by
    rw [quasiIso_iff]
    intro k
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (habs k)
  have h₁ : QuasiIso (integralSingularChainMap (singularPairRestriction f hf)) := by
    rw [quasiIso_iff]
    intro k
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (hsub k)
  have hrel : QuasiIso (integralRelativeChainMap f hf) :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃ (integralRelativeSequenceMap f hf)
      (integralRelativeChainSequence_shortExact A) (integralRelativeChainSequence_shortExact B) h₁ h₂
  exact (ConcreteCategory.isIso_iff_bijective _).mp
    (inferInstanceAs (_root_.CategoryTheory.IsIso (HomologicalComplex.homologyMap (integralRelativeChainMap f hf) n)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeHomologyMap_bijective_of_absolute_and_subspace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeHomologyMap_bijective_of_absolute_and_subspace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeHomologyMap_bijective_of_absolute_and_subspace ``Submission.DifferentialGeometry.Topology.integralRelativeHomologyMap_bijective_of_absolute_and_subspace

theorem integralRelativeCohomologyMap_bijective_of_absolute_and_subspace
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : ContinuousMap X Y) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B)
    (habs : ∀ n, Function.Bijective (integralSingularCohomologyMap n f))
    (hsub : ∀ n, Function.Bijective (integralSingularCohomologyMap n (singularPairRestriction f hf)))
    (n : ℕ) : Function.Bijective (integralRelativeCohomologyMap n f hf) := by
  have h₂ : QuasiIso (integralSingularCochainMap f) := by
    rw [quasiIso_iff]
    intro k
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (habs k)
  have h₃ : QuasiIso (integralSingularCochainMap (singularPairRestriction f hf)) := by
    rw [quasiIso_iff]
    intro k
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (hsub k)
  let φ := integralRelativeCochainSequenceMap f hf
  let F := HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) (.up ℕ)
  have h := HomologicalComplex.HomologySequence.quasiIso_τ₃
    (F.mapShortComplex.map (ShortComplex.opMap φ))
    ((integralRelativeCochainSequence_shortExact A).op.map_of_exact F)
    ((integralRelativeCochainSequence_shortExact B).op.map_of_exact F)
    ((HomologicalComplex.quasiIso_opFunctor_map_iff φ.τ₃).mpr h₃)
    ((HomologicalComplex.quasiIso_opFunctor_map_iff φ.τ₂).mpr h₂)
  have hrel : QuasiIso (integralRelativeCochainMap f hf) :=
    (HomologicalComplex.quasiIso_opFunctor_map_iff φ.τ₁).mp h
  exact (ConcreteCategory.isIso_iff_bijective _).mp
    (inferInstanceAs (_root_.CategoryTheory.IsIso (HomologicalComplex.homologyMap (integralRelativeCochainMap f hf) n)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeCohomologyMap_bijective_of_absolute_and_subspace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeCohomologyMap_bijective_of_absolute_and_subspace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeCohomologyMap_bijective_of_absolute_and_subspace ``Submission.DifferentialGeometry.Topology.integralRelativeCohomologyMap_bijective_of_absolute_and_subspace

end DifferentialGeometry.Topology
