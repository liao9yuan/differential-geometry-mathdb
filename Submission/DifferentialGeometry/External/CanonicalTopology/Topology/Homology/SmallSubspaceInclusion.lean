import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SmallHomology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Actual subspace chains included in the original small complex -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module

universe u v

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- The original inclusion of a cover member takes its chains into the
SAME original small-chain submodule. -/
theorem integralSingularChainToSmall_mem (n : ℕ) (U : ι → Set X) (i : ι)
    (c : (integralSingularChains (U i)).X n) :
    (integralSingularChainMap (singularSubspaceInclusion (U i))).f n c ∈ integralSingularSmallChains n U := by
  apply Submodule.mem_iSup_of_mem i
  rw [integralSingularChainsIn_eq_range]
  exact ⟨c, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainToSmall_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainToSmall_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainToSmall_mem ``Submission.DifferentialGeometry.Topology.integralSingularChainToSmall_mem

/-- The SAME actual inclusion, corestricted to the original small complex. -/
def integralSingularChainToSmall (U : ι → Set X) (i : ι) :
    integralSingularChains (U i) ⟶ integralSingularSmallComplex U where
  f n := ModuleCat.ofHom (((integralSingularChainMap (singularSubspaceInclusion (U i))).f n).hom.codRestrict
    (integralSingularSmallChains n U) (integralSingularChainToSmall_mem n U i))
  comm' j k _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg (fun f : (integralSingularChains (U i)).X j ⟶ (integralSingularChains X).X k => f c)
      ((integralSingularChainMap (singularSubspaceInclusion (U i))).comm j k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainToSmall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainToSmall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainToSmall ``Submission.DifferentialGeometry.Topology.integralSingularChainToSmall

/-- Factoring through the small complex gives the SAME original subspace inclusion. -/
theorem integralSingularChainToSmall_inclusion (U : ι → Set X) (i : ι) :
    integralSingularChainToSmall U i ≫ integralSingularSmallInclusion U =
      integralSingularChainMap (singularSubspaceInclusion (U i)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainToSmall_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainToSmall_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainToSmall_inclusion ``Submission.DifferentialGeometry.Topology.integralSingularChainToSmall_inclusion

/-- This actual inclusion into the small complex is injective. -/
instance integralSingularChainToSmall_mono (U : ι → Set X) (i : ι) :
    Mono (integralSingularChainToSmall U i) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  apply (ModuleCat.mono_iff_injective _).mpr
  intro a b h
  apply integralSingularChainInclusion_injective n (U i)
  exact congrArg Subtype.val h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainToSmall_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainToSmall_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainToSmall_mono ``Submission.DifferentialGeometry.Topology.integralSingularChainToSmall_mono

end DifferentialGeometry.Topology
