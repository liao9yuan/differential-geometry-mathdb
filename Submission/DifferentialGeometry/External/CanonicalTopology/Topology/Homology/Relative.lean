import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Homotopy
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Actual relative integral singular chains and the homology sequence

The relative complex is the cokernel of the original inclusion of singular
chains on the actual subspace. Its short exact sequence is proved using
injectivity of that inclusion, and the connecting map is the proved snake
construction on these same complexes.
-/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The original chain map induced by the original continuous map. -/
abbrev integralSingularChainMap (f : C(X, Y)) : integralSingularChains X ⟶ integralSingularChains Y :=
  ((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).map (TopCat.ofHom f)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainMap ``Submission.DifferentialGeometry.Topology.integralSingularChainMap

/-- The actual continuous inclusion of the specified subspace. -/
def singularSubspaceInclusion (A : Set X) : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.singularSubspaceInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.singularSubspaceInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.singularSubspaceInclusion ``Submission.DifferentialGeometry.Topology.singularSubspaceInclusion

/-- Actual subspace inclusion is injective on the original singular chain complex. -/
instance integralSingularChainMap_subspace_mono (A : Set X) :
    Mono (integralSingularChainMap (singularSubspaceInclusion A)) := by
  have : _root_.CategoryTheory.Mono (TopCat.ofHom (singularSubspaceInclusion A)) :=
    (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  exact inferInstanceAs (_root_.CategoryTheory.Mono
    (((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).map
      (TopCat.ofHom (singularSubspaceInclusion A))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainMap_subspace_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainMap_subspace_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainMap_subspace_mono ``Submission.DifferentialGeometry.Topology.integralSingularChainMap_subspace_mono

/-- The actual relative complex C(X,A;Z), obtained by quotienting the original
singular subcomplex, with no assumed relative-homology interface. -/
def integralRelativeChains (A : Set X) : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  _root_.CategoryTheory.Limits.cokernel (integralSingularChainMap (singularSubspaceInclusion A))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeChains then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeChains"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeChains ``Submission.DifferentialGeometry.Topology.integralRelativeChains

/-- The original short complex C(A) → C(X) → C(X,A). -/
def integralRelativeChainSequence (A : Set X) : _root_.CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (integralSingularChainMap (singularSubspaceInclusion A))
    (cokernel.π _) (cokernel.condition _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeChainSequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeChainSequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeChainSequence ``Submission.DifferentialGeometry.Topology.integralRelativeChainSequence

/-- Exactness comes from the proved inclusion and the actual cokernel. -/
theorem integralRelativeChainSequence_shortExact (A : Set X) :
    (integralRelativeChainSequence A).ShortExact where
  exact := (integralRelativeChainSequence A).exact_of_g_is_cokernel (_root_.CategoryTheory.Limits.cokernelIsCokernel _)
  mono_f := integralSingularChainMap_subspace_mono A
  epi_g := inferInstanceAs (_root_.CategoryTheory.Epi (cokernel.π (integralSingularChainMap (singularSubspaceInclusion A))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeChainSequence_shortExact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeChainSequence_shortExact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeChainSequence_shortExact ``Submission.DifferentialGeometry.Topology.integralRelativeChainSequence_shortExact

/-- Relative singular homology is the homology of that same quotient complex. -/
abbrev integralRelativeHomology (n : ℕ) (A : Set X) : ModuleCat.{u} ℤ :=
  (integralRelativeChains A).homology n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeHomology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeHomology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeHomology ``Submission.DifferentialGeometry.Topology.integralRelativeHomology

/-- The canonical map from absolute to relative homology. -/
def integralAbsoluteToRelative (n : ℕ) (A : Set X) :
    integralSingularHomology n X →ₗ[ℤ] integralRelativeHomology n A :=
  (HomologicalComplex.homologyMap (integralRelativeChainSequence A).g n).hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralAbsoluteToRelative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralAbsoluteToRelative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralAbsoluteToRelative ``Submission.DifferentialGeometry.Topology.integralAbsoluteToRelative

/-- The actual boundary connecting homomorphism of the same pair. -/
def integralRelativeConnecting (n : ℕ) (A : Set X) :
    integralRelativeHomology (n + 1) A →ₗ[ℤ] integralSingularHomology n A :=
  ((integralRelativeChainSequence_shortExact A).δ (n + 1) n (by simp)).hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeConnecting then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeConnecting"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeConnecting ``Submission.DifferentialGeometry.Topology.integralRelativeConnecting

/-- Exactness at the absolute group uses the actual inclusion and quotient maps. -/
theorem integralRelative_exact_absolute (n : ℕ) (A : Set X) :
    Function.Exact (integralSingularHomologyMap n (singularSubspaceInclusion A))
      (integralAbsoluteToRelative n A) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((integralRelativeChainSequence_shortExact A).homology_exact₂ n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelative_exact_absolute then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelative_exact_absolute"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelative_exact_absolute ``Submission.DifferentialGeometry.Topology.integralRelative_exact_absolute

/-- Exactness at the relative group uses the constructed connecting map. -/
theorem integralRelative_exact_relative (n : ℕ) (A : Set X) :
    Function.Exact (integralAbsoluteToRelative (n + 1) A) (integralRelativeConnecting n A) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((integralRelativeChainSequence_shortExact A).homology_exact₃ (n + 1) n (by simp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelative_exact_relative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelative_exact_relative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelative_exact_relative ``Submission.DifferentialGeometry.Topology.integralRelative_exact_relative

/-- Exactness at the subspace homology completes the actual pair sequence. -/
theorem integralRelative_exact_subspace (n : ℕ) (A : Set X) :
    Function.Exact (integralRelativeConnecting n A)
      (integralSingularHomologyMap n (singularSubspaceInclusion A)) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((integralRelativeChainSequence_shortExact A).homology_exact₁ (n + 1) n (by simp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelative_exact_subspace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelative_exact_subspace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelative_exact_subspace ``Submission.DifferentialGeometry.Topology.integralRelative_exact_subspace

/-- For a contractible ambient space the actual connecting map is an
isomorphism in positive subspace degree, as required for local homology. -/
def integralRelativeConnectingEquivOfContractible [ContractibleSpace X]
    (n : ℕ) (hn : n ≠ 0) (A : Set X) :
    integralRelativeHomology (n + 1) A ≃ₗ[ℤ] integralSingularHomology n A := by
  let := integralSingularHomology_subsingleton_of_contractible n hn X
  let := integralSingularHomology_subsingleton_of_contractible (n + 1) (by omega) X
  exact ((integralRelativeChainSequence_shortExact A).δIso (n + 1) n (by simp)
    (ModuleCat.isZero_of_subsingleton (integralSingularHomology (n + 1) X))
    (ModuleCat.isZero_of_subsingleton (integralSingularHomology n X))).toLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeConnectingEquivOfContractible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeConnectingEquivOfContractible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeConnectingEquivOfContractible ``Submission.DifferentialGeometry.Topology.integralRelativeConnectingEquivOfContractible

end DifferentialGeometry.Topology
