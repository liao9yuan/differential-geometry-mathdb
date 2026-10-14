import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SmallSubspaceInclusion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The same relative complex formed using original small chains -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module

universe u v

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- Quotient the ORIGINAL small complex by the ORIGINAL chains of the
specified cover member. -/
def integralSmallRelativeChains (U : ι → Set X) (i : ι) : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  _root_.CategoryTheory.Limits.cokernel (integralSingularChainToSmall U i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSmallRelativeChains then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSmallRelativeChains"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSmallRelativeChains ``Submission.DifferentialGeometry.Topology.integralSmallRelativeChains

/-- The actual subspace-small-relative short complex. -/
def integralSmallRelativeSequence (U : ι → Set X) (i : ι) :
    ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (integralSingularChainToSmall U i) (cokernel.π _) (cokernel.condition _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSmallRelativeSequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSmallRelativeSequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSmallRelativeSequence ``Submission.DifferentialGeometry.Topology.integralSmallRelativeSequence

/-- This sequence is short exact for the same proved inclusion and cokernel. -/
theorem integralSmallRelativeSequence_shortExact (U : ι → Set X) (i : ι) :
    (integralSmallRelativeSequence U i).ShortExact where
  exact := (integralSmallRelativeSequence U i).exact_of_g_is_cokernel (_root_.CategoryTheory.Limits.cokernelIsCokernel _)
  mono_f := integralSingularChainToSmall_mono U i
  epi_g := inferInstanceAs (_root_.CategoryTheory.Epi (cokernel.π (integralSingularChainToSmall U i)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSmallRelativeSequence_shortExact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSmallRelativeSequence_shortExact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSmallRelativeSequence_shortExact ``Submission.DifferentialGeometry.Topology.integralSmallRelativeSequence_shortExact

/-- The SAME small inclusion induces the comparison to the original
relative singular complex, with identity on the specified subspace. -/
def integralSmallRelativeComparison (U : ι → Set X) (i : ι) :
    integralSmallRelativeChains U i ⟶ integralRelativeChains (U i) :=
  cokernel.map _ _ (𝟙 _) (integralSingularSmallInclusion U)
    (by rw [integralSingularChainToSmall_inclusion, Category.id_comp])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSmallRelativeComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSmallRelativeComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSmallRelativeComparison ``Submission.DifferentialGeometry.Topology.integralSmallRelativeComparison

/-- The comparison is a morphism of these SAME original short exact sequences. -/
def integralSmallRelativeSequenceComparison (U : ι → Set X) (i : ι) :
    integralSmallRelativeSequence U i ⟶ integralRelativeChainSequence (U i) where
  τ₁ := 𝟙 _
  τ₂ := integralSingularSmallInclusion U
  τ₃ := integralSmallRelativeComparison U i
  comm₁₂ := by
    change (𝟙 _) ≫ integralSingularChainMap (singularSubspaceInclusion (U i)) =
      integralSingularChainToSmall U i ≫ integralSingularSmallInclusion U
    rw [Category.id_comp, integralSingularChainToSmall_inclusion]
  comm₂₃ := (cokernel.π_desc _ _ _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSmallRelativeSequenceComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSmallRelativeSequenceComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSmallRelativeSequenceComparison ``Submission.DifferentialGeometry.Topology.integralSmallRelativeSequenceComparison

/-- For an actual open cover, the SAME relative comparison is a
quasi-isomorphism, using the proved small-chain result and the exact sequences. -/
theorem integralSmallRelativeComparison_quasiIso (U : ι → Set X) (i : ι)
    (hU : ∀ j, IsOpen (U j)) (hcover : ∀ x, ∃ j, x ∈ U j) :
    QuasiIso (integralSmallRelativeComparison U i) := by
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃
    (integralSmallRelativeSequenceComparison U i)
    (integralSmallRelativeSequence_shortExact U i)
    (integralRelativeChainSequence_shortExact (U i))
    (inferInstanceAs (QuasiIso (𝟙 (integralSingularChains (U i)))))
    (integralSingularSmallInclusion_quasiIso U hU hcover)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSmallRelativeComparison_quasiIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSmallRelativeComparison_quasiIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSmallRelativeComparison_quasiIso ``Submission.DifferentialGeometry.Topology.integralSmallRelativeComparison_quasiIso

/-- Its actual homology map identifies the small relative quotient with
the ORIGINAL relative singular homology, in every degree. -/
def integralSmallRelativeHomologyIso (n : ℕ) (U : ι → Set X) (i : ι)
    (hU : ∀ j, IsOpen (U j)) (hcover : ∀ x, ∃ j, x ∈ U j) :
    (integralSmallRelativeChains U i).homology n ≅ integralRelativeHomology n (U i) := by
  letI := integralSmallRelativeComparison_quasiIso U i hU hcover
  exact _root_.CategoryTheory.asIso (HomologicalComplex.homologyMap (integralSmallRelativeComparison U i) n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSmallRelativeHomologyIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSmallRelativeHomologyIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSmallRelativeHomologyIso ``Submission.DifferentialGeometry.Topology.integralSmallRelativeHomologyIso

end DifferentialGeometry.Topology
