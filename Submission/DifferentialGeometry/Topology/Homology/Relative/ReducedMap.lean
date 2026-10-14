import Submission.DifferentialGeometry.Topology.Homology.Relative.Reduced
import Submission.DifferentialGeometry.Topology.Homology.Relative.Map
import Submission.DifferentialGeometry.Topology.Homology.Algebra.AugmentHomology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology
open scoped _root_.ZeroObject
namespace DifferentialGeometry.Homology
universe u
variable {X Y : TopCat.{u}} {s : Set X} {t : Set Y}
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)

def augmentedRelativeChainMap (f : X ⟶ Y) (hf : Set.MapsTo f s t) :
    augmentedRelativeChainComplex X s R ⟶ augmentedRelativeChainComplex Y t R :=
  DifferentialGeometry.ChainComplex.augmentMap (by simp) (by simp) (relativeChainMap R f hf)
    (0 : (0 : ModuleCat.{u} k) ⟶ 0) (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedRelativeChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedRelativeChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedRelativeChainMap ``Submission.DifferentialGeometry.Homology.augmentedRelativeChainMap


def augmentedRelativeShortComplexMap (f : X ⟶ Y) (hf : Set.MapsTo f s t) :
    augmentedRelativeShortComplex X s R ⟶ augmentedRelativeShortComplex Y t R where
  τ₁ := augmentedSingularChainMap R (relativeSubspaceMap f hf)
  τ₂ := augmentedSingularChainMap R f
  τ₃ := augmentedRelativeChainMap R f hf
  comm₁₂ := by
    apply _root_.HomologicalComplex.Hom.ext
    funext n
    cases n with
    | zero => change 𝟙 R ≫ 𝟙 R = 𝟙 R ≫ 𝟙 R; rfl
    | succ n => exact congrArg (fun g => g.f n) (relativeInclusion_naturality R f hf).symm
  comm₂₃ := by
    apply _root_.HomologicalComplex.Hom.ext
    funext n
    cases n with
    | zero => change 𝟙 R ≫ (0 : R ⟶ 0) = (0 : R ⟶ 0) ≫ 0; simp
    | succ n => exact congrArg (fun g => g.f n) (relativeProjection_chainMap R f hf).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedRelativeShortComplexMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedRelativeShortComplexMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedRelativeShortComplexMap ``Submission.DifferentialGeometry.Homology.augmentedRelativeShortComplexMap


@[reassoc]
theorem augmentedRelativeHomologySuccIso_naturality (f : X ⟶ Y) (hf : Set.MapsTo f s t)
    (n : ℕ) :
    _root_.HomologicalComplex.homologyMap (augmentedRelativeChainMap R f hf) (n + 2) ≫
      (augmentedRelativeHomologySuccIso Y t R n).hom =
    (augmentedRelativeHomologySuccIso X s R n).hom ≫ relativeHomologyMap R f hf (n + 1) :=
  DifferentialGeometry.ChainComplex.augmentHomologySuccIso_naturality (by simp) (by simp)
    (relativeChainMap R f hf) (0 : (0 : ModuleCat.{u} k) ⟶ 0) (by simp) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedRelativeHomologySuccIso_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedRelativeHomologySuccIso_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedRelativeHomologySuccIso_naturality ``Submission.DifferentialGeometry.Homology.augmentedRelativeHomologySuccIso_naturality


@[reassoc]
theorem relativeReducedConnectingIso_naturality [ContractibleSpace X] [ContractibleSpace Y]
    (f : X ⟶ Y) (hf : Set.MapsTo f s t) (n : ℕ) :
    (relativeReducedConnectingIso X s R n).hom ≫
      reducedSingularHomologyMap R (relativeSubspaceMap f hf) n =
    relativeHomologyMap R f hf (n + 1) ≫ (relativeReducedConnectingIso Y t R n).hom := by
  apply (_root_.CategoryTheory.cancel_epi (augmentedRelativeHomologySuccIso X s R n).hom).mp
  rw [augmentedRelativeHomologySuccIso_connecting_assoc,
    ← augmentedRelativeHomologySuccIso_naturality_assoc,
    augmentedRelativeHomologySuccIso_connecting]
  exact _root_.HomologicalComplex.HomologySequence.δ_naturality
    (augmentedRelativeShortComplexMap R f hf)
    (augmentedRelativeShortExact X s R) (augmentedRelativeShortExact Y t R) (n + 2) (n + 1) rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.relativeReducedConnectingIso_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.relativeReducedConnectingIso_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.relativeReducedConnectingIso_naturality ``Submission.DifferentialGeometry.Homology.relativeReducedConnectingIso_naturality
end DifferentialGeometry.Homology
