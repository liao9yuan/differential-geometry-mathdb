import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalClassRealizationTransport
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassFrontier

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry.Topology

universe u

def PuncturedThreeManifoldTopHomologyVanishing
    (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (x₀ : M) : Prop :=
  (Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 2) ∧
    Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3)) ∧
    ∀ x : M, Subsingleton (IntegralHomology ({x}ᶜ : Set M) 3)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PuncturedThreeManifoldTopHomologyVanishing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PuncturedThreeManifoldTopHomologyVanishing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PuncturedThreeManifoldTopHomologyVanishing ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PuncturedThreeManifoldTopHomologyVanishing

theorem exists_unique_fundamentalClass_of_puncturedVanishing_of_localClassTransport
    (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [ConnectedSpace M]
    (x₀ : M) (o : TangentOrientationSection M)
    (hvan : PuncturedThreeManifoldTopHomologyVanishing M x₀)
    (htransport : localClassTransport o) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x := by
  obtain ⟨⟨h₂, h₃⟩, htop⟩ := hvan
  exact exists_unique_fundamentalClass_of_surjective_and_injective o
    (localClassRealizationLocallyConstant_of_localClassTransport o htransport) x₀
    (absoluteToRelative_surjective_of_subsingleton_punctured x₀ h₂)
    (absoluteToRelative_compl_singleton_injective_of_subsingleton x₀ h₃)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_fundamentalClass_of_puncturedVanishing_of_localClassTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_fundamentalClass_of_puncturedVanishing_of_localClassTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_fundamentalClass_of_puncturedVanishing_of_localClassTransport ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_fundamentalClass_of_puncturedVanishing_of_localClassTransport

def ClosedThreeManifoldFundamentalClassFrontier : Prop :=
  (∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (x₀ : M), PuncturedThreeManifoldTopHomologyVanishing M x₀) ∧
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (o : TangentOrientationSection M), localClassTransport o

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ClosedThreeManifoldFundamentalClassFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ClosedThreeManifoldFundamentalClassFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ClosedThreeManifoldFundamentalClassFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ClosedThreeManifoldFundamentalClassFrontier

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Lean in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PuncturedThreeManifoldTopHomologyVanishing,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_fundamentalClass_of_puncturedVanishing_of_localClassTransport,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ClosedThreeManifoldFundamentalClassFrontier] do
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a) do
      throwError "unexpected axioms for {n}: {axs}"
