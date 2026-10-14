import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

structure FiniteAncestorChain (H : ObservedHistory.{u})
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier) where
  component : (j : Fin (H.eventCount + 1)) → ConnectedComponents (H.stage j).Carrier
  terminal_eq : component (Fin.last H.eventCount) = terminal
  parent_eq : ∀ j : Fin H.eventCount,
    component j.castSucc = (H.event j).transition.childParent (component j.succ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FiniteAncestorChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FiniteAncestorChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FiniteAncestorChain ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FiniteAncestorChain

@[ext] theorem FiniteAncestorChain.ext {H : ObservedHistory.{u}}
    {terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier}
    (A B : FiniteAncestorChain H terminal) (h : A.component = B.component) : A = B := by
  cases A
  cases B
  cases h
  rfl

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FiniteAncestorChain
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FiniteAncestorChain.ext then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FiniteAncestorChain.ext"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FiniteAncestorChain.ext ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FiniteAncestorChain.ext

def ancestorComponent (H : ObservedHistory.{u})
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier) :
    (j : Fin (H.eventCount + 1)) → ConnectedComponents (H.stage j).Carrier :=
  Fin.reverseInduction terminal (fun j c => (H.event j).transition.childParent c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ancestorComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ancestorComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ancestorComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ancestorComponent

def rfs_finite_ancestor_chain (H : ObservedHistory.{u})
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier) :
    FiniteAncestorChain H terminal where
  component := ancestorComponent H terminal
  terminal_eq := by simp [ancestorComponent]
  parent_eq j := by simp [ancestorComponent]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_finite_ancestor_chain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_finite_ancestor_chain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_finite_ancestor_chain ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_finite_ancestor_chain

theorem exists_unique_finiteAncestorChain (H : ObservedHistory.{u})
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier) :
    Nonempty (Unique (FiniteAncestorChain H terminal)) := by
  let canonical := rfs_finite_ancestor_chain H terminal
  refine ⟨{ default := canonical, uniq := ?_ }⟩
  intro chain
  have hcomponent : chain.component = canonical.component := by
    funext j
    induction j using Fin.reverseInduction with
    | last => exact chain.terminal_eq.trans canonical.terminal_eq.symm
    | cast j ih => rw [chain.parent_eq, canonical.parent_eq, ih]
  exact FiniteAncestorChain.ext chain canonical hcomponent

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_finiteAncestorChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_finiteAncestorChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_finiteAncestorChain ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_finiteAncestorChain

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
