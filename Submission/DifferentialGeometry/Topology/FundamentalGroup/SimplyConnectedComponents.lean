import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Product
import Mathlib.Topology.Connected.TotallyDisconnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContinuousMap

namespace DifferentialGeometry.Topology

theorem subsingleton_pathHomotopicQuotient_of_totallyDisconnected
    {X : Type*} [TopologicalSpace X] [TotallyDisconnectedSpace X] (x y : X) :
    Subsingleton (Path.Homotopic.Quotient x y) := by
  constructor
  intro p q
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
    induction q using Path.Homotopic.Quotient.ind with
    | mk q =>
      congr 1
      ext t
      exact ((isPreconnected_range p.continuous).subsingleton
        ⟨t, rfl⟩ ⟨0, p.source⟩).trans
        ((isPreconnected_range q.continuous).subsingleton ⟨t, rfl⟩ ⟨0, q.source⟩).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_pathHomotopicQuotient_of_totallyDisconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_pathHomotopicQuotient_of_totallyDisconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_pathHomotopicQuotient_of_totallyDisconnected ``Submission.DifferentialGeometry.Topology.subsingleton_pathHomotopicQuotient_of_totallyDisconnected

theorem subsingleton_pathHomotopicQuotient_prod
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (hX : ∀ x y : X, Subsingleton (Path.Homotopic.Quotient x y))
    (hY : ∀ x y : Y, Subsingleton (Path.Homotopic.Quotient x y)) (x y : X × Y) :
    Subsingleton (Path.Homotopic.Quotient x y) := by
  constructor
  intro p q
  have hleft := (hX x.1 y.1).elim (Path.Homotopic.projLeft p) (Path.Homotopic.projLeft q)
  have hright := (hY x.2 y.2).elim (Path.Homotopic.projRight p) (Path.Homotopic.projRight q)
  rw [← Path.Homotopic.prod_projLeft_projRight p, ← Path.Homotopic.prod_projLeft_projRight q]
  exact congrArg₂ Path.Homotopic.prod hleft hright

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_pathHomotopicQuotient_prod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_pathHomotopicQuotient_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_pathHomotopicQuotient_prod ``Submission.DifferentialGeometry.Topology.subsingleton_pathHomotopicQuotient_prod

theorem subsingleton_pathHomotopicQuotient_of_homotopyEquiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y)
    (hY : ∀ x y : Y, Subsingleton (Path.Homotopic.Quotient x y)) (x y : X) :
    Subsingleton (Path.Homotopic.Quotient x y) := by
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e
  exact ⟨fun p q ↦ E.functor.map_injective
    ((hY (e x) (e y)).elim
      (E.functor.map (X := FundamentalGroupoid.mk x) (Y := FundamentalGroupoid.mk y) p)
      (E.functor.map (X := FundamentalGroupoid.mk x) (Y := FundamentalGroupoid.mk y) q))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_pathHomotopicQuotient_of_homotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_pathHomotopicQuotient_of_homotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_pathHomotopicQuotient_of_homotopyEquiv ``Submission.DifferentialGeometry.Topology.subsingleton_pathHomotopicQuotient_of_homotopyEquiv

end DifferentialGeometry.Topology
