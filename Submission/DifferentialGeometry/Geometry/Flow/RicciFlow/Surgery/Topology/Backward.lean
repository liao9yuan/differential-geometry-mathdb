import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData

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

structure BackwardPointTrace (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (endpoint : (H.stage last).Carrier) where
  point : (j : Fin (H.eventCount + 1)) → first ≤ j → j ≤ last → (H.stage j).Carrier
  endpoint_eq : point last hle le_rfl = endpoint
  crossing : ∀ i : Fin H.eventCount, ∀ hf : first ≤ i.castSucc, ∀ hl : i.succ ≤ last,
    (H.event i).RegularCrossing
      (point i.castSucc hf ((Fin.castSucc_lt_succ (i := i)).le.trans hl))
      (point i.succ (hf.trans (Fin.castSucc_lt_succ (i := i)).le) hl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

namespace BackwardPointTrace

variable {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)}
    {hle : first ≤ last} {endpoint : (H.stage last).Carrier}

theorem point_unique (A B : BackwardPointTrace H first last hle endpoint) :
    ∀ j : Fin (H.eventCount + 1), ∀ hf : first ≤ j, ∀ hl : j ≤ last,
      A.point j hf hl = B.point j hf hl := by
  intro j
  induction j using Fin.reverseInduction with
  | last =>
    intro hf hl
    have he : last = Fin.last H.eventCount := le_antisymm (Fin.le_last _) hl
    subst last
    exact A.endpoint_eq.trans B.endpoint_eq.symm
  | cast i ih =>
    intro hf hl
    by_cases he : i.castSucc = last
    · subst last
      exact A.endpoint_eq.trans B.endpoint_eq.symm
    · have hs : i.succ ≤ last := by
        apply Fin.le_iff_val_le_val.mpr
        have hlt : i.castSucc < last := lt_of_le_of_ne hl he
        exact Nat.succ_le_iff.mpr hlt
      have hp := A.crossing i hf hs
      have hq := B.crossing i hf hs
      have hn := ih (hf.trans (Fin.castSucc_lt_succ (i := i)).le) hs
      rw [hn] at hp
      exact (H.event i).regularCrossing_left_unique hp hq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.point_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.point_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.point_unique ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.point_unique

instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.instSubsingleton : Subsingleton (BackwardPointTrace H first last hle endpoint) := by
  constructor
  intro A B
  have hp : A.point = B.point := by
    funext j hf hl
    exact point_unique A B j hf hl
  cases A
  cases B
  cases hp
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.instSubsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.instSubsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.instSubsingleton ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.instSubsingleton

def singleton (H : ObservedHistory.{u}) (j : Fin (H.eventCount + 1))
    (endpoint : (H.stage j).Carrier) : BackwardPointTrace H j j le_rfl endpoint where
  point k hk hk' := (congrArg (fun i => (H.stage i).Carrier) (le_antisymm hk' hk).symm) ▸ endpoint
  endpoint_eq := rfl
  crossing i hf hl := by
    have hlt := Fin.castSucc_lt_succ (i := i)
    exact False.elim ((not_lt_of_ge (hl.trans hf)) hlt)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.singleton ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace.singleton

end BackwardPointTrace

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
