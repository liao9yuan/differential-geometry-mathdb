import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryIdentities

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem SamePresentation.activeStage {K : ObservedHistory.{u}}
    (R : H.SamePresentation K) (t : _root_.Set.Icc (0 : ℝ) H.horizon) :
    Fin.cast (congrArg (· + 1) R.count_eq) (H.activeStage t) =
      K.activeStage ⟨t.1, t.2.1, by rw [← R.horizon_eq]; exact t.2.2⟩ := by
  symm
  apply K.activeStage_eq_of_maximal
  · rw [← R.time_eq]
    exact H.activeStage_time_le t
  · intro k hk
    let j : Fin (H.eventCount + 1) := Fin.cast (congrArg (· + 1) R.count_eq.symm) k
    have hj : Fin.cast (congrArg (· + 1) R.count_eq) j = k := Fin.ext rfl
    have he := R.time_eq j
    rw [hj] at he
    have hle := H.le_activeStage t j (he.trans_le hk)
    exact hle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.activeStage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.activeStage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.activeStage ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.activeStage

theorem SamePresentation.restrict {K : ObservedHistory.{u}}
    (R : H.SamePresentation K) (t : _root_.Set.Icc (0 : ℝ) H.horizon) :
    (H.restrict t).SamePresentation
      (K.restrict ⟨t.1, t.2.1, by rw [← R.horizon_eq]; exact t.2.2⟩) := by
  let tK : _root_.Set.Icc (0 : ℝ) K.horizon :=
    ⟨t.1, t.2.1, by rw [← R.horizon_eq]; exact t.2.2⟩
  let S := H.restrict t
  let T := K.restrict tK
  have hc : S.eventCount = T.eventCount := congrArg Fin.val (SamePresentation.activeStage H R t)
  have htime (j : Fin (S.eventCount + 1)) :
      S.time j = T.time (Fin.cast (congrArg (· + 1) hc) j) := R.time_eq _
  refine {
    horizon_eq := rfl
    count_eq := hc
    time_eq := htime
    stage_eq := fun j => R.stage_eq _
    initialMetric_heq := fun j => R.initialMetric_heq _
    event_eq := fun i => R.event_eq _
    metric_heq := ?_ }
  intro j τ hτ
  have hdom : S.stageDomain j = T.stageDomain (Fin.cast (congrArg (· + 1) hc) j) := by
    cases j using Fin.lastCases with
    | last =>
      have hj : Fin.cast (congrArg (· + 1) hc) (Fin.last S.eventCount) =
          Fin.last T.eventCount := Fin.ext hc
      have he := htime (Fin.last S.eventCount)
      rw [hj] at he ⊢
      dsimp only [S, T] at he ⊢
      simp only [stageDomain, Fin.lastCases_last]
      exact congrArg₂ _root_.Set.Icc he rfl
    | cast i =>
      have hj : Fin.cast (congrArg (· + 1) hc) i.castSucc =
          (Fin.cast hc i).castSucc := Fin.ext rfl
      have hs : Fin.cast (congrArg (· + 1) hc) i.succ =
          (Fin.cast hc i).succ := Fin.ext rfl
      have hl := htime i.castSucc
      have hu := htime i.succ
      rw [hj] at hl ⊢
      rw [hs] at hu
      simp only [stageDomain, Fin.lastCases_castSucc]
      exact congrArg₂ _root_.Set.Ico hl hu
  have hτK : τ ∈ T.stageDomain (Fin.cast (congrArg (· + 1) hc) j) := by
    rw [← hdom]
    exact hτ
  have hτH := H.restrict_stageDomain_subset t j hτ
  have hm₁ := H.restrict_stageMetric t j τ hτ
  have hm₂ := R.metric_heq _ τ hτH
  have hm₃ := K.restrict_stageMetric tK
    (Fin.cast (congrArg (· + 1) hc) j) τ hτK
  exact (hm₁.trans hm₂).trans hm₃.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.restrict ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.restrict
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification

universe u
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {H K : ObservedHistory.{u}}

theorem restrict_heq (A : InitialIdentification P g H)
    (B : InitialIdentification P g K) (hmap : HEq A.map B.map)
    (t : _root_.Set.Icc (0 : ℝ) H.horizon) (s : _root_.Set.Icc (0 : ℝ) K.horizon) :
    HEq (A.restrict t).map (B.restrict s).map := hmap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.restrict_heq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.restrict_heq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.restrict_heq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.restrict_heq


theorem restrict_restrict_map (A : InitialIdentification P g H)
    (a : _root_.Set.Icc (0 : ℝ) H.horizon) (t : _root_.Set.Icc (0 : ℝ) (H.restrict a).horizon) :
    ((A.restrict a).restrict t).map =
      (A.restrict ⟨t.1, t.2.1, t.2.2.trans a.2.2⟩).map := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.restrict_restrict_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.restrict_restrict_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.restrict_restrict_map ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.restrict_restrict_map

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification
