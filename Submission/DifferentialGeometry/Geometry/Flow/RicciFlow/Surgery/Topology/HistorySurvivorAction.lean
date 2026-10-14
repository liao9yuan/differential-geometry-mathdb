import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFlow
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ReducedAction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.LocalPullback
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Basic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman

universe u

private theorem intervalIntegrable_lRegularizedLagrangian
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := M) D) (hS : IsSolutionOn S)
    (T a b : ℝ) (α : ℝ → M) (hα : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α)
    (hcarrier : ∀ s ∈ _root_.Set.uIcc a b, T - s ^ 2 ∈ D.carrier) :
    IntervalIntegrable (lRegularizedLagrangian S T α) _root_.MeasureTheory.MeasureSpace.volume a b := by
  have hmap : ContinuousOn (fun s : ℝ => (T, s)) (_root_.Set.uIcc a b) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hmaps : _root_.Set.MapsTo (fun s : ℝ => (T, s)) (_root_.Set.uIcc a b)
      {q : ℝ × ℝ | q.1 - q.2 ^ 2 ∈ D.carrier} := hcarrier
  have hc : ContinuousOn (lRegularizedLagrangian S T α) (_root_.Set.uIcc a b) :=
    (lRegularizedLagrangian_continuousOn_carrier (I := ThreeModel) (M := M) (D := D)
      S hS α hα).comp (f := fun s : ℝ => (T, s)) hmap hmaps
  exact ContinuousOn.intervalIntegrable (μ := _root_.MeasureTheory.MeasureSpace.volume) hc

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.intervalIntegrable_lRegularizedLagrangian
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.intervalIntegrable_lRegularizedLagrangian target :: scope.openDecls } }

variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)

theorem backwardSurvivorSlabMetric_before
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    {t : ℝ} (ht : t < H.time i.succ) :
    H.backwardSurvivorSlabMetric first last hle i hf hl t =
      localPullMetric ((H.event i).incoming.flow.base.metric t)
        (H.backwardSurvivorMap first last hle i.castSucc hf (i.castSucc_lt_succ.le.trans hl))
        (H.backwardSurvivorMap_isLocalDiffeomorph first last hle i.castSucc hf
          (i.castSucc_lt_succ.le.trans hl)) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [H.backwardSurvivorSlabMetric_inner,
    (H.event i).terminal.extendedMetric_before ht,
    SmoothRiemannianMetric.restrictOpen_inner, localPullMetric_inner]
  have hd := DifferentialGeometry.mfderiv_subtypeVal_comp (I := ThreeModel) (J := ThreeModel)
    (H.backwardSurvivorTerminalMap first last hle i hf hl) x
  change mfderiv ThreeModel ThreeModel
      (H.backwardSurvivorMap first last hle i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) x =
      mfderiv ThreeModel ThreeModel
        (H.backwardSurvivorTerminalMap first last hle i hf hl) x at hd
  rw [hd]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.backwardSurvivorSlabMetric_before then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.backwardSurvivorSlabMetric_before"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.backwardSurvivorSlabMetric_before ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.backwardSurvivorSlabMetric_before

theorem lRegularizedLagrangian_backwardSurvivorMap
    {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first last hle) D)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    (hmetric : ∀ t ∈ _root_.Set.Icc (H.time i.castSucc) (H.time i.succ),
      S.base.metric t = H.backwardSurvivorSlabMetric first last hle i hf hl t)
    (T : ℝ) {α : ℝ → H.backwardSurvivorDomain first last hle} {s : ℝ}
    (hα : MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel α s)
    (hs : T - s ^ 2 ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ)) :
    lRegularizedLagrangian S T α s =
      lRegularizedLagrangian (H.event i).incoming.flow T
        (H.backwardSurvivorMap first last hle i.castSucc hf
          (i.castSucc_lt_succ.le.trans hl) ∘ α) s := by
  let p := H.backwardSurvivorMap first last hle i.castSucc hf (i.castSucc_lt_succ.le.trans hl)
  let hp := H.backwardSurvivorMap_isLocalDiffeomorph first last hle i.castSucc hf
    (i.castSucc_lt_succ.le.trans hl)
  have hm : S.base.metric (T - s ^ 2) =
      ((H.event i).incoming.flow.localPullback p hp).base.metric (T - s ^ 2) :=
    (hmetric _ ⟨hs.1, hs.2.le⟩).trans
      (H.backwardSurvivorSlabMetric_before first last hle i hf hl hs.2)
  calc
    _ = lRegularizedLagrangian ((H.event i).incoming.flow.localPullback p hp) T α s := by
      unfold lRegularizedLagrangian SolutionOn.scalar SolutionFamily.scalar
      rw [hm]
    _ = _ := lRegularizedLagrangian_localPullback (H.event i).incoming.flow p hp T hα

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.lRegularizedLagrangian_backwardSurvivorMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.lRegularizedLagrangian_backwardSurvivorMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.lRegularizedLagrangian_backwardSurvivorMap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.lRegularizedLagrangian_backwardSurvivorMap

theorem lRegularizedAction_backwardSurvivorMap
    {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first last hle) D)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    (hmetric : ∀ t ∈ _root_.Set.Icc (H.time i.castSucc) (H.time i.succ),
      S.base.metric t = H.backwardSurvivorSlabMetric first last hle i hf hl t)
    (T : ℝ) {α : ℝ → H.backwardSurvivorDomain first last hle}
    (a b : ℝ) (hα : ∀ s ∈ _root_.Set.uIoo a b, MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel α s)
    (hslab : ∀ s ∈ _root_.Set.uIoo a b, T - s ^ 2 ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ)) :
    lRegularizedAction S T α a b =
      lRegularizedAction (H.event i).incoming.flow T
        (H.backwardSurvivorMap first last hle i.castSucc hf
          (i.castSucc_lt_succ.le.trans hl) ∘ α) a b := by
  unfold lRegularizedAction
  apply intervalIntegral.integral_congr_uIoo
  intro s hs
  exact H.lRegularizedLagrangian_backwardSurvivorMap first last hle S i hf hl hmetric T
    (hα s hs) (hslab s hs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.lRegularizedAction_backwardSurvivorMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.lRegularizedAction_backwardSurvivorMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.lRegularizedAction_backwardSurvivorMap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.lRegularizedAction_backwardSurvivorMap

theorem sum_lRegularizedAction_backwardSurvivorMap
    {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first last hle) D)
    (hS : IsSolutionOn S) (T : ℝ)
    (α : ℝ → H.backwardSurvivorDomain first last hle)
    (hα : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α)
    {n : ℕ} (t : ℕ → ℝ) (event : Fin n → Fin H.eventCount)
    (hf : ∀ k, first ≤ (event k).castSucc) (hl : ∀ k, (event k).succ ≤ last)
    (hmetric : ∀ k, ∀ u ∈ _root_.Set.Icc (H.time (event k).castSucc) (H.time (event k).succ),
      S.base.metric u = H.backwardSurvivorSlabMetric first last hle (event k) (hf k) (hl k) u)
    (hslab : ∀ k : Fin n, ∀ s ∈ _root_.Set.uIoo (t k.val) (t (k.val + 1)),
      T - s ^ 2 ∈ _root_.Set.Ico (H.time (event k).castSucc) (H.time (event k).succ))
    (hcarrier : ∀ k < n, ∀ s ∈ _root_.Set.uIcc (t k) (t (k + 1)), T - s ^ 2 ∈ D.carrier) :
    (∑ k : Fin n, lRegularizedAction (H.event (event k)).incoming.flow T
      (H.backwardSurvivorMap first last hle (event k).castSucc (hf k)
        ((event k).castSucc_lt_succ.le.trans (hl k)) ∘ α) (t k.val) (t (k.val + 1))) =
      lRegularizedAction S T α (t 0) (t n) := by
  have hint (k : ℕ) (hk : k < n) :
      IntervalIntegrable (lRegularizedLagrangian S T α) _root_.MeasureTheory.MeasureSpace.volume (t k) (t (k + 1)) := by
    exact intervalIntegrable_lRegularizedLagrangian S hS T (t k) (t (k + 1)) α hα
      (hcarrier k hk)
  calc
    _ = ∑ k : Fin n, lRegularizedAction S T α (t k.val) (t (k.val + 1)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact (H.lRegularizedAction_backwardSurvivorMap first last hle S
        (event k) (hf k) (hl k) (hmetric k) T (t k.val) (t (k.val + 1))
        (fun s _ => hα.mdifferentiable one_ne_zero s) (hslab k)).symm
    _ = lRegularizedAction S T α (t 0) (t n) := by
      rw [Fin.sum_univ_eq_sum_range (fun k => lRegularizedAction S T α (t k) (t (k + 1))) n]
      exact lRegularizedAction_sum S T α hint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.sum_lRegularizedAction_backwardSurvivorMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.sum_lRegularizedAction_backwardSurvivorMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.sum_lRegularizedAction_backwardSurvivorMap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.sum_lRegularizedAction_backwardSurvivorMap

omit hle in
theorem exists_backwardSurvivor_isSolutionOn_preserving_action (hlt : first < last) :
    ∃ S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first last hlt.le)
        (RealTimeInterval.closed (H.time first) (H.time last) (H.time_strictMono hlt).le),
      IsSolutionOn S ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∀ t ∈ _root_.Set.Icc (H.time i.castSucc) (H.time i.succ),
          S.base.metric t = H.backwardSurvivorSlabMetric first last hlt.le i hf hl t) ∧
      (∀ (j : Fin (H.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ last),
        S.base.metric (H.time j) = H.backwardSurvivorInitialMetric first last hlt.le j hj hl) ∧
      ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
        (T : ℝ) (α : ℝ → H.backwardSurvivorDomain first last hlt.le),
        ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α → ∀ a b : ℝ,
        (∀ s ∈ _root_.Set.uIoo a b, T - s ^ 2 ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ)) →
        lRegularizedAction S T α a b =
          lRegularizedAction (H.event i).incoming.flow T
            (H.backwardSurvivorMap first last hlt.le i.castSucc hf
              (i.castSucc_lt_succ.le.trans hl) ∘ α) a b := by
  obtain ⟨G, hslabs, hinitial, _, hS⟩ := H.exists_backwardSurvivor_isSolutionOn first last hlt
  let S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first last hlt.le)
      (RealTimeInterval.closed (H.time first) (H.time last) (H.time_strictMono hlt).le) :=
    { base := { metric := G } }
  refine ⟨S, hS, hslabs, hinitial, ?_⟩
  intro i hf hl T α hα a b hslab
  exact H.lRegularizedAction_backwardSurvivorMap first last hlt.le S i hf hl
    (hslabs i hf hl) T a b (fun s _ => hα.mdifferentiable one_ne_zero s) hslab

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_backwardSurvivor_isSolutionOn_preserving_action then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_backwardSurvivor_isSolutionOn_preserving_action"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_backwardSurvivor_isSolutionOn_preserving_action ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_backwardSurvivor_isSolutionOn_preserving_action

theorem reducedAction_backwardSurvivorMap
    {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first last hle) D)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    (hmetric : ∀ t ∈ _root_.Set.Icc (H.time i.castSucc) (H.time i.succ),
      S.base.metric t = H.backwardSurvivorSlabMetric first last hle i hf hl t)
    (T τ : ℝ) (hτ : 0 ≤ τ) (α : ℝ → H.backwardSurvivorDomain first last hle)
    (hα : ∀ s ∈ _root_.Set.Ioo 0 (Real.sqrt τ), MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel α s)
    (hslab : ∀ s ∈ _root_.Set.Ioo 0 (Real.sqrt τ),
      T - s ^ 2 ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ)) :
    reducedAction S.base.metric T τ (squareRootReparametrization α) =
      reducedAction (H.event i).incoming.flow.base.metric T τ
        (squareRootReparametrization
          (H.backwardSurvivorMap first last hle i.castSucc hf
            (i.castSucc_lt_succ.le.trans hl) ∘ α)) := by
  rw [reducedAction_eq_lLength, reducedAction_eq_lLength,
    lLength_squareRootReparametrization_eq_lRegularizedAction _ _ _ _ hτ,
    lLength_squareRootReparametrization_eq_lRegularizedAction _ _ _ _ hτ]
  exact H.lRegularizedAction_backwardSurvivorMap first last hle S i hf hl hmetric T
    0 (Real.sqrt τ) (by simpa only [_root_.Set.uIoo_of_le (Real.sqrt_nonneg τ)] using hα)
    (by simpa only [_root_.Set.uIoo_of_le (Real.sqrt_nonneg τ)] using hslab)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.reducedAction_backwardSurvivorMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.reducedAction_backwardSurvivorMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.reducedAction_backwardSurvivorMap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.reducedAction_backwardSurvivorMap

theorem reducedAction_eq_sum_stage_lLength
    {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first last hle) D)
    (hS : IsSolutionOn S) (T τ : ℝ) (hτ : 0 ≤ τ)
    (α : ℝ → H.backwardSurvivorDomain first last hle)
    (hα : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α)
    {n : ℕ} (t : ℕ → ℝ) (ht : ∀ k ≤ n, 0 ≤ t k)
    (hzero : t 0 = 0) (hlast : t n = Real.sqrt τ) (event : Fin n → Fin H.eventCount)
    (hf : ∀ k, first ≤ (event k).castSucc) (hl : ∀ k, (event k).succ ≤ last)
    (hmetric : ∀ k, ∀ u ∈ _root_.Set.Icc (H.time (event k).castSucc) (H.time (event k).succ),
      S.base.metric u = H.backwardSurvivorSlabMetric first last hle (event k) (hf k) (hl k) u)
    (hslab : ∀ k : Fin n, ∀ s ∈ _root_.Set.uIoo (t k.val) (t (k.val + 1)),
      T - s ^ 2 ∈ _root_.Set.Ico (H.time (event k).castSucc) (H.time (event k).succ))
    (hcarrier : ∀ k < n, ∀ s ∈ _root_.Set.uIcc (t k) (t (k + 1)), T - s ^ 2 ∈ D.carrier) :
    reducedAction S.base.metric T τ (squareRootReparametrization α) =
      ∑ k : Fin n, lLength (H.event (event k)).incoming.flow T
        (squareRootReparametrization
          (H.backwardSurvivorMap first last hle (event k).castSucc (hf k)
            ((event k).castSucc_lt_succ.le.trans (hl k)) ∘ α))
        ((t k.val) ^ 2) ((t (k.val + 1)) ^ 2) := by
  rw [reducedAction_eq_lLength,
    lLength_squareRootReparametrization_eq_lRegularizedAction _ _ _ _ hτ,
    ← hzero, ← hlast]
  rw [← H.sum_lRegularizedAction_backwardSurvivorMap first last hle S hS T α hα
    t event hf hl hmetric hslab hcarrier]
  apply Finset.sum_congr rfl
  intro k _
  exact (lLength_squareRootReparametrization_sq (H.event (event k)).incoming.flow T _
    (t k.val) (t (k.val + 1)) (ht k.val k.isLt.le) (ht (k.val + 1) k.isLt)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.reducedAction_eq_sum_stage_lLength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.reducedAction_eq_sum_stage_lLength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.reducedAction_eq_sum_stage_lLength ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.reducedAction_eq_sum_stage_lLength

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

theorem exists_backwardSurvivor_isSolutionOn_action_mem_history
    (first last : Fin (H.eventCount + 1)) (hlt : first < last) :
    ∃ S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first last hlt.le)
        (RealTimeInterval.closed (H.time first) (H.time last) (H.time_strictMono hlt).le),
      IsSolutionOn S ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∀ t ∈ _root_.Set.Icc (H.time i.castSucc) (H.time i.succ),
          S.base.metric t = H.backwardSurvivorSlabMetric first last hlt.le i hf hl t) ∧
      (∀ (j : Fin (H.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ last),
        S.base.metric (H.time j) = H.backwardSurvivorInitialMetric first last hlt.le j hj hl) ∧
      ∀ γ : ℝ → H.backwardSurvivorDomain first last hlt.le,
        ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ →
        lRegularizedAction S (H.time last) γ 0 (Real.sqrt (H.time last - H.time first)) ∈
          H.regularizedC1ActionValues first last hlt.le (H.time last) 0
            (Real.sqrt (H.time last - H.time first)) (γ 0).val
            (H.backwardSurvivorMap first last hlt.le first le_rfl hlt.le
              (γ (Real.sqrt (H.time last - H.time first)))) := by
  obtain ⟨S, hS, hslabs, hinitial, _⟩ := H.exists_backwardSurvivor_isSolutionOn_preserving_action first last hlt
  refine ⟨S, hS, hslabs, hinitial, ?_⟩
  intro γ hγ
  let T := H.time last
  let v := Real.sqrt (H.time last - H.time first)
  have hv : 0 ≤ v := Real.sqrt_nonneg _
  have hv2 : v ^ 2 = H.time last - H.time first := Real.sq_sqrt (sub_nonneg.mpr (H.time_strictMono hlt).le)
  have hupper : T - (0 : ℝ) ^ 2 ∈ _root_.Set.Icc (H.time last) (H.stageEndTime last) := by
    simp only [zero_pow two_ne_zero, sub_zero, T]
    exact ⟨le_rfl, H.time_le_stageEndTime last⟩
  have hlower : T - v ^ 2 ∈ H.stageDomain first := by
    rw [hv2]
    simpa only [T, sub_sub_cancel] using H.time_mem_stageDomain first
  let f : (j : H.StageInterval first last) → H.backwardSurvivorDomain first last hlt.le → (H.stage j.val).Carrier :=
    fun j => H.backwardSurvivorMap first last hlt.le j.val j.property.1 j.property.2
  have hf (j : H.StageInterval first last) : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j) :=
    H.backwardSurvivorMap_isLocalDiffeomorph first last hlt.le j.val j.property.1 j.property.2
  have hmetric (j : H.StageInterval first last)
      (t : ℝ) (ht : t ∈ _root_.Set.Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) :
      S.base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2)) (f j) (hf j) := by
    by_cases hjlast : j.val = last
    · have he : H.regularizedStageEnd T v j.val = 0 := by
        rw [hjlast, regularizedStageEnd]
        simp only [T, max_eq_right (sub_le_self _ (sq_nonneg v)), sub_self, Real.sqrt_zero]
      have hs : 0 ≤ H.regularizedStageStart T 0 j.val := Real.sqrt_nonneg _
      rw [he] at ht
      exact False.elim ((not_lt_of_ge hs) (ht.1.trans ht.2))
    · have hjlt : j.val < last := lt_of_le_of_ne j.property.2 hjlast
      obtain ⟨i, hi⟩ : ∃ i : Fin H.eventCount, j.val = i.castSucc := by
        have hjN : j.val.val < H.eventCount := lt_of_lt_of_le hjlt (Fin.le_last last)
        exact ⟨⟨j.val.val, hjN⟩, Fin.ext rfl⟩
      rcases j with ⟨j, hjfirst, hjlast'⟩
      dsimp only at hi
      subst j
      have hiLast : i.succ ≤ last := hjlt
      have hstage := H.mapsTo_regularizedStage_Ioo T 0 v i.castSucc ht
      simp only [stageDomain, Fin.lastCases_castSucc, _root_.Set.mem_Ico] at hstage
      have hh := (hslabs i hjfirst hiLast _ ⟨hstage.1, hstage.2.le⟩).trans
        (H.backwardSurvivorSlabMetric_before first last hlt.le i hjfirst hiLast hstage.2)
      simpa only [stageMetric, Fin.lastCases_castSucc, f] using hh
  have hmem := H.action_mem_regularizedC1ActionValues_of_common_curve first last hlt.le f hf
    (fun i hi hl z => H.backwardSurvivorMap_crossing first last hlt.le i hi hl z) S hS T le_rfl hv
    hupper hlower (fun t ht => by
      change H.time first ≤ T - t ^ 2 ∧ T - t ^ 2 ≤ H.time last
      have ht2 := (sq_le_sq₀ ht.1 hv).mpr ht.2
      rw [hv2] at ht2
      constructor <;> dsimp only [T] <;> nlinarith [sq_nonneg t]) hmetric γ hγ
  simpa only [f, backwardSurvivorMap_last] using hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_backwardSurvivor_isSolutionOn_action_mem_history then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_backwardSurvivor_isSolutionOn_action_mem_history"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_backwardSurvivor_isSolutionOn_action_mem_history ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_backwardSurvivor_isSolutionOn_action_mem_history

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
