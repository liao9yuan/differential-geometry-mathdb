import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ActualWidth
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ObservedComparisonRecord

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter _root_.Submission.Filter
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Topology _root_.Submission.Topology _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

universe u

theorem historyStageAt_eq_last (H : ObservedHistory.{u}) (t : _root_.Set.Icc (0 : ℝ) H.horizon)
    (ht : H.time (Fin.last H.eventCount) ≤ t.1) :
    historyStageAt H t = Fin.last H.eventCount := by
  apply le_antisymm (Fin.le_last _)
  apply Finset.le_max'
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.historyStageAt_eq_last then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.historyStageAt_eq_last"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.historyStageAt_eq_last ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.historyStageAt_eq_last

theorem historyWidth_final (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    (hfin : H.time (Fin.last H.eventCount) < H.horizon)
    (t : _root_.Set.Icc (0 : ℝ) H.horizon) (ht : H.time (Fin.last H.eventCount) ≤ t.1) :
    historyWidth H h0 terminal t =
      componentWidth (H.stage (Fin.last H.eventCount))
        ((H.finalSlab hfin).flow.base.metric t.1)
        ((rfs_finite_ancestor_chain H terminal).component (Fin.last H.eventCount))
        (rfs_simply_connected_history H h0 (Fin.last H.eventCount) _) := by
  change componentWidth (H.stage (historyStageAt H t))
      (historyStageMetric H (historyStageAt H t) t.1)
      ((rfs_finite_ancestor_chain H terminal).component (historyStageAt H t))
      (rfs_simply_connected_history H h0 (historyStageAt H t) _) = _
  rw [historyStageAt_eq_last H t ht]
  simp only [historyStageMetric, Fin.lastCases_last, dif_pos hfin]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.historyWidth_final then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Width.historyWidth_final"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Width.historyWidth_final ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width.historyWidth_final

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width

universe u

theorem two_mul_le_componentHalfScalar (P : OrientedThreeStage.{u})
    (F : SolutionFamily (I := ThreeModel) (M := P.Carrier))
    (p : ConnectedComponents P.Carrier) (t a : ℝ)
    (h : ∀ x : (P.component p).Carrier, 2 * a ≤ F.scalar t x.1) :
    a ≤ componentHalfScalar P F p t := by
  let : ConnectedSpace (P.component p).Carrier := P.component_connected p
  have hle : 2 * a ≤ _root_.InfSet.sInf (Set.range (fun x : (P.component p).Carrier => F.scalar t x.1)) :=
    le_csInf (Set.range_nonempty _) (by rintro _ ⟨x, rfl⟩; exact h x)
  have h2 : a ≤ _root_.InfSet.sInf (Set.range (fun x : (P.component p).Carrier => F.scalar t x.1)) / 2 := by
    linarith
  simpa only [componentHalfScalar] using h2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.two_mul_le_componentHalfScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.two_mul_le_componentHalfScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.two_mul_le_componentHalfScalar ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.two_mul_le_componentHalfScalar

theorem componentHalfScalar_congr (P : OrientedThreeStage.{u})
    (p : ConnectedComponents P.Carrier) (t : ℝ)
    {F G : SolutionFamily (I := ThreeModel) (M := P.Carrier)}
    (h : ∀ s, F.metric s = G.metric s) :
    componentHalfScalar P F p t = componentHalfScalar P G p t := by
  simp only [componentHalfScalar, SolutionFamily.scalar, h t]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentHalfScalar_congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentHalfScalar_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentHalfScalar_congr ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentHalfScalar_congr

theorem componentHalfScalar_le_of_scalarLowerBound {H : ObservedHistory.{u}}
    {terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier} {c : ℝ}
    (hc : 0 < c) (hscalar : HistoryScalarLowerBound H c)
    (t : _root_.Set.Icc (0 : ℝ) H.horizon) (htE : t.1 ∉ H.eventTimes) :
    -3 / (4 * (t.1 + c)) ≤
      componentHalfScalar (H.stage (historyStageAt H t))
        ⟨historyStageMetric H (historyStageAt H t)⟩
        ((rfs_finite_ancestor_chain H terminal).component (historyStageAt H t)) t.1 := by
  refine two_mul_le_componentHalfScalar (H.stage (historyStageAt H t))
    ⟨historyStageMetric H (historyStageAt H t)⟩
    ((rfs_finite_ancestor_chain H terminal).component (historyStageAt H t)) t.1
    (-3 / (4 * (t.1 + c))) ?_
  intro x
  have hx := hscalar t htE x.1
  have harith : (2 : ℝ) * (-3 / (4 * (t.1 + c))) = -3 / (2 * (t.1 + c)) := by
    have hx0 : t.1 + c ≠ 0 := ne_of_gt (by linarith [t.2.1, hc])
    field_simp
    ring
  rw [harith]
  exact hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentHalfScalar_le_of_scalarLowerBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentHalfScalar_le_of_scalarLowerBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentHalfScalar_le_of_scalarLowerBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentHalfScalar_le_of_scalarLowerBound

theorem componentHalfScalar_le_of_scalarLowerBound_incoming {H : ObservedHistory.{u}}
    {terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier} {c : ℝ}
    (hc : 0 < c) (hscalar : HistoryScalarLowerBound H c) (i : Fin H.eventCount)
    {t : ℝ} (ht : t ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ)) (htE : t ∉ H.eventTimes) :
    -3 / (4 * (t + c)) ≤
      componentHalfScalar (H.stage i.castSucc) (H.event i).incoming.flow.base
        ((rfs_finite_ancestor_chain H terminal).component i.castSucc) t := by
  have htIcc : t ∈ _root_.Set.Icc (0 : ℝ) H.horizon :=
    ⟨le_trans (le_of_eq H.time_zero.symm)
        (le_trans (H.time_strictMono.monotone (Fin.zero_le _)) ht.1),
      le_trans ht.2.le (le_trans (H.time_strictMono.monotone (Fin.le_last _)) H.time_le_horizon)⟩
  have hstage : historyStageAt H (⟨t, htIcc⟩ : _root_.Set.Icc (0 : ℝ) H.horizon) = i.castSucc :=
    historyStageAt_of_mem_incoming H i ⟨t, htIcc⟩ ht
  have h0 := componentHalfScalar_le_of_scalarLowerBound (H := H) (terminal := terminal) (c := c)
    hc hscalar (⟨t, htIcc⟩ : _root_.Set.Icc (0 : ℝ) H.horizon) htE
  rw [hstage] at h0
  refine h0.trans (le_of_eq ?_)
  refine (componentHalfScalar_congr (H.stage i.castSucc)
    ((rfs_finite_ancestor_chain H terminal).component i.castSucc)
    (↑(⟨t, htIcc⟩ : _root_.Set.Icc (0 : ℝ) H.horizon)) ?_).symm
  intro s
  simp only [historyStageMetric, Fin.lastCases_castSucc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentHalfScalar_le_of_scalarLowerBound_incoming then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentHalfScalar_le_of_scalarLowerBound_incoming"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentHalfScalar_le_of_scalarLowerBound_incoming ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentHalfScalar_le_of_scalarLowerBound_incoming

theorem componentHalfScalar_le_of_scalarLowerBound_final {H : ObservedHistory.{u}}
    {terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier} {c : ℝ}
    (hc : 0 < c) (hscalar : HistoryScalarLowerBound H c)
    (hfin : H.time (Fin.last H.eventCount) < H.horizon)
    {t : ℝ} (ht : t ∈ _root_.Set.Icc (H.time (Fin.last H.eventCount)) H.horizon)
    (htE : t ∉ H.eventTimes) :
    -3 / (4 * (t + c)) ≤
      componentHalfScalar (H.stage (Fin.last H.eventCount)) (H.finalSlab hfin).flow.base
        ((rfs_finite_ancestor_chain H terminal).component (Fin.last H.eventCount)) t := by
  have htIcc : t ∈ _root_.Set.Icc (0 : ℝ) H.horizon :=
    ⟨le_trans (le_of_eq H.time_zero.symm)
        (le_trans (H.time_strictMono.monotone (Fin.zero_le _)) ht.1),
      ht.2⟩
  have hstage : historyStageAt H (⟨t, htIcc⟩ : _root_.Set.Icc (0 : ℝ) H.horizon) =
      Fin.last H.eventCount := historyStageAt_eq_last H ⟨t, htIcc⟩ ht.1
  have h0 := componentHalfScalar_le_of_scalarLowerBound (H := H) (terminal := terminal) (c := c)
    hc hscalar (⟨t, htIcc⟩ : _root_.Set.Icc (0 : ℝ) H.horizon) htE
  rw [hstage] at h0
  refine h0.trans (le_of_eq ?_)
  refine (componentHalfScalar_congr (H.stage (Fin.last H.eventCount))
    ((rfs_finite_ancestor_chain H terminal).component (Fin.last H.eventCount))
    (↑(⟨t, htIcc⟩ : _root_.Set.Icc (0 : ℝ) H.horizon)) ?_).symm
  intro s
  simp only [historyStageMetric, Fin.lastCases_last, dif_pos hfin]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentHalfScalar_le_of_scalarLowerBound_final then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentHalfScalar_le_of_scalarLowerBound_final"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentHalfScalar_le_of_scalarLowerBound_final ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.componentHalfScalar_le_of_scalarLowerBound_final

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width

universe u

theorem slopeBound_of_halfScalarBound {W : ℝ → ℝ} {t c ρ : ℝ} (hWt : 0 ≤ W t)
    (hρ : -3 / (4 * (t + c)) ≤ ρ)
    (h : ∀ ε > 0, ∃ δ > 0, ∀ h ∈ _root_.Set.Ioo (0 : ℝ) δ,
      (W (t + h) - W t) / h ≤ -2 * Real.pi - ρ * W t + ε) :
    ∀ ε > 0, ∃ δ > 0, ∀ h ∈ _root_.Set.Ioo (0 : ℝ) δ,
      (W (t + h) - W t) / h ≤ -2 * Real.pi - (-3 / (4 * (t + c))) * W t + ε := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := h ε hε
  refine ⟨δ, hδ, fun h hh => (hb h hh).trans ?_⟩
  have hmul : (-3 / (4 * (t + c))) * W t ≤ ρ * W t := mul_le_mul_of_nonneg_right hρ hWt
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.slopeBound_of_halfScalarBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.slopeBound_of_halfScalarBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.slopeBound_of_halfScalarBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.slopeBound_of_halfScalarBound

theorem observedHistoryWidthValue_upperRightDiniLE_of_slabIncrementBounds
    (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    {c : ℝ} (hc : 0 < c)
    (hscalar : HistoryScalarLowerBound H c)
    (hinc : ∀ (i : Fin H.eventCount)
        (p : ConnectedComponents (H.stage i.castSucc).Carrier)
        (hSC : SimplyConnectedSpace ((H.stage i.castSucc).component p).Carrier),
        ∀ t ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ), ∀ ε > 0, ∃ δ > 0,
          ∀ h ∈ _root_.Set.Ioo (0 : ℝ) δ, t + h < H.time i.succ →
            (componentWidth (H.stage i.castSucc)
                ((H.event i).incoming.flow.base.metric (t + h)) p hSC -
              componentWidth (H.stage i.castSucc)
                ((H.event i).incoming.flow.base.metric t) p hSC) / h ≤
              -2 * Real.pi - componentHalfScalar (H.stage i.castSucc)
                (H.event i).incoming.flow.base p t *
                componentWidth (H.stage i.castSucc)
                  ((H.event i).incoming.flow.base.metric t) p hSC + ε)
    (hclosed : ∀ (hfin : H.time (Fin.last H.eventCount) < H.horizon)
        (p : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
        (hSC : SimplyConnectedSpace
          ((H.stage (Fin.last H.eventCount)).component p).Carrier),
        ∀ t ∈ _root_.Set.Ico (H.time (Fin.last H.eventCount)) H.horizon, ∀ ε > 0, ∃ δ > 0,
          ∀ h ∈ _root_.Set.Ioo (0 : ℝ) δ, t + h ≤ H.horizon →
            (componentWidth (H.stage (Fin.last H.eventCount))
                ((H.finalSlab hfin).flow.base.metric (t + h)) p hSC -
              componentWidth (H.stage (Fin.last H.eventCount))
                ((H.finalSlab hfin).flow.base.metric t) p hSC) / h ≤
              -2 * Real.pi - componentHalfScalar (H.stage (Fin.last H.eventCount))
                (H.finalSlab hfin).flow.base p t *
                componentWidth (H.stage (Fin.last H.eventCount))
                  ((H.finalSlab hfin).flow.base.metric t) p hSC + ε) :
    ∀ t ∈ _root_.Set.Ico (0 : ℝ) H.horizon, t ∉ H.eventTimes →
      UpperRightDiniLE (observedHistoryWidthValue H h0 terminal) t
        (-2 * Real.pi + 3 * observedHistoryWidthValue H h0 terminal t / (4 * (t + c))) := by
  intro t htm htE
  have htIcc : t ∈ _root_.Set.Icc (0 : ℝ) H.horizon := ⟨htm.1, htm.2.le⟩
  let T : _root_.Set.Icc (0 : ℝ) H.horizon := ⟨t, htIcc⟩
  have hclamp_t : horizonClamp H.horizon t = t := horizonClamp_eq_self htIcc
  have hmem_ev : ∀ᶠ s in 𝓝[>] t, s ∈ _root_.Set.Icc (0 : ℝ) H.horizon := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [eventually_lt_nhds htm.2] with s hs
    exact fun hs' => ⟨htm.1.trans hs'.le, hs.le⟩
  have htend : _root_.Filter.Tendsto (fun s : ℝ => (⟨horizonClamp H.horizon s,
      horizonClamp_mem H.horizon_nonneg s⟩ : _root_.Set.Icc (0 : ℝ) H.horizon)) (𝓝[>] t) (𝓝 T) := by
    have h := (continuousAt_horizonClamp_subtype H.horizon_nonneg t).mono_left
      (show 𝓝[>] t ≤ 𝓝 t from nhdsWithin_le_nhds)
    rw [show (fun s : ℝ => (⟨horizonClamp H.horizon s,
        horizonClamp_mem H.horizon_nonneg s⟩ : _root_.Set.Icc (0 : ℝ) H.horizon)) t = T from
      Subtype.ext hclamp_t] at h
    exact h
  have hmem_Ici : ∀ᶠ s in 𝓝[>] t, (⟨horizonClamp H.horizon s,
      horizonClamp_mem H.horizon_nonneg s⟩ : _root_.Set.Icc (0 : ℝ) H.horizon) ∈ _root_.Set.Ici T := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    change t ≤ horizonClamp H.horizon s
    calc t = horizonClamp H.horizon t := hclamp_t.symm
      _ ≤ horizonClamp H.horizon s := max_le_max le_rfl (min_le_min hs.le le_rfl)
  have htend' : _root_.Filter.Tendsto (fun s : ℝ => (⟨horizonClamp H.horizon s,
      horizonClamp_mem H.horizon_nonneg s⟩ : _root_.Set.Icc (0 : ℝ) H.horizon)) (𝓝[>] t)
      (𝓝[_root_.Set.Ici T] T) :=
    tendsto_nhdsWithin_iff.mpr ⟨htend, hmem_Ici⟩
  have hstage_ev : ∀ᶠ s in 𝓝[>] t, historyStageAt H (⟨horizonClamp H.horizon s,
      horizonClamp_mem H.horizon_nonneg s⟩ : _root_.Set.Icc (0 : ℝ) H.horizon) =
      historyStageAt H T :=
    htend'.eventually (historyStageAt_eventually_eq_right H T)
  rcases Fin.eq_castSucc_or_eq_last (historyStageAt H T) with ⟨i, hi⟩ | hi
  · have hdomain : t ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ) := by
      have hm := historyStageAt_mem H T
      rw [hi] at hm
      simpa only [historyStageDomain, Fin.lastCases_castSucc] using hm
    let W : ℝ → ℝ := fun s => componentWidth (H.stage i.castSucc)
      ((H.event i).incoming.flow.base.metric (horizonClamp H.horizon s))
      ((rfs_finite_ancestor_chain H terminal).component i.castSucc)
      (rfs_simply_connected_history H h0 i.castSucc
        ((rfs_finite_ancestor_chain H terminal).component i.castSucc))
    have hWt : 0 ≤ W t := by
      simp only [W]
      exact componentWidth_nonneg _ _ _ _
    have hVW : observedHistoryWidthValue H h0 terminal =ᶠ[𝓝[>] t] W := by
      filter_upwards [hmem_ev, hstage_ev] with s hmem hs
      have hΦ : (⟨horizonClamp H.horizon s, horizonClamp_mem H.horizon_nonneg s⟩ :
          Icc (0 : ℝ) H.horizon) = ⟨s, hmem⟩ := Subtype.ext (horizonClamp_eq_self hmem)
      have hs' : historyStageAt H (⟨s, hmem⟩ : _root_.Set.Icc (0 : ℝ) H.horizon) = i.castSucc := by
        rw [← hΦ, hs, hi]
      have hIco : s ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ) := by
        have hmem' := historyStageAt_mem H (⟨s, hmem⟩ : _root_.Set.Icc (0 : ℝ) H.horizon)
        rw [hs'] at hmem'
        simpa only [historyStageDomain, Fin.lastCases_castSucc] using hmem'
      change historyWidth H h0 terminal (⟨horizonClamp H.horizon s,
        horizonClamp_mem H.horizon_nonneg s⟩ : _root_.Set.Icc (0 : ℝ) H.horizon) = W s
      simp only [W]
      rw [hΦ, historyWidth_incoming H h0 terminal i ⟨s, hmem⟩ hIco, horizonClamp_eq_self hmem]
    have hVt : observedHistoryWidthValue H h0 terminal t = W t := by
      have hT : (⟨horizonClamp H.horizon t, horizonClamp_mem H.horizon_nonneg t⟩ :
          Icc (0 : ℝ) H.horizon) = T := Subtype.ext hclamp_t
      change historyWidth H h0 terminal (⟨horizonClamp H.horizon t,
        horizonClamp_mem H.horizon_nonneg t⟩ : _root_.Set.Icc (0 : ℝ) H.horizon) = W t
      simp only [W]
      rw [hT, historyWidth_incoming H h0 terminal i T hdomain, hclamp_t]
    have hbound : ∀ ε > 0, ∃ δ > 0, ∀ h ∈ _root_.Set.Ioo (0 : ℝ) δ,
        (W (t + h) - W t) / h ≤ -2 * Real.pi - (-3 / (4 * (t + c))) * W t + ε := by
      intro ε hε
      obtain ⟨δ, hδ, hb⟩ := hinc i
        ((rfs_finite_ancestor_chain H terminal).component i.castSucc)
        (rfs_simply_connected_history H h0 i.castSucc
          ((rfs_finite_ancestor_chain H terminal).component i.castSucc)) t hdomain ε hε
      refine ⟨min δ (H.time i.succ - t), lt_min hδ (by linarith [hdomain.2]), ?_⟩
      intro h hh
      have hh1 : h < δ := hh.2.trans_le (min_le_left _ _)
      have hh2 : t + h < H.time i.succ := by
        have := hh.2.trans_le (min_le_right _ _)
        linarith
      have hstep := hb h ⟨hh.1, hh1⟩ hh2
      have hhmem : t + h ∈ _root_.Set.Icc (0 : ℝ) H.horizon :=
        ⟨by linarith [htm.1, hh.1],
          hh2.le.trans (le_trans (H.time_strictMono.monotone (Fin.le_last _)) H.time_le_horizon)⟩
      have hstep' : (W (t + h) - W t) / h ≤
          -2 * Real.pi - componentHalfScalar (H.stage i.castSucc)
            (H.event i).incoming.flow.base
            ((rfs_finite_ancestor_chain H terminal).component i.castSucc) t * W t + ε := by
        simp only [W, horizonClamp_eq_self hhmem, hclamp_t]
        exact hstep
      refine hstep'.trans ?_
      have hhalf : -3 / (4 * (t + c)) ≤ componentHalfScalar (H.stage i.castSucc)
          (H.event i).incoming.flow.base
          ((rfs_finite_ancestor_chain H terminal).component i.castSucc) t :=
        componentHalfScalar_le_of_scalarLowerBound_incoming (terminal := terminal)
          hc hscalar i hdomain htE
      have hmul := mul_le_mul_of_nonneg_right hhalf hWt
      linarith
    exact upperRightDiniLE_of_incrementBound hc htm.1 hVW hVt hWt le_rfl hbound
  · have hdomain : t ∈ _root_.Set.Icc (H.time (Fin.last H.eventCount)) H.horizon := by
      have hm := historyStageAt_mem H T
      rw [hi] at hm
      simpa only [historyStageDomain, Fin.lastCases_last] using hm
    have hfin : H.time (Fin.last H.eventCount) < H.horizon := lt_of_le_of_lt hdomain.1 htm.2
    let W : ℝ → ℝ := fun s => componentWidth (H.stage (Fin.last H.eventCount))
      ((H.finalSlab hfin).flow.base.metric (horizonClamp H.horizon s))
      ((rfs_finite_ancestor_chain H terminal).component (Fin.last H.eventCount))
      (rfs_simply_connected_history H h0 (Fin.last H.eventCount)
        ((rfs_finite_ancestor_chain H terminal).component (Fin.last H.eventCount)))
    have hWt : 0 ≤ W t := by
      simp only [W]
      exact componentWidth_nonneg _ _ _ _
    have hVW : observedHistoryWidthValue H h0 terminal =ᶠ[𝓝[>] t] W := by
      filter_upwards [hmem_ev, hstage_ev] with s hmem hs
      have hΦ : (⟨horizonClamp H.horizon s, horizonClamp_mem H.horizon_nonneg s⟩ :
          Icc (0 : ℝ) H.horizon) = ⟨s, hmem⟩ := Subtype.ext (horizonClamp_eq_self hmem)
      have hs' : historyStageAt H (⟨s, hmem⟩ : _root_.Set.Icc (0 : ℝ) H.horizon) =
          Fin.last H.eventCount := by
        rw [← hΦ, hs, hi]
      have hle : H.time (Fin.last H.eventCount) ≤ s := by
        have hmem' := historyStageAt_mem H (⟨s, hmem⟩ : _root_.Set.Icc (0 : ℝ) H.horizon)
        rw [hs'] at hmem'
        have hmem'' := hmem'
        simp only [historyStageDomain, Fin.lastCases_last, Set.mem_Icc] at hmem''
        exact hmem''.1
      change historyWidth H h0 terminal (⟨horizonClamp H.horizon s,
        horizonClamp_mem H.horizon_nonneg s⟩ : _root_.Set.Icc (0 : ℝ) H.horizon) = W s
      simp only [W]
      rw [hΦ, historyWidth_final H h0 terminal hfin ⟨s, hmem⟩ hle, horizonClamp_eq_self hmem]
    have hVt : observedHistoryWidthValue H h0 terminal t = W t := by
      have hT : (⟨horizonClamp H.horizon t, horizonClamp_mem H.horizon_nonneg t⟩ :
          Icc (0 : ℝ) H.horizon) = T := Subtype.ext hclamp_t
      change historyWidth H h0 terminal (⟨horizonClamp H.horizon t,
        horizonClamp_mem H.horizon_nonneg t⟩ : _root_.Set.Icc (0 : ℝ) H.horizon) = W t
      simp only [W]
      rw [hT, historyWidth_final H h0 terminal hfin T hdomain.1, hclamp_t]
    have hbound : ∀ ε > 0, ∃ δ > 0, ∀ h ∈ _root_.Set.Ioo (0 : ℝ) δ,
        (W (t + h) - W t) / h ≤ -2 * Real.pi - (-3 / (4 * (t + c))) * W t + ε := by
      intro ε hε
      obtain ⟨δ, hδ, hb⟩ := hclosed hfin
        ((rfs_finite_ancestor_chain H terminal).component (Fin.last H.eventCount))
        (rfs_simply_connected_history H h0 (Fin.last H.eventCount)
          ((rfs_finite_ancestor_chain H terminal).component (Fin.last H.eventCount)))
        t ⟨hdomain.1, htm.2⟩ ε hε
      refine ⟨min δ (H.horizon - t), lt_min hδ (by linarith [htm.2]), ?_⟩
      intro h hh
      have hh1 : h < δ := hh.2.trans_le (min_le_left _ _)
      have hh2 : t + h ≤ H.horizon := by
        have := hh.2.trans_le (min_le_right _ _)
        linarith
      have hstep := hb h ⟨hh.1, hh1⟩ hh2
      have hhmem : t + h ∈ _root_.Set.Icc (0 : ℝ) H.horizon := ⟨by linarith [htm.1, hh.1], hh2⟩
      have hstep' : (W (t + h) - W t) / h ≤
          -2 * Real.pi - componentHalfScalar (H.stage (Fin.last H.eventCount))
            (H.finalSlab hfin).flow.base
            ((rfs_finite_ancestor_chain H terminal).component (Fin.last H.eventCount)) t * W t +
            ε := by
        simp only [W, horizonClamp_eq_self hhmem, hclamp_t]
        exact hstep
      refine hstep'.trans ?_
      have hhalf : -3 / (4 * (t + c)) ≤ componentHalfScalar (H.stage (Fin.last H.eventCount))
          (H.finalSlab hfin).flow.base
          ((rfs_finite_ancestor_chain H terminal).component (Fin.last H.eventCount)) t :=
        componentHalfScalar_le_of_scalarLowerBound_final (terminal := terminal)
          hc hscalar hfin hdomain htE
      have hmul := mul_le_mul_of_nonneg_right hhalf hWt
      linarith
    exact upperRightDiniLE_of_incrementBound hc htm.1 hVW hVt hWt le_rfl hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.observedHistoryWidthValue_upperRightDiniLE_of_slabIncrementBounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.observedHistoryWidthValue_upperRightDiniLE_of_slabIncrementBounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.observedHistoryWidthValue_upperRightDiniLE_of_slabIncrementBounds ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.observedHistoryWidthValue_upperRightDiniLE_of_slabIncrementBounds

theorem observedHistoryWidthValue_upperRightDiniLE_of_historyIncoming
    (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    {c : ℝ} (hc : 0 < c)
    (hscalar : HistoryScalarLowerBound H c) :
    ∀ t ∈ _root_.Set.Ico (0 : ℝ) H.horizon, t ∉ H.eventTimes →
      UpperRightDiniLE (observedHistoryWidthValue H h0 terminal) t
        (-2 * Real.pi + 3 * observedHistoryWidthValue H h0 terminal t / (4 * (t + c))) :=
  observedHistoryWidthValue_upperRightDiniLE_of_slabIncrementBounds H h0 terminal hc hscalar
    (fun i p hSC => history_incoming_component_dini H i p hSC)
    (fun hfin p hSC => (closed_component_smooth_width (H.finalSlab hfin) p hSC).2.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.observedHistoryWidthValue_upperRightDiniLE_of_historyIncoming then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.observedHistoryWidthValue_upperRightDiniLE_of_historyIncoming"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.observedHistoryWidthValue_upperRightDiniLE_of_historyIncoming ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.observedHistoryWidthValue_upperRightDiniLE_of_historyIncoming

theorem observedComparisonRecord_of_historyWidth_of_scalarLowerBound
    (H : ObservedHistory.{u})
    (h0 : ∀ c : ConnectedComponents (H.stage 0).Carrier,
      SimplyConnectedSpace ((H.stage 0).component c).Carrier)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    {c A : ℝ} (hc : 0 < c) (hHpos : 0 < H.horizon)
    (hscalar : HistoryScalarLowerBound H c)
    (hinitial : Extinction.Width.historyWidth H h0 terminal
      (Extinction.Width.historyStageTime H 0) ≤ A)
    (hcont : ∀ t : _root_.Set.Icc (0 : ℝ) H.horizon, t.1 ∉ H.eventTimes →
      ContinuousAt (Extinction.Width.historyWidth H h0 terminal) t)
    (hrcont : ∀ i : Fin H.eventCount, H.time i.succ < H.horizon →
      ContinuousWithinAt (Extinction.Width.historyWidth H h0 terminal)
        (_root_.Set.Ici (Extinction.Width.historyStageTime H i.succ))
        (Extinction.Width.historyStageTime H i.succ))
    (hjump : ∀ i : Fin H.eventCount,
      ENNReal.ofReal (Extinction.Width.historyWidth H h0 terminal
          (Extinction.Width.historyStageTime H i.succ)) ≤
        _root_.Filter.liminf (fun t : _root_.Set.Icc (0 : ℝ) H.horizon =>
          ENNReal.ofReal (Extinction.Width.historyWidth H h0 terminal t))
          (𝓝[<] (Extinction.Width.historyStageTime H i.succ))) :
    Nonempty (ObservedComparisonRecord H c A) :=
  observedComparisonRecord_of_historyWidth H h0 terminal hc hHpos hinitial hcont hrcont hjump
    (observedHistoryWidthValue_upperRightDiniLE_of_historyIncoming H h0 terminal hc hscalar)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.observedComparisonRecord_of_historyWidth_of_scalarLowerBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.observedComparisonRecord_of_historyWidth_of_scalarLowerBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.observedComparisonRecord_of_historyWidth_of_scalarLowerBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.observedComparisonRecord_of_historyWidth_of_scalarLowerBound

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
