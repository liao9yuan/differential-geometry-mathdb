import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.MinDomain

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter _root_.Submission.Filter
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman

universe u
variable {H : ObservedHistory.{u}}

private theorem lt_stageEndTime_of_lt' {j k : Fin (H.eventCount + 1)} {t : ℝ}
    (ht : t ∈ H.stageDomain j) (hjk : j < k) : t < H.stageEndTime j := by
  cases j using Fin.lastCases with
  | last => exact absurd hjk (not_lt.2 (Fin.le_last k))
  | cast i =>
    simp only [stageDomain, Fin.lastCases_castSucc, _root_.Set.mem_Ico] at ht
    rw [stageEndTime_castSucc]
    exact ht.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.lt_stageEndTime_of_lt'
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.lt_stageEndTime_of_lt' target :: scope.openDecls } }

private theorem le_of_mem_stageDomain {j k : Fin (H.eventCount + 1)} {t t' : ℝ}
    (ht : t ∈ H.stageDomain j) (ht' : t' ∈ H.stageDomain k) (htt' : t ≤ t') : j ≤ k := by
  by_contra h
  have h1 := stageEndTime_le_time_of_lt (not_le.1 h)
  have h2 := lt_stageEndTime_of_lt' ht' (not_le.1 h)
  linarith [H.time_le_of_mem_stageDomain ht]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.le_of_mem_stageDomain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.le_of_mem_stageDomain target :: scope.openDecls } }

private theorem exists_mem_stageDomain {t : ℝ} (h0 : 0 ≤ t) (hH : t ≤ H.horizon) :
    ∃ k, t ∈ H.stageDomain k :=
  ⟨_, H.activeStage_mem ⟨t, h0, hH⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_mem_stageDomain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_mem_stageDomain target :: scope.openDecls } }

private theorem mem_piece_of_mem {T a b r : ℝ} (ha : 0 ≤ a) (hr : r ∈ _root_.Set.Icc a b)
    {j : Fin (H.eventCount + 1)} (ht : T - r ^ 2 ∈ _root_.Set.Icc (H.time j) (H.stageEndTime j)) :
    r ∈ _root_.Set.Icc (H.regularizedStageStart T a j) (H.regularizedStageEnd T b j) := by
  have hr0 : 0 ≤ r := ha.trans hr.1
  have ha2 : a ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ ha hr.1 2
  have hb2 : r ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hr0 hr.2 2
  constructor
  · apply (Real.sqrt_le_left hr0).2
    have := le_min (show T - r ^ 2 ≤ T - a ^ 2 by linarith) ht.2
    linarith
  · apply (Real.le_sqrt hr0 ?_).2
    · have := max_le (show T - b ^ 2 ≤ T - r ^ 2 by linarith) ht.1
      linarith
    · have := max_le (show T - b ^ 2 ≤ T - r ^ 2 by linarith) ht.1
      nlinarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.mem_piece_of_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.mem_piece_of_mem target :: scope.openDecls } }

private theorem mem_window_range {lo hi : Fin (H.eventCount + 1)} {T : ℝ}
    (W : H.LWindow lo hi T) {r : ℝ} (hr : r ∈ _root_.Set.Ioo W.a W.b) {j : Fin (H.eventCount + 1)}
    (ht : T - r ^ 2 ∈ _root_.Set.Icc (H.time j) (H.stageEndTime j)) : lo ≤ j ∧ j ≤ hi := by
  have ha := W.nonneg
  have h1 : W.a ^ 2 < r ^ 2 := pow_lt_pow_left₀ hr.1 ha two_ne_zero
  have h2 : r ^ 2 < W.b ^ 2 := pow_lt_pow_left₀ hr.2 (ha.trans hr.1.le) two_ne_zero
  constructor
  · by_contra h
    have := (stageEndTime_le_time_of_lt (not_le.1 h)).trans (H.time_le_of_mem_stageDomain W.lower)
    linarith [ht.2]
  · by_contra h
    have := (H.le_stageEndTime_of_mem_stageDomain W.upper).trans
      (stageEndTime_le_time_of_lt (not_le.1 h))
    linarith [ht.1]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.mem_window_range
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.mem_window_range target :: scope.openDecls } }

private theorem bounds_of_action_eq_cost {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
    {T B v : ℝ} {α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}
    (hmin : H.regularizedExtendedAction first last T B 0 v α =
      H.regularizedCost first last hle T B 0 v (α ⟨last, hle, le_rfl⟩ 0)
        (α ⟨first, le_rfl, hle⟩ v))
    (hfin : H.regularizedExtendedAction first last T B 0 v α ≠ ⊤) :
    T - 0 ^ 2 ∈ _root_.Set.Icc (H.time last) (H.stageEndTime last) ∧ T - v ^ 2 ∈ H.stageDomain first := by
  have hne : (H.regularizedActionValues first last hle T B 0 v (α ⟨last, hle, le_rfl⟩ 0)
      (α ⟨first, le_rfl, hle⟩ v)).Nonempty := by
    by_contra h
    exact hfin (hmin.trans (H.regularizedCost_eq_top_of_no_competitor first last hle T B 0 v _ _
      (not_nonempty_iff_eq_empty.1 h)))
  obtain ⟨A, -, -, hupper, hlower, -⟩ := hne
  exact ⟨hupper, hlower⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.bounds_of_action_eq_cost
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.bounds_of_action_eq_cost target :: scope.openDecls } }

private theorem node_of_crossing {first last : Fin (H.eventCount + 1)} {T : ℝ}
    {α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}
    (hcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      (H.event i).RegularCrossing
        (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
        (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))))
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last) :
    ∃ z : (H.event i).old,
      z.val.val = α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
        (Real.sqrt (T - H.time i.succ)) ∧
      (H.event i).oldOutput z = α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
        (Real.sqrt (T - H.time i.succ)) := by
  obtain ⟨z, -, h1, h2⟩ := hcross i hf hl
  exact ⟨z, h1, h2⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.node_of_crossing
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.node_of_crossing target :: scope.openDecls } }

section Truncation

variable {first last k : Fin (H.eventCount + 1)} {T B v₁ v₂ : ℝ}

theorem first_le_of_mem_stageDomain (hv₁ : 0 ≤ v₁) (h12 : v₁ ≤ v₂)
    (hlower : T - v₂ ^ 2 ∈ H.stageDomain first) (hk : T - v₁ ^ 2 ∈ H.stageDomain k) :
    first ≤ k :=
  le_of_mem_stageDomain hlower hk (sub_le_sub_left (pow_le_pow_left₀ hv₁ h12 2) T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.first_le_of_mem_stageDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.first_le_of_mem_stageDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.first_le_of_mem_stageDomain ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.first_le_of_mem_stageDomain

theorem regularizedExtendedAction_truncate_eq_regularizedCost (hle : first ≤ last)
    (hfk : first ≤ k) (hkl : k ≤ last) (hv₁ : 0 ≤ v₁) (h12 : v₁ ≤ v₂)
    (hk : T - v₁ ^ 2 ∈ H.stageDomain k)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v₂ j.val))
    (hnode : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B 0 v₂ α =
      H.regularizedCost first last hle T B 0 v₂ (α ⟨last, hle, le_rfl⟩ 0)
        (α ⟨first, le_rfl, hle⟩ v₂))
    (hfin : H.regularizedExtendedAction first last T B 0 v₂ α ≠ ⊤) :
    H.regularizedExtendedAction k last T B 0 v₁
        (fun j => α ⟨j.val, hfk.trans j.property.1, j.property.2⟩) =
      H.regularizedCost k last hkl T B 0 v₁ (α ⟨last, hle, le_rfl⟩ 0) (α ⟨k, hfk, hkl⟩ v₁) ∧
    H.regularizedExtendedAction k last T B 0 v₁
        (fun j => α ⟨j.val, hfk.trans j.property.1, j.property.2⟩) ≠ ⊤ := by
  obtain ⟨hupper, hlower⟩ := bounds_of_action_eq_cost hmin hfin
  have hsc : ∀ t ∈ _root_.Set.Ioo (H.regularizedStageStart T 0 k) (H.regularizedStageEnd T v₂ k),
      ∀ x : (H.stage k).Carrier, -B ≤ metricScalarAt (H.stageMetric k (T - t ^ 2)) x :=
    fun t ht x => hfloor k _ (H.mapsTo_regularizedStage_Ioo T 0 v₂ k ht) x
  have hsplit := regularizedExtendedAction_eq_add_at_parameter k hfk hkl le_rfl hv₁ h12 hk hsc
    α hα
  have hU := mem_regularizedActionValues_upper_restrict (B := B) k hfk hkl le_rfl hv₁ h12 hupper
    hlower hk α hα hnode
  have hL := mem_regularizedActionValues_lower_restrict (B := B) k hfk hkl le_rfl hv₁ h12 hupper
    hlower hk α hα hnode
  rw [hsplit] at hfin hmin
  have hLtop : H.regularizedExtendedAction first k T B v₁ v₂
      (fun j => α ⟨j.val, j.property.1, j.property.2.trans hkl⟩) ≠ ⊤ := fun h =>
    hfin (by rw [h, add_top])
  have hUtop : H.regularizedExtendedAction k last T B 0 v₁
      (fun j => α ⟨j.val, hfk.trans j.property.1, j.property.2⟩) ≠ ⊤ := fun h =>
    hfin (by rw [h, top_add])
  refine ⟨le_antisymm ?_ (H.regularizedCost_le_of_competitor _ _ _ _ _ _ _ _ _ hU), hUtop⟩
  rcases (H.regularizedActionValues k last hkl T B 0 v₁ (α ⟨last, hle, le_rfl⟩ 0)
    (α ⟨k, hfk, hkl⟩ v₁)).eq_empty_or_nonempty with he | hne
  · rw [H.regularizedCost_eq_top_of_no_competitor k last hkl T B 0 v₁ _ _ he]
    exact le_top
  refine le_csInf hne fun A' hA' => ?_
  have hmem := (H.mem_regularizedActionValues_split_at_parameter hle k hfk hkl le_rfl hv₁ h12
    hupper hlower hk hsc (α ⟨last, hle, le_rfl⟩ 0) (α ⟨first, le_rfl, hle⟩ v₂)).2
    ⟨_, A', _, hA', hL, rfl⟩
  have hc := H.regularizedCost_le_of_competitor first last hle T B 0 v₂ _ _ hmem
  rw [← hmin] at hc
  exact (WithTop.add_le_add_iff_right hLtop).1 hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.regularizedExtendedAction_truncate_eq_regularizedCost then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.regularizedExtendedAction_truncate_eq_regularizedCost"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.regularizedExtendedAction_truncate_eq_regularizedCost ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.regularizedExtendedAction_truncate_eq_regularizedCost

theorem HasHistoryLInitialVector.truncate (hv₁ : 0 < v₁) (hfk : first ≤ k)
    (hk : T - v₁ ^ 2 ∈ H.stageDomain k)
    {α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}
    {p : (H.stage last).Carrier} {Z : TangentSpace ThreeModel p}
    (h : H.HasHistoryLInitialVector T α p Z) :
    H.HasHistoryLInitialVector T
      (fun j : H.StageInterval k last => α ⟨j.val, hfk.trans j.property.1, j.property.2⟩) p Z := by
  obtain ⟨lo, hlo, W, x, Zx, ha, hx, hZ, hb, heq⟩ := h
  have hT : T ∈ H.stageDomain last := by simpa [ha] using W.upper
  set b' := _root_.Min.min W.b v₁ with hb'
  have hab : W.a < b' := lt_min W.lt (ha ▸ hv₁)
  have hb'0 : 0 ≤ b' := W.nonneg.trans hab.le
  have hb'b : b' ≤ W.b := min_le_left _ _
  have hlowb : T - W.b ^ 2 ≤ T - b' ^ 2 := sub_le_sub_left (pow_le_pow_left₀ hb'0 hb'b 2) T
  have hbv : T - v₁ ^ 2 ≤ T - b' ^ 2 :=
    sub_le_sub_left (pow_le_pow_left₀ hb'0 (min_le_right _ _) 2) T
  have hbT : T - b' ^ 2 ≤ T := by nlinarith
  have h0 : 0 ≤ T - b' ^ 2 :=
    (H.time_nonneg k).trans ((H.time_le_of_mem_stageDomain hk).trans hbv)
  have hH : T - b' ^ 2 ≤ H.horizon :=
    hbT.trans ((H.le_stageEndTime_of_mem_stageDomain hT).trans (H.stageEndTime_le_horizon _))
  obtain ⟨lo', hlo'⟩ := exists_mem_stageDomain h0 hH
  have h1 : lo ≤ lo' := le_of_mem_stageDomain W.lower hlo' hlowb
  have h2 : k ≤ lo' := le_of_mem_stageDomain hk hlo' hbv
  have h3 : lo' ≤ last := le_of_mem_stageDomain hlo' hT hbT
  refine ⟨lo', h2, W.restrict h1 le_rfl h3 le_rfl hab hb'b W.upper hlo', x, Zx, ha, hx, hZ,
    ?_, fun j r hr => ?_⟩
  · obtain ⟨c, J, hJo, hJc, h0J, hbJ, hcurve⟩ := hb
    have hbJ' : W.b ∈ J := hbJ
    exact ⟨c, J, hJo, hJc, h0J, hJc.Icc_subset h0J hbJ' ⟨hb'0, hb'b⟩, hcurve⟩
  · exact heq ⟨j.val, h1.trans j.property.1, j.property.2⟩
      ⟨hr.1, hr.2.trans (regularizedStageEnd_le_of_le hb'0 hb'b j.val)⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.HasHistoryLInitialVector
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.HasHistoryLInitialVector.truncate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.HasHistoryLInitialVector.truncate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.HasHistoryLInitialVector.truncate ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.HasHistoryLInitialVector.truncate

private theorem absolutelyContinuous_truncate (hfk : first ≤ k) (hv₁ : 0 ≤ v₁) (h12 : v₁ ≤ v₂)
    (hupper : T - 0 ^ 2 ∈ _root_.Set.Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v₂ ^ 2 ∈ H.stageDomain first) (hk : T - v₁ ^ 2 ∈ H.stageDomain k)
    {α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v₂ j.val))
    (j : H.StageInterval k last) :
    Manifold.absolutelyContinuousOnInterval ThreeModel
      (α ⟨j.val, hfk.trans j.property.1, j.property.2⟩)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v₁ j.val) := by
  apply Manifold.absolutelyContinuousOnInterval_mono (hα _)
  rw [_root_.Set.uIcc_of_le (H.regularizedStage_bounds le_rfl hv₁ hupper hk j).2.1,
    _root_.Set.uIcc_of_le (H.regularizedStage_bounds le_rfl (hv₁.trans h12) hupper hlower
      ⟨j.val, hfk.trans j.property.1, j.property.2⟩).2.1]
  exact _root_.Set.Icc_subset_Icc le_rfl (regularizedStageEnd_le_of_le hv₁ h12 j.val)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.absolutelyContinuous_truncate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.absolutelyContinuous_truncate target :: scope.openDecls } }

theorem truncate_mem_regularMinimizerEndpoints (hle : first ≤ last) (hfk : first ≤ k)
    (hkl : k ≤ last) (hv₁ : 0 ≤ v₁) (h12 : v₁ ≤ v₂) (hk : T - v₁ ^ 2 ∈ H.stageDomain k)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v₂ j.val))
    (hcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      (H.event i).RegularCrossing
        (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
        (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))))
    (hmin : H.regularizedExtendedAction first last T B 0 v₂ α =
      H.regularizedCost first last hle T B 0 v₂ (α ⟨last, hle, le_rfl⟩ 0)
        (α ⟨first, le_rfl, hle⟩ v₂))
    (hfin : H.regularizedExtendedAction first last T B 0 v₂ α ≠ ⊤) :
    α ⟨k, hfk, hkl⟩ v₁ ∈ H.regularMinimizerEndpoints k last hkl T B v₁ (α ⟨last, hle, le_rfl⟩ 0) ∧
      H.regularizedCost k last hkl T B 0 v₁ (α ⟨last, hle, le_rfl⟩ 0) (α ⟨k, hfk, hkl⟩ v₁) ≠ ⊤ := by
  obtain ⟨hupper, hlower⟩ := bounds_of_action_eq_cost hmin hfin
  have h := regularizedExtendedAction_truncate_eq_regularizedCost hle hfk hkl hv₁ h12 hk hfloor α
    hα (node_of_crossing hcross) hmin hfin
  exact ⟨⟨_, absolutelyContinuous_truncate hfk hv₁ h12 hupper hlower hk hα, rfl, rfl,
    fun i hf hl => hcross i (hfk.trans hf) hl, h.1⟩, h.1 ▸ h.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.truncate_mem_regularMinimizerEndpoints then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.truncate_mem_regularMinimizerEndpoints"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.truncate_mem_regularMinimizerEndpoints ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.truncate_mem_regularMinimizerEndpoints

variable {hle : first ≤ last} {p : (H.stage last).Carrier}
  (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
    -B ≤ metricScalarAt (H.stageMetric j t) x)
include hfloor

theorem isHistoryLGeodesicOn_truncate (hfk : first ≤ k) (hkl : k ≤ last) (hv₁ : 0 < v₁)
    (h12 : v₁ ≤ v₂) (hk : T - v₁ ^ 2 ∈ H.stageDomain k)
    {α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}
    (hgeo : H.IsHistoryLGeodesicOn hle T v₂ α)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v₂ j.val))
    (hmin : H.regularizedExtendedAction first last T B 0 v₂ α =
      H.regularizedCost first last hle T B 0 v₂ (α ⟨last, hle, le_rfl⟩ 0)
        (α ⟨first, le_rfl, hle⟩ v₂))
    (hfin : H.regularizedExtendedAction first last T B 0 v₂ α ≠ ⊤) :
    H.IsHistoryLGeodesicOn hkl T v₁
      (fun j : H.StageInterval k last => α ⟨j.val, hfk.trans j.property.1, j.property.2⟩) := by
  obtain ⟨hupper, hlower⟩ := bounds_of_action_eq_cost hmin hfin
  have h := regularizedExtendedAction_truncate_eq_regularizedCost hle hfk hkl hv₁.le h12 hk
    hfloor α hα (node_of_crossing hgeo.2.1) hmin hfin
  exact isHistoryLGeodesicOn_of_regularizedCost_eq hkl hfloor
    (absolutelyContinuous_truncate hfk hv₁.le h12 hupper hlower hk hα)
    (fun i hf hl => hgeo.2.1 i (hfk.trans hf) hl) h.1 h.2 hv₁

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.isHistoryLGeodesicOn_truncate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.isHistoryLGeodesicOn_truncate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.isHistoryLGeodesicOn_truncate ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.isHistoryLGeodesicOn_truncate

theorem mem_historyMinDomain_of_le (hkl : k ≤ last) (hv₁ : 0 < v₁) (h12 : v₁ ≤ v₂)
    (hk : T - v₁ ^ 2 ∈ H.stageDomain k) {Z : TangentSpace ThreeModel p}
    (hZ : Z ∈ H.historyMinDomain hle T B v₂ p) : Z ∈ H.historyMinDomain hkl T B v₁ p := by
  obtain ⟨α, hgeo, hinit, hac, rfl, hmin, hfin⟩ := hZ
  obtain ⟨hupper, hlower⟩ := bounds_of_action_eq_cost hmin hfin
  have hfk := first_le_of_mem_stageDomain hv₁.le h12 hlower hk
  have h := regularizedExtendedAction_truncate_eq_regularizedCost hle hfk hkl hv₁.le h12 hk
    hfloor α hac (node_of_crossing hgeo.2.1) hmin hfin
  exact ⟨_, isHistoryLGeodesicOn_truncate hfloor hfk hkl hv₁ h12 hk hgeo hac hmin hfin,
    hinit.truncate hv₁ hfk hk, absolutelyContinuous_truncate hfk hv₁.le h12 hupper hlower hk hac,
    rfl, h.1, h.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.mem_historyMinDomain_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.mem_historyMinDomain_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.mem_historyMinDomain_of_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.mem_historyMinDomain_of_le

theorem historyMinDomain_subset_of_le (hkl : k ≤ last) (hv₁ : 0 < v₁) (h12 : v₁ ≤ v₂)
    (hk : T - v₁ ^ 2 ∈ H.stageDomain k) :
    H.historyMinDomain hle T B v₂ p ⊆ H.historyMinDomain hkl T B v₁ p :=
  fun _ hZ => mem_historyMinDomain_of_le hfloor hkl hv₁ h12 hk hZ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.historyMinDomain_subset_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.historyMinDomain_subset_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.historyMinDomain_subset_of_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.historyMinDomain_subset_of_le

theorem historyLExp_eq_historyLCurve_of_le (hfk : first ≤ k) (hkl : k ≤ last) (hv₁ : 0 < v₁)
    (h12 : v₁ ≤ v₂) (hk : T - v₁ ^ 2 ∈ H.stageDomain k) (Z : H.historyLExpDomain hle T v₂ p)
    (hZ : Z.1 ∈ H.historyMinDomain hle T B v₂ p) (Z' : H.historyLExpDomain hkl T v₁ p)
    (hZZ' : Z'.1 = Z.1) :
    H.historyLExp hkl T v₁ p Z' = H.historyLCurve hle T v₂ p Z ⟨k, hfk, hkl⟩ v₁ := by
  obtain ⟨α, hgeo, hinit, hac, rfl, hmin, hfin⟩ := hZ
  obtain ⟨hupper, hlower⟩ := bounds_of_action_eq_cost hmin hfin
  have hv₂ : 0 < v₂ := hv₁.trans_le h12
  have hinit' := hinit.truncate hv₁ hfk hk
  rw [← hZZ'] at hinit'
  rw [historyLExp_eq hv₁ Z' (isHistoryLGeodesicOn_truncate hfloor hfk hkl hv₁ h12 hk hgeo hac hmin
    hfin) hinit']
  refine (eqOn_historyLCurve hv₂ Z hgeo hinit ⟨k, hfk, hkl⟩ ?_).symm
  have hb := (H.regularizedStage_bounds le_rfl hv₁.le hupper hk ⟨k, le_rfl, hkl⟩).1
  refine ⟨?_, ?_⟩
  · exact (regularizedStageStart_le_of_le le_rfl hv₁.le k).trans
      (H.regularizedStageStart_eq_of_mem_Icc hv₁.le
        ⟨H.time_le_of_mem_stageDomain hk, H.le_stageEndTime_of_mem_stageDomain hk⟩).le
  · exact (H.regularizedStageEnd_eq_of_mem_stageDomain hv₁.le hk).symm.le.trans
      (regularizedStageEnd_le_of_le hv₁.le h12 k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.historyLExp_eq_historyLCurve_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.historyLExp_eq_historyLCurve_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.historyLExp_eq_historyLCurve_of_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.historyLExp_eq_historyLCurve_of_le

theorem image_historyMinDomain_subset_of_le (hkl : k ≤ last) (hv₁ : 0 < v₁) (h12 : v₁ ≤ v₂)
    (hk : T - v₁ ^ 2 ∈ H.stageDomain k) :
    H.historyLExp hkl T v₁ p '' (Subtype.val ⁻¹' H.historyMinDomain hle T B v₂ p) ⊆
      H.regularMinimizerEndpoints k last hkl T B v₁ p ∩
        {q | H.regularizedCost k last hkl T B 0 v₁ p q ≠ ⊤} :=
  (_root_.Set.image_mono (_root_.Set.preimage_mono (historyMinDomain_subset_of_le hfloor hkl hv₁ h12 hk))).trans
    (image_historyMinDomain_subset hv₁)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.image_historyMinDomain_subset_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.image_historyMinDomain_subset_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.image_historyMinDomain_subset_of_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.image_historyMinDomain_subset_of_le

end Truncation

section Backward

variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {T B v : ℝ}
  {α β : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}

private theorem agree_at_of_lt (hv : 0 ≤ v)
    (hupper : T - 0 ^ 2 ∈ _root_.Set.Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (hαac : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hβac : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (β j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    {s : ℝ} (hA : ∀ (j : H.StageInterval first last) (r : ℝ),
      r ∈ _root_.Set.Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) →
        s < r → α j r = β j r)
    (j : H.StageInterval first last)
    (hj : s ∈ _root_.Set.Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hlt : s < H.regularizedStageEnd T v j.val) : α j s = β j s := by
  have hb := (H.regularizedStage_bounds le_rfl hv hupper hlower j).2.1
  have cα := (hαac j).1
  have cβ := (hβac j).1
  rw [_root_.Set.uIcc_of_le hb] at cα cβ
  have hsub : _root_.Set.Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) ∈
      𝓝[>] s :=
    _root_.Filter.mem_of_superset (Ioo_mem_nhdsGT hlt) fun r hr => ⟨hj.1.trans hr.1.le, hr.2.le⟩
  have hev : α j =ᶠ[𝓝[>] s] β j := by
    filter_upwards [Ioo_mem_nhdsGT hlt] with r hr
    exact hA j r ⟨hj.1.trans hr.1.le, hr.2.le⟩ hr.1
  exact tendsto_nhds_unique_of_eventuallyEq ((cα s hj).mono_of_mem_nhdsWithin hsub)
    ((cβ s hj).mono_of_mem_nhdsWithin hsub) hev

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.agree_at_of_lt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.agree_at_of_lt target :: scope.openDecls } }

private theorem agree_at (hv : 0 ≤ v)
    (hupper : T - 0 ^ 2 ∈ _root_.Set.Icc (H.time last) (H.stageEndTime last))
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    (hαac : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hβac : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (β j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hαcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      (H.event i).RegularCrossing
        (α ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
        (α ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))))
    (hβcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      (H.event i).RegularCrossing
        (β ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
        (β ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))))
    {s : ℝ} (hs0 : 0 ≤ s) (hsv : s < v) (hA : ∀ (j : H.StageInterval first last) (r : ℝ),
      r ∈ _root_.Set.Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) →
        s < r → α j r = β j r)
    (j : H.StageInterval first last)
    (hj : s ∈ _root_.Set.Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) :
    α j s = β j s := by
  rcases lt_or_eq_of_le hj.2 with hlt | heq
  · exact agree_at_of_lt hv hupper hlower hαac hβac hA j hj hlt
  obtain ⟨jv, h1, h2⟩ := j
  change s = Real.sqrt (T - _root_.Max.max (T - v ^ 2) (H.time jv)) at heq
  have hT : H.time jv ≤ T := (H.time_strictMono.monotone h2).trans (by simpa using hupper.1)
  have hnn : 0 ≤ T - _root_.Max.max (T - v ^ 2) (H.time jv) := by
    have := max_le (show T - v ^ 2 ≤ T by nlinarith [sq_nonneg v]) hT
    linarith
  have hsq : s ^ 2 = T - _root_.Max.max (T - v ^ 2) (H.time jv) := by
    rw [heq]
    exact Real.sq_sqrt hnn
  have hvs : s ^ 2 < v ^ 2 := pow_lt_pow_left₀ hsv hs0 two_ne_zero
  have htime : H.time jv = T - s ^ 2 := by
    rcases max_choice (T - v ^ 2) (H.time jv) with h | h <;> rw [h] at hsq
    · linarith
    · linarith
  have hfj : first < jv := H.time_strictMono.lt_iff_lt.1
    (by linarith [H.time_le_of_mem_stageDomain hlower])
  obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 (ne_of_gt ((Fin.zero_le first).trans_lt hfj))
  have hf : first ≤ i.castSucc := Fin.le_castSucc_iff.2 hfj
  have hw : Real.sqrt (T - H.time i.succ) = s := by
    rw [htime, sub_sub_cancel, Real.sqrt_sq hs0]
  have hstart : H.regularizedStageStart T 0 i.castSucc = s := by
    rw [regularizedStageStart, stageEndTime_castSucc,
      min_eq_right (show H.time i.succ ≤ T - 0 ^ 2 by rw [htime]; nlinarith [sq_nonneg s]), hw]
  have hend : s < H.regularizedStageEnd T v i.castSucc := by
    rw [regularizedStageEnd, Real.lt_sqrt hs0]
    have hc : H.time i.castSucc < T - s ^ 2 := by
      rw [← htime]
      exact H.time_strictMono i.castSucc_lt_succ
    have := max_lt (show T - v ^ 2 < T - s ^ 2 by linarith) hc
    linarith
  have hold := agree_at_of_lt hv hupper hlower hαac hβac hA
    ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans h2⟩ ⟨hstart.le, hend.le⟩ hend
  have c₁ := hαcross i hf h2
  have c₂ := hβcross i hf h2
  rw [hw] at c₁ c₂
  rw [hold] at c₁
  exact (H.event i).regularCrossing_right_unique c₁ c₂

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.agree_at
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.agree_at target :: scope.openDecls } }

variable
  (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
    -B ≤ metricScalarAt (H.stageMetric j t) x)
  (hα : H.IsHistoryLGeodesicOn hle T v α)
  (hαac : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
    (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
  (hβac : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (β j)
    (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
  (hβcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
    (H.event i).RegularCrossing
      (β ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
      (β ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))))
  (hβmin : H.regularizedExtendedAction first last T B 0 v β =
    H.regularizedCost first last hle T B 0 v (β ⟨last, hle, le_rfl⟩ 0)
      (β ⟨first, le_rfl, hle⟩ v))
  (hβfin : H.regularizedExtendedAction first last T B 0 v β ≠ ⊤)
include hfloor hα hαac hβac hβcross hβmin hβfin

private theorem backward_step (hv : 0 < v) {s : ℝ} (hs : s ∈ _root_.Set.Ioo 0 v)
    (hA : ∀ (j : H.StageInterval first last) (r : ℝ),
      r ∈ _root_.Set.Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) →
        s < r → α j r = β j r) :
    ∃ s' < s, ∀ (j : H.StageInterval first last) (r : ℝ),
      r ∈ _root_.Set.Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) →
        s' < r → α j r = β j r := by
  obtain ⟨hupper, hlower⟩ := bounds_of_action_eq_cost hβmin hβfin
  obtain ⟨lo, hi, hlo, hhi, W, hsW, hWv, γα, hγα, heqα⟩ := hα.2.2.1 s hs
  have hag := agree_at hv.le hupper hlower hαac hβac hα.2.1 hβcross hs.1.le hs.2 hA
  have hnear : ∀ᶠ r in 𝓝 s, ∀ j : H.StageInterval lo hi,
      r ∈ _root_.Set.Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) →
        β ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ r ∈ _root_.Set.range (W.f j) := by
    refine eventually_all.2 fun j => ?_
    by_cases hj : s ∈ _root_.Set.Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)
    · have hb := (H.regularizedStage_bounds le_rfl hv.le hupper hlower
        ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩).2.1
      have hc := (hβac ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩).1
      rw [_root_.Set.uIcc_of_le hb] at hc
      have hjt := H.mem_Icc_of_mem_regularizedStage_Icc le_rfl hv.le hupper hlower
        ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ hj
      have hsj := mem_piece_of_mem W.nonneg (_root_.Set.Ioo_subset_Icc_self hsW) hjt
      have hmem : β ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ s ∈ _root_.Set.range (W.f j) :=
        ⟨γα s, (heqα j hsj).trans (hag _ hj)⟩
      exact mem_nhdsWithin_iff_eventually.1 ((hc s hj).preimage_mem_nhdsWithin
        ((W.localDiffeomorph j).isOpen_range.mem_nhds hmem))
    · filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hj] with r hr hr'
      exact absurd hr' hr
  obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff.1 (hnear.and (Ioo_mem_nhds hsW.1 hsW.2))
  set a' := _root_.Max.max W.a (s - ε / 2) with ha'
  set b' := _root_.Min.min W.b (s + ε / 2) with hb'
  have has : a' < s := max_lt hsW.1 (by linarith)
  have hsb : s < b' := lt_min hsW.2 (by linarith)
  have haa : W.a ≤ a' := le_max_left _ _
  have hbb : b' ≤ W.b := min_le_left _ _
  have hball : ∀ r ∈ _root_.Set.Icc a' b', _root_.Dist.dist r s < ε := fun r hr => by
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith [le_max_right W.a (s - ε / 2), min_le_right W.b (s + ε / 2), hr.1,
      hr.2]
  have ha'0 : 0 ≤ a' := W.nonneg.trans haa
  have hb'0 : 0 ≤ b' := ha'0.trans (has.trans hsb).le
  have hTa : T - a' ^ 2 ≤ T - W.a ^ 2 := sub_le_sub_left (pow_le_pow_left₀ W.nonneg haa 2) T
  have hTb : T - W.b ^ 2 ≤ T - b' ^ 2 := sub_le_sub_left (pow_le_pow_left₀ hb'0 hbb 2) T
  have hTab : T - b' ^ 2 ≤ T - a' ^ 2 :=
    sub_le_sub_left (pow_le_pow_left₀ ha'0 (has.trans hsb).le 2) T
  have hlo0 : 0 ≤ T - W.b ^ 2 :=
    (H.time_nonneg lo).trans (H.time_le_of_mem_stageDomain W.lower)
  have hhiH : T - W.a ^ 2 ≤ H.horizon :=
    (H.le_stageEndTime_of_mem_stageDomain W.upper).trans (H.stageEndTime_le_horizon hi)
  obtain ⟨hi', hhi'⟩ := exists_mem_stageDomain (hlo0.trans (hTb.trans hTab)) (hTa.trans hhiH)
  obtain ⟨lo', hlo'⟩ := exists_mem_stageDomain (hlo0.trans hTb) (hTab.trans (hTa.trans hhiH))
  have hl1 : lo ≤ lo' := le_of_mem_stageDomain W.lower hlo' hTb
  have hh1 : hi' ≤ hi := le_of_mem_stageDomain hhi' W.upper hTa
  have hlh : lo' ≤ hi' := le_of_mem_stageDomain hlo' hhi' hTab
  let W' := W.restrict hl1 hh1 hlh haa (has.trans hsb) hbb hhi' hlo'
  have hrange : ∀ j : H.StageInterval lo' hi',
      _root_.Set.MapsTo (β ⟨j.val, (hlo.trans hl1).trans j.property.1, j.property.2.trans (hh1.trans hhi)⟩)
        (_root_.Set.Icc (H.regularizedStageStart T W'.a j.val) (H.regularizedStageEnd T W'.b j.val))
        (_root_.Set.range (W'.f j)) := by
    intro j r hr
    exact (hεs (hball r (W'.piece_subset j hr))).1 ⟨j.val, hl1.trans j.property.1,
      j.property.2.trans hh1⟩ ⟨(regularizedStageStart_le_of_le le_rfl ha'0 j.val).trans hr.1,
        hr.2.trans (regularizedStageEnd_le_of_le hb'0 (hbb.trans hWv) j.val)⟩
  obtain ⟨γβ, -, -, heqβ, hγβ⟩ := W'.exists_lift_isLRegularizedGeodesicOn_of_regularizedCost_eq
    hle (hlo.trans hl1) (hh1.trans hhi) le_rfl ha'0 (hbb.trans hWv) hupper hlower hfloor β hβac
    (node_of_crossing hβcross) hβmin hβfin hrange
  have hlift : ∀ r ∈ _root_.Set.Ioo s b', γβ r = γα r := by
    intro r hr
    obtain ⟨j, hj⟩ := W'.exists_mem_piece (show r ∈ _root_.Set.Icc a' b' from ⟨(has.trans hr.1).le, hr.2.le⟩)
    have e₁ := heqβ j hj
    have hjP : r ∈ _root_.Set.Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) :=
      ⟨(regularizedStageStart_le_of_le le_rfl ha'0 j.val).trans hj.1,
        hj.2.trans (regularizedStageEnd_le_of_le hb'0 (hbb.trans hWv) j.val)⟩
    have hjW : r ∈ _root_.Set.Icc (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val) :=
      ⟨(regularizedStageStart_le_of_le W.nonneg haa j.val).trans hj.1,
        hj.2.trans (regularizedStageEnd_le_of_le hb'0 hbb j.val)⟩
    have e₂ := heqα ⟨j.val, hl1.trans j.property.1, j.property.2.trans hh1⟩ hjW
    have e₃ := hA ⟨j.val, (hlo.trans hl1).trans j.property.1, j.property.2.trans (hh1.trans hhi)⟩
      r hjP hr.1
    apply W.injective ⟨j.val, hl1.trans j.property.1, j.property.2.trans hh1⟩
    exact e₁.trans (e₃.symm.trans e₂.symm)
  set s₀ := (s + b') / 2 with hs₀def
  have hs₀ : s₀ ∈ _root_.Set.Ioo s b' := ⟨by linarith, by linarith⟩
  have hs₀' : s₀ ∈ _root_.Set.Ioo a' b' := ⟨has.trans hs₀.1, hs₀.2⟩
  have hevq : γβ =ᶠ[𝓝 s₀] γα := _root_.Filter.eventually_of_mem (Ioo_mem_nhds hs₀.1 hs₀.2) hlift
  have hvel : lVelocity (I := ThreeModel) γβ s₀ = lVelocity (I := ThreeModel) γα s₀ := by
    unfold lVelocity
    exact congrArg (fun L => L (1 : ℝ)) (hevq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel))
  have hγα' : IsLRegularizedGeodesicOn W.S T γα (_root_.Set.Ioo a' b') := fun r hr =>
    hγα r ⟨haa.trans_lt hr.1, hr.2.trans_le hbb⟩
  have heq := lRegularizedSolution_eqOn W.S W.solution T isOpen_Ioo isPreconnected_Ioo hs₀'
    isOpen_Ioo isPreconnected_Ioo hs₀' hγβ hγα' (hlift s₀ hs₀) hvel
  refine ⟨a', has, fun j r hr har => ?_⟩
  rcases lt_or_ge s r with hsr | hrs
  · exact hA j r hr hsr
  have hrI : r ∈ _root_.Set.Ioo a' b' := ⟨har, hrs.trans_lt hsb⟩
  have ht := H.mem_Icc_of_mem_regularizedStage_Icc le_rfl hv.le hupper hlower j hr
  have hj' := mem_window_range W' hrI ht
  have hj1 := mem_piece_of_mem ha'0 (_root_.Set.Ioo_subset_Icc_self hrI) ht
  have hjW := mem_piece_of_mem (H := H) (T := T) W.nonneg
    ⟨haa.trans hrI.1.le, hrI.2.le.trans hbb⟩ ht
  have e₁ := heqβ ⟨j.val, hj'⟩ hj1
  have e₂ := heqα ⟨j.val, hl1.trans hj'.1, hj'.2.trans hh1⟩ hjW
  exact e₂.symm.trans ((congrArg (W.f ⟨j.val, hl1.trans hj'.1, hj'.2.trans hh1⟩)
    (heq ⟨hrI, hrI⟩).symm).trans e₁)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.backward_step
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.backward_step target :: scope.openDecls } }

theorem IsHistoryLGeodesicOn.eqOn_of_eqOn_Ioi (hv : 0 < v) {s₀ : ℝ} (hs₀ : s₀ < v)
    (hA : ∀ (j : H.StageInterval first last) (r : ℝ),
      r ∈ _root_.Set.Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) →
        s₀ < r → α j r = β j r)
    (j : H.StageInterval first last) :
    _root_.Set.EqOn (α j) (β j)
      (_root_.Set.Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) := by
  obtain ⟨hupper, hlower⟩ := bounds_of_action_eq_cost hβmin hβfin
  let A : ℝ → Prop := fun s => ∀ (j : H.StageInterval first last) (r : ℝ),
    r ∈ _root_.Set.Icc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) →
      s < r → α j r = β j r
  have hmono : ∀ {s s' : ℝ}, s ≤ s' → A s → A s' := fun hss h j r hr hrs =>
    h j r hr (hss.trans_lt hrs)
  set S : Set ℝ := {s | 0 ≤ s ∧ A s} with hSdef
  have hS : _root_.Max.max s₀ 0 ∈ S := ⟨le_max_right _ _, hmono (le_max_left _ _) hA⟩
  have hbdd : BddBelow S := ⟨0, fun s hs => hs.1⟩
  have hc0 : 0 ≤ _root_.InfSet.sInf S := le_csInf ⟨_, hS⟩ fun s hs => hs.1
  have hAc : A (_root_.InfSet.sInf S) := fun j r hr hcr => by
    obtain ⟨s, hsS, hsr⟩ := exists_lt_of_csInf_lt ⟨_, hS⟩ hcr
    exact hsS.2 j r hr hsr
  have hc : _root_.InfSet.sInf S = 0 := by
    by_contra hne
    have hcpos : 0 < _root_.InfSet.sInf S := lt_of_le_of_ne hc0 (Ne.symm hne)
    have hcv : _root_.InfSet.sInf S < v := (csInf_le hbdd hS).trans_lt (max_lt hs₀ hv)
    obtain ⟨s', hs'c, hs'⟩ := backward_step hfloor hα hαac hβac hβcross hβmin hβfin hv
      ⟨hcpos, hcv⟩ hAc
    have h1 := csInf_le hbdd
      (show _root_.Max.max s' 0 ∈ S from ⟨le_max_right _ _, hmono (le_max_left _ _) hs'⟩)
    have h2 : _root_.Max.max s' 0 < _root_.InfSet.sInf S := max_lt hs'c hcpos
    linarith
  rw [hc] at hAc
  intro r hr
  rcases eq_or_lt_of_le ((Real.sqrt_nonneg _).trans hr.1) with h | h
  · subst h
    exact agree_at hv.le hupper hlower hαac hβac hα.2.1 hβcross le_rfl hv hAc j hr
  · exact hAc j r hr h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsHistoryLGeodesicOn.eqOn_of_eqOn_Ioi then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsHistoryLGeodesicOn.eqOn_of_eqOn_Ioi"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsHistoryLGeodesicOn.eqOn_of_eqOn_Ioi ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsHistoryLGeodesicOn.eqOn_of_eqOn_Ioi

end Backward

section InitialVector

variable {first last : Fin (H.eventCount + 1)} {T : ℝ}
  {α β : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}
  {p : (H.stage last).Carrier} {Z Z' : TangentSpace ThreeModel p}

private theorem exists_mfderivWithin_eq (hle : first ≤ last) (hT : H.time last < T)
    (h : H.HasHistoryLInitialVector T α p Z) :
    ∃ e > 0, ∀ e' ∈ _root_.Set.Ioc 0 e, mfderivWithin 𝓘(ℝ, ℝ) ThreeModel (α ⟨last, hle, le_rfl⟩)
      (_root_.Set.Icc 0 e') 0 1 = (2 : ℝ) • Z := by
  obtain ⟨lo, hlo, W, x, Zx, ha, hx, hZ, -, heq⟩ := h
  have hb : 0 < W.b := ha ▸ W.lt
  have hTreg : T ∈ W.D.regular := by simpa [ha] using W.regular W.a ⟨le_rfl, W.lt.le⟩
  have hstart : H.regularizedStageStart T 0 last = 0 := by
    have := H.regularizedStageStart_eq_of_mem_Icc W.nonneg W.upper_mem_Icc
    rwa [ha] at this
  have hepos : 0 < H.regularizedStageEnd T W.b last := by
    apply Real.sqrt_pos.2
    have := max_lt (show T - W.b ^ 2 < T by nlinarith) hT
    linarith
  have hEq : _root_.Set.EqOn (W.f ⟨last, W.le, le_rfl⟩ ∘ lRegularizedCurve W.S T x Zx)
      (α ⟨last, hle, le_rfl⟩) (_root_.Set.Icc 0 (H.regularizedStageEnd T W.b last)) := by
    have := heq ⟨last, W.le, le_rfl⟩
    rw [hstart] at this
    exact this
  have hcd : MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel (lRegularizedCurve W.S T x Zx) 0 := by
    have hpair : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ThreeSpace).prod 𝓘(ℝ, ℝ)) ∞
        (fun r : ℝ => ((Zx, r) : ThreeSpace × ℝ)) 0 :=
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    exact ((lRegularizedCurve_smoothAt W.S W.solution T x Zx hTreg).comp 0 hpair).mdifferentiableAt
      (by simp)
  have hfd : MDifferentiableAt ThreeModel ThreeModel (W.f ⟨last, W.le, le_rfl⟩)
      (lRegularizedCurve W.S T x Zx 0) :=
    (W.localDiffeomorph _ _).mdifferentiableAt (by simp)
  refine ⟨_, hepos, fun e' he' => ?_⟩
  have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (_root_.Set.Icc (0 : ℝ) e') 0 :=
    uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffOn_Icc he'.1 0 ⟨le_rfl, he'.1.le⟩)
  have hEq' := hEq.mono (_root_.Set.Icc_subset_Icc le_rfl he'.2)
  have key : mfderivWithin 𝓘(ℝ, ℝ) ThreeModel (α ⟨last, hle, le_rfl⟩) (_root_.Set.Icc 0 e') 0 =
      mfderivWithin 𝓘(ℝ, ℝ) ThreeModel
        (W.f ⟨last, W.le, le_rfl⟩ ∘ lRegularizedCurve W.S T x Zx) (_root_.Set.Icc 0 e') 0 :=
    (mfderivWithin_congr hEq' (hEq' ⟨le_rfl, he'.1.le⟩)).symm
  rw [key, mfderivWithin_eq_mfderiv hu (hfd.comp 0 hcd), mfderiv_comp 0 hfd hcd]
  change mfderiv ThreeModel ThreeModel (W.f ⟨last, W.le, le_rfl⟩)
    (lRegularizedCurve W.S T x Zx 0)
    (lVelocity (I := ThreeModel) (lRegularizedCurve W.S T x Zx) 0) = _
  rw [lRegularizedCurve_velocity_zero W.S W.solution T x Zx hTreg]
  have key₂ : ∀ y : W.X, y = x → mfderiv ThreeModel ThreeModel (W.f ⟨last, W.le, le_rfl⟩) y
      ((2 : ℝ) • Zx) = (2 : ℝ) • Z := by
    rintro y rfl
    rw [map_smul, hZ]
    rfl
  exact key₂ _ (lRegularizedCurve_zero _ _ _ _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_mfderivWithin_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_mfderivWithin_eq target :: scope.openDecls } }

theorem HasHistoryLInitialVector.eq_of_eqOn (hle : first ≤ last) (hT : H.time last < T)
    (hα : H.HasHistoryLInitialVector T α p Z) (hβ : H.HasHistoryLInitialVector T β p Z')
    {η : ℝ} (hη : 0 < η)
    (h : _root_.Set.EqOn (α ⟨last, hle, le_rfl⟩) (β ⟨last, hle, le_rfl⟩) (_root_.Set.Icc 0 η)) : Z = Z' := by
  obtain ⟨e₁, he₁, h₁⟩ := exists_mfderivWithin_eq hle hT hα
  obtain ⟨e₂, he₂, h₂⟩ := exists_mfderivWithin_eq hle hT hβ
  have he : 0 < _root_.Min.min η (_root_.Min.min e₁ e₂) := lt_min hη (lt_min he₁ he₂)
  have hc := mfderivWithin_congr (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel)
    (h.mono (_root_.Set.Icc_subset_Icc le_rfl (min_le_left η (_root_.Min.min e₁ e₂)))) (h ⟨le_rfl, hη.le⟩)
  have k₁ := h₁ _ ⟨he, (min_le_right _ _).trans (min_le_left _ _)⟩
  have k₂ := h₂ _ ⟨he, (min_le_right _ _).trans (min_le_right _ _)⟩
  rw [hc] at k₁
  exact smul_right_injective ThreeSpace (two_ne_zero : (2 : ℝ) ≠ 0) (k₁.symm.trans k₂)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.HasHistoryLInitialVector.eq_of_eqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.HasHistoryLInitialVector.eq_of_eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.HasHistoryLInitialVector.eq_of_eqOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.HasHistoryLInitialVector.eq_of_eqOn

end InitialVector

section Injective

variable {first last k : Fin (H.eventCount + 1)} {hle : first ≤ last} {T B v₁ v₂ : ℝ}
  {p : (H.stage last).Carrier}

theorem injOn_historyLExp_of_lt (hkl : k ≤ last)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (hT : H.time last < T) (hv₁ : 0 < v₁) (h12 : v₁ < v₂) (hk : T - v₁ ^ 2 ∈ H.stageDomain k) :
    InjOn (H.historyLExp hkl T v₁ p) (Subtype.val ⁻¹' H.historyMinDomain hle T B v₂ p) := by
  classical
  intro Z₁ hZ₁ Z₂ hZ₂ hE
  apply Subtype.ext
  obtain ⟨α, hαg, hαi, hαac, hαp, hαmin, hαfin⟩ := hZ₁
  obtain ⟨β, hβg, hβi, hβac, hβp, hβmin, hβfin⟩ := hZ₂
  rw [← hαp] at hαmin
  rw [← hβp] at hβmin
  obtain ⟨hupper, hlower⟩ := bounds_of_action_eq_cost hαmin hαfin
  have hv₂ : 0 < v₂ := hv₁.trans h12
  have hfk := first_le_of_mem_stageDomain hv₁.le h12.le hlower hk
  have hkI : T - v₁ ^ 2 ∈ _root_.Set.Icc (H.time k) (H.stageEndTime k) :=
    ⟨H.time_le_of_mem_stageDomain hk, H.le_stageEndTime_of_mem_stageDomain hk⟩
  have hxα : H.historyLExp hkl T v₁ p Z₁ = α ⟨k, hfk, hkl⟩ v₁ :=
    historyLExp_eq hv₁ Z₁ (isHistoryLGeodesicOn_truncate hfloor hfk hkl hv₁ h12.le hk hαg hαac
      hαmin hαfin) (hαi.truncate hv₁ hfk hk)
  have hxβ : H.historyLExp hkl T v₁ p Z₂ = β ⟨k, hfk, hkl⟩ v₁ :=
    historyLExp_eq hv₁ Z₂ (isHistoryLGeodesicOn_truncate hfloor hfk hkl hv₁ h12.le hk hβg hβac
      hβmin hβfin) (hβi.truncate hv₁ hfk hk)
  have hx : α ⟨k, hfk, hkl⟩ v₁ = β ⟨k, hfk, hkl⟩ v₁ := hxα.symm.trans (hE.trans hxβ)
  have hcα := regularizedExtendedAction_truncate_eq_regularizedCost hle hfk hkl hv₁.le h12.le hk
    hfloor α hαac (node_of_crossing hαg.2.1) hαmin hαfin
  have hcβ := regularizedExtendedAction_truncate_eq_regularizedCost hle hfk hkl hv₁.le h12.le hk
    hfloor β hβac (node_of_crossing hβg.2.1) hβmin hβfin
  have hU : H.regularizedExtendedAction k last T B 0 v₁
        (fun j => α ⟨j.val, hfk.trans j.property.1, j.property.2⟩) =
      H.regularizedExtendedAction k last T B 0 v₁
        (fun j => β ⟨j.val, hfk.trans j.property.1, j.property.2⟩) := by
    rw [hcα.1, hcβ.1, hαp, hβp, hx]
  let γ : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier := fun j =>
    if k < j.val then β j else if j.val < k then α j else _root_.Set.piecewise (_root_.Set.Iic v₁) (β j) (α j)
  have hγgt : ∀ j : H.StageInterval first last, k < j.val → γ j = β j := fun j h => by
    simp only [γ, if_pos h]
  have hγlt : ∀ j : H.StageInterval first last, j.val < k → γ j = α j := fun j h => by
    simp only [γ, if_neg (not_lt.2 h.le), if_pos h]
  have hγeq : ∀ j : H.StageInterval first last, j.val = k →
      γ j = _root_.Set.piecewise (_root_.Set.Iic v₁) (β j) (α j) := fun j h => by
    simp only [γ, h, lt_irrefl, if_false]
  have hγle : ∀ (j : H.StageInterval first last) (r : ℝ), k ≤ j.val → r ≤ v₁ → γ j r = β j r := by
    intro j r hj hr
    rcases hj.lt_or_eq with h | h
    · rw [hγgt j h]
    · rw [hγeq j h.symm, _root_.Set.piecewise_eq_of_mem _ _ _ (mem_Iic.2 hr)]
  have hγge : ∀ (j : H.StageInterval first last) (r : ℝ), j.val ≤ k → v₁ ≤ r → γ j r = α j r := by
    intro j r hj hr
    rcases hj.lt_or_eq with h | h
    · rw [hγlt j h]
    rcases hr.lt_or_eq with h' | h'
    · rw [hγeq j h, _root_.Set.piecewise_eq_of_notMem _ _ _ fun hm => absurd (mem_Iic.1 hm) (not_le.2 h')]
    · subst h'
      obtain rfl : j = ⟨k, hfk, hkl⟩ := Subtype.ext h
      rw [hγeq _ rfl, _root_.Set.piecewise_eq_of_mem _ _ _ (mem_Iic.2 le_rfl)]
      exact hx.symm
  have hγac : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (γ j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v₂ j.val) := by
    intro j
    rcases lt_trichotomy j.val k with h | h | h
    · rw [hγlt j h]
      exact hαac j
    · obtain rfl : j = ⟨k, hfk, hkl⟩ := Subtype.ext h
      rw [hγeq _ rfl]
      have hs : H.regularizedStageStart T 0 k ≤ v₁ :=
        (regularizedStageStart_le_of_le le_rfl hv₁.le k).trans
          (H.regularizedStageStart_eq_of_mem_Icc hv₁.le hkI).le
      have he : v₁ ≤ H.regularizedStageEnd T v₂ k :=
        (H.regularizedStageEnd_eq_of_mem_stageDomain hv₁.le hk).symm.le.trans
          (regularizedStageEnd_le_of_le hv₁.le h12.le k)
      have hb := (H.regularizedStage_bounds le_rfl hv₂.le hupper hlower ⟨k, hfk, hkl⟩).2.1
      dsimp only at hb ⊢
      refine Manifold.absolutelyContinuousOnInterval_piecewise_Iic ?_ ?_ hs he hx.symm
      · apply Manifold.absolutelyContinuousOnInterval_mono (hβac _)
        rw [_root_.Set.uIcc_of_le hs, _root_.Set.uIcc_of_le hb]
        exact _root_.Set.Icc_subset_Icc le_rfl he
      · apply Manifold.absolutelyContinuousOnInterval_mono (hαac _)
        rw [_root_.Set.uIcc_of_le he, _root_.Set.uIcc_of_le hb]
        exact _root_.Set.Icc_subset_Icc hs le_rfl
    · rw [hγgt j h]
      exact hβac j
  have hγp : γ ⟨last, hle, le_rfl⟩ 0 = p := (hγle _ 0 hkl hv₁.le).trans hβp
  have hγq : γ ⟨first, le_rfl, hle⟩ v₂ = α ⟨first, le_rfl, hle⟩ v₂ := hγge _ v₂ hfk h12.le
  have hγcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      (H.event i).RegularCrossing
        (γ ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
        (γ ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ (Real.sqrt (T - H.time i.succ))) := by
    intro i hf hl
    rcases le_or_gt k i.castSucc with hki | hik
    · have hks := hki.trans_lt i.castSucc_lt_succ
      have hw : Real.sqrt (T - H.time i.succ) ≤ v₁ := by
        have h1 := lt_stageEndTime_of_lt' hk hks
        have h2 := stageEndTime_le_time_of_lt hks
        exact ((Real.sqrt_lt' hv₁).2 (by linarith)).le
      rw [hγle ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ _ hki hw,
        hγle ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ _ hks.le hw]
      exact hβg.2.1 i hf hl
    · have hsk : i.succ ≤ k := Fin.castSucc_lt_iff_succ_le.1 hik
      have hw : v₁ ≤ Real.sqrt (T - H.time i.succ) := by
        apply Real.le_sqrt_of_sq_le
        have := (H.time_strictMono.monotone hsk).trans (H.time_le_of_mem_stageDomain hk)
        linarith
      rw [hγge ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩ _ hik.le hw,
        hγge ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩ _ hsk hw]
      exact hαg.2.1 i hf hl
  have hsc : ∀ t ∈ _root_.Set.Ioo (H.regularizedStageStart T 0 k) (H.regularizedStageEnd T v₂ k),
      ∀ x : (H.stage k).Carrier, -B ≤ metricScalarAt (H.stageMetric k (T - t ^ 2)) x :=
    fun t ht x => hfloor k _ (H.mapsTo_regularizedStage_Ioo T 0 v₂ k ht) x
  have hsplitγ := regularizedExtendedAction_eq_add_at_parameter k hfk hkl le_rfl hv₁.le h12.le hk
    hsc γ hγac
  have hsplitα := regularizedExtendedAction_eq_add_at_parameter k hfk hkl le_rfl hv₁.le h12.le hk
    hsc α hαac
  have hUγ : H.regularizedExtendedAction k last T B 0 v₁
        (fun j => γ ⟨j.val, hfk.trans j.property.1, j.property.2⟩) =
      H.regularizedExtendedAction k last T B 0 v₁
        (fun j => β ⟨j.val, hfk.trans j.property.1, j.property.2⟩) := by
    unfold regularizedExtendedAction
    refine Finset.sum_congr rfl fun j _ =>
      H.stageRegularizedExtendedAction_congr j.val T B _ _ _ _ fun r hr => ?_
    have hb := (H.regularizedStage_bounds le_rfl hv₁.le hupper hk j).2.2
    exact hγle _ r j.property.1 (hr.2.le.trans hb)
  have hLγ : H.regularizedExtendedAction first k T B v₁ v₂
        (fun j => γ ⟨j.val, j.property.1, j.property.2.trans hkl⟩) =
      H.regularizedExtendedAction first k T B v₁ v₂
        (fun j => α ⟨j.val, j.property.1, j.property.2.trans hkl⟩) := by
    unfold regularizedExtendedAction
    refine Finset.sum_congr rfl fun j _ =>
      H.stageRegularizedExtendedAction_congr j.val T B _ _ _ _ fun r hr => ?_
    have hb := (H.regularizedStage_bounds hv₁.le h12.le hkI hlower j).1
    exact hγge _ r j.property.2 (hb.trans hr.1.le)
  have hγact : H.regularizedExtendedAction first last T B 0 v₂ γ =
      H.regularizedExtendedAction first last T B 0 v₂ α := by
    rw [hsplitγ, hsplitα, hUγ, hLγ, ← hU]
  have hγmin : H.regularizedExtendedAction first last T B 0 v₂ γ =
      H.regularizedCost first last hle T B 0 v₂ (γ ⟨last, hle, le_rfl⟩ 0)
        (γ ⟨first, le_rfl, hle⟩ v₂) := by
    rw [hγact, hγp, hγq, hαmin, hαp]
  have hγfin : H.regularizedExtendedAction first last T B 0 v₂ γ ≠ ⊤ := by
    rw [hγact]
    exact hαfin
  have hagree := IsHistoryLGeodesicOn.eqOn_of_eqOn_Ioi hfloor hαg hαac hγac hγcross hγmin hγfin
    hv₂ h12 fun j r hr hvr => by
      rcases le_or_gt j.val k with hjk | hkj
      · exact (hγge j r hjk hvr.le).symm
      · have he := H.regularizedStageEnd_eq_of_lt hk hkj (pow_le_pow_left₀ hv₁.le h12.le 2)
        have hb := (H.regularizedStage_bounds le_rfl hv₁.le hupper hk
          ⟨j.val, hkj.le, j.property.2⟩).2.2
        dsimp only at hb
        linarith [hr.2]
  have hstart : H.regularizedStageStart T 0 last = 0 :=
    H.regularizedStageStart_eq_of_mem_Icc le_rfl hupper
  have hη : 0 < _root_.Min.min v₁ (H.regularizedStageEnd T v₂ last) := by
    refine lt_min hv₁ (Real.sqrt_pos.2 ?_)
    have := max_lt (show T - v₂ ^ 2 < T by nlinarith) hT
    linarith
  refine HasHistoryLInitialVector.eq_of_eqOn hle hT hαi hβi hη fun r hr => ?_
  have hrP : r ∈ _root_.Set.Icc (H.regularizedStageStart T 0 last) (H.regularizedStageEnd T v₂ last) :=
    ⟨hstart.le.trans hr.1, hr.2.trans (min_le_right _ _)⟩
  exact (hagree ⟨last, hle, le_rfl⟩ hrP).trans (hγle _ r hkl (hr.2.trans (min_le_left _ _)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.injOn_historyLExp_of_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.injOn_historyLExp_of_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.injOn_historyLExp_of_lt ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.injOn_historyLExp_of_lt

end Injective

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
