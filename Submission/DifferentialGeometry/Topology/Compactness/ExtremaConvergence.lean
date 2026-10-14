import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.Real
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set _root_.Filter
open scoped _root_.Topology

namespace IsCompact
open _root_.IsCompact

variable {X ι : Type*} [TopologicalSpace X] {l : Filter ι}
  {K : Set X} {F : ι → X → ℝ} {f : X → ℝ} {x : X} {z : ι → X}

open _root_.IsCompact in
theorem tendsto_of_isMaxOn_of_tendstoUniformlyOn
    (hK : IsCompact K) (hf : UpperSemicontinuousOn f K) (hx : x ∈ K)
    (hstrict : ∀ y ∈ K, y ≠ x → f y < f x)
    (hconv : TendstoUniformlyOn F f l K)
    (hmax : ∀ᶠ i in l, z i ∈ K ∧ IsMaxOn (F i) K (z i)) :
    Tendsto z l (𝓝 x) := by
  apply tendsto_nhds.mpr
  intro U hU hxU
  by_cases hne : (K \ U).Nonempty
  · obtain ⟨y, hy, hyle⟩ := UpperSemicontinuousOn.exists_isMaxOn hne (hK.diff hU) (hf.mono _root_.Set.sdiff_subset)
    have hyx : y ≠ x := by intro heq; exact hy.2 (heq ▸ hxU)
    have hgap := hstrict y hy.1 hyx
    let eps := (f x - f y) / 3
    have heps : 0 < eps := by dsimp [eps]; linarith
    have he := (Metric.tendstoUniformlyOn_iff.mp hconv) eps heps
    filter_upwards [he, hmax] with i hi hmi
    by_contra hn
    have hzi := hyle ⟨hmi.1, hn⟩
    change f (z i) ≤ f y at hzi
    have hcompare : F i x ≤ F i (z i) := hmi.2 hx
    have hxi := hi x hx
    have hz := hi (z i) hmi.1
    rw [Real.dist_eq] at hxi hz
    have h1 := (abs_lt.mp hxi).2
    have h2 := (abs_lt.mp hz).1
    dsimp only [eps] at h1 h2
    linarith
  · filter_upwards [hmax] with i hi
    by_contra hn
    exact hne ⟨z i, hi.1, hn⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCompact.tendsto_of_isMaxOn_of_tendstoUniformlyOn then
    throwError "Refusing to shadow existing declaration IsCompact.tendsto_of_isMaxOn_of_tendstoUniformlyOn"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCompact.tendsto_of_isMaxOn_of_tendstoUniformlyOn ``Submission.IsCompact.tendsto_of_isMaxOn_of_tendstoUniformlyOn

open _root_.IsCompact in
theorem tendsto_of_isMinOn_of_tendstoUniformlyOn
    (hK : IsCompact K) (hf : LowerSemicontinuousOn f K) (hx : x ∈ K)
    (hstrict : ∀ y ∈ K, y ≠ x → f x < f y)
    (hconv : TendstoUniformlyOn F f l K)
    (hmin : ∀ᶠ i in l, z i ∈ K ∧ IsMinOn (F i) K (z i)) :
    Tendsto z l (𝓝 x) := by
  apply hK.tendsto_of_isMaxOn_of_tendstoUniformlyOn hf.neg hx
    (fun y hy hne => neg_lt_neg (hstrict y hy hne)) hconv.neg
  filter_upwards [hmin] with i hi
  refine ⟨hi.1, ?_⟩
  intro y hy
  change -F i y ≤ -F i (z i)
  exact neg_le_neg (hi.2 hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCompact.tendsto_of_isMinOn_of_tendstoUniformlyOn then
    throwError "Refusing to shadow existing declaration IsCompact.tendsto_of_isMinOn_of_tendstoUniformlyOn"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCompact.tendsto_of_isMinOn_of_tendstoUniformlyOn ``Submission.IsCompact.tendsto_of_isMinOn_of_tendstoUniformlyOn

open _root_.IsCompact in
theorem exists_tendsto_isLocalMax_of_tendstoUniformlyOn [l.NeBot]
    (hK : IsCompact K) (hx : K ∈ 𝓝 x)
    (hF : ∀ᶠ i in l, ContinuousOn (F i) K)
    (hstrict : ∀ y ∈ K, y ≠ x → f y < f x)
    (hconv : TendstoUniformlyOn F f l K) :
    ∃ z : ι → X, _root_.Filter.Tendsto z l (𝓝 x) ∧
      (∀ᶠ i in l, z i ∈ K ∧ IsMaxOn (F i) K (z i)) ∧
      ∀ᶠ i in l, IsLocalMax (F i) (z i) := by
  classical
  have hxK : x ∈ K := mem_of_mem_nhds hx
  have hex (i : ι) : ∃ y, y ∈ K ∧ (ContinuousOn (F i) K → IsMaxOn (F i) K y) := by
    by_cases hi : ContinuousOn (F i) K
    · obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn ⟨x, hxK⟩ hi
      exact ⟨y, hy, fun _ => hmax⟩
    · exact ⟨x, hxK, fun h => False.elim (hi h)⟩
  choose z hz hmax using hex
  have hmaxTail : ∀ᶠ i in l, z i ∈ K ∧ IsMaxOn (F i) K (z i) :=
    hF.mono fun i hi => ⟨hz i, hmax i hi⟩
  have hlim : _root_.Filter.Tendsto z l (𝓝 x) := hK.tendsto_of_isMaxOn_of_tendstoUniformlyOn
    (hconv.continuousOn hF.frequently).upperSemicontinuousOn hxK hstrict hconv
    hmaxTail
  refine ⟨z, hlim, hmaxTail, ?_⟩
  filter_upwards [hlim.eventually (interior_mem_nhds.mpr hx), hF] with i hi hFi
  exact (hmax i hFi).isLocalMax (mem_interior_iff_mem_nhds.mp hi)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCompact.exists_tendsto_isLocalMax_of_tendstoUniformlyOn then
    throwError "Refusing to shadow existing declaration IsCompact.exists_tendsto_isLocalMax_of_tendstoUniformlyOn"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCompact.exists_tendsto_isLocalMax_of_tendstoUniformlyOn ``Submission.IsCompact.exists_tendsto_isLocalMax_of_tendstoUniformlyOn

open _root_.IsCompact in
theorem exists_tendsto_isLocalMin_of_tendstoUniformlyOn [l.NeBot]
    (hK : IsCompact K) (hx : K ∈ 𝓝 x)
    (hF : ∀ᶠ i in l, ContinuousOn (F i) K)
    (hstrict : ∀ y ∈ K, y ≠ x → f x < f y)
    (hconv : TendstoUniformlyOn F f l K) :
    ∃ z : ι → X, _root_.Filter.Tendsto z l (𝓝 x) ∧
      (∀ᶠ i in l, z i ∈ K ∧ IsMinOn (F i) K (z i)) ∧
      ∀ᶠ i in l, IsLocalMin (F i) (z i) := by
  obtain ⟨z, hlim, hmax, hlocal⟩ := hK.exists_tendsto_isLocalMax_of_tendstoUniformlyOn hx
    (hF.mono fun _ hi => hi.neg) (fun y hy hne => neg_lt_neg (hstrict y hy hne)) hconv.neg
  refine ⟨z, hlim, ?_, ?_⟩
  · filter_upwards [hmax] with i hi
    refine ⟨hi.1, ?_⟩
    intro y hy
    change F i (z i) ≤ F i y
    exact neg_le_neg_iff.mp (hi.2 hy)
  · filter_upwards [hlocal] with i hi
    filter_upwards [hi] with y hy
    exact neg_le_neg_iff.mp hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCompact.exists_tendsto_isLocalMin_of_tendstoUniformlyOn then
    throwError "Refusing to shadow existing declaration IsCompact.exists_tendsto_isLocalMin_of_tendstoUniformlyOn"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCompact.exists_tendsto_isLocalMin_of_tendstoUniformlyOn ``Submission.IsCompact.exists_tendsto_isLocalMin_of_tendstoUniformlyOn

end IsCompact
