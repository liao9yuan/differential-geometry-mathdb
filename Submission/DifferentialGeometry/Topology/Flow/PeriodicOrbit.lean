import Mathlib.Dynamics.Flow
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Connected.Clopen

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.Flow

theorem exists_minimal_pos_period
    {X : Type*} [TopologicalSpace X] [T2Space X] (φ : _root_.Flow ℝ X) {x : X}
    (hnon : ∃ s : ℝ, φ s x ≠ x) (hreturn : ∃ t > 0, φ t x = x) :
    ∃ T > 0, Function.Periodic (fun t ↦ φ t x) T ∧
      InjOn (fun t ↦ φ t x) (_root_.Set.Ico 0 T) ∧ ∀ t > 0, φ t x = x → T ≤ t := by
  let S : AddSubgroup ℝ := {
    carrier := {t | φ t x = x}
    zero_mem' := φ.map_zero_apply x
    add_mem' := by
      intro s t hs ht
      change φ (s + t) x = x
      rw [φ.map_add, ht, hs]
    neg_mem' := by
      intro t ht
      have he := congrArg (φ (-t)) ht
      rw [← φ.map_add, neg_add_cancel, φ.map_zero_apply] at he
      exact he.symm }
  have hclosed : IsClosed (S : Set ℝ) :=
    isClosed_eq (φ.continuous continuous_id continuous_const) continuous_const
  have hnotdense : ¬ Dense (S : Set ℝ) := by
    intro hdense
    obtain ⟨s, hs⟩ := hnon
    have he : (S : Set ℝ) = univ := hclosed.closure_eq.symm.trans hdense.closure_eq
    apply hs
    change s ∈ (S : Set ℝ)
    rw [he]
    exact _root_.Set.mem_univ s
  have hbot : S ≠ ⊥ := by
    intro he
    obtain ⟨t, ht, hret⟩ := hreturn
    have hmem : t ∈ S := hret
    rw [he, AddSubgroup.mem_bot] at hmem
    exact ht.ne' hmem
  obtain ⟨T, hT⟩ : ∃ T, IsLeast {t : ℝ | t ∈ S ∧ 0 < t} T := by
    by_contra h
    exact hnotdense (S.dense_of_no_min hbot h)
  have hperiodic : Function.Periodic (fun t ↦ φ t x) T := by
    intro t
    change φ (t + T) x = φ t x
    rw [φ.map_add, show φ T x = x from hT.1.1]
  have horder (s t : ℝ) (hs : s ∈ _root_.Set.Ico 0 T) (ht : t ∈ _root_.Set.Ico 0 T)
      (hst : s < t) (he : φ s x = φ t x) : False := by
    have hret : t - s ∈ S := by
      change φ (t - s) x = x
      calc
        φ (t - s) x = φ (-s) (φ t x) := by rw [← φ.map_add]; congr 1; ring
        _ = φ (-s) (φ s x) := congrArg (φ (-s)) he.symm
        _ = x := by rw [← φ.map_add, neg_add_cancel, φ.map_zero_apply]
    have hmin := hT.2 ⟨hret, sub_pos.mpr hst⟩
    linarith [hs.1, ht.2]
  refine ⟨T, hT.1.2, hperiodic, ?_, fun t ht hret ↦ hT.2 ⟨hret, ht⟩⟩
  intro s hs t ht he
  rcases lt_trichotomy s t with h | h | h
  · exact (horder s t hs ht h he).elim
  · exact h
  · exact (horder t s ht hs h he.symm).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Flow.exists_minimal_pos_period then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Flow.exists_minimal_pos_period"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Flow.exists_minimal_pos_period ``Submission.DifferentialGeometry.Topology.Flow.exists_minimal_pos_period

theorem exists_simple_closed_curve_of_periodic_orbit
    {X : Type*} [TopologicalSpace X] [T2Space X] (φ : _root_.Flow ℝ X) {x : X}
    (hnon : ∃ s : ℝ, φ s x ≠ x) (hreturn : ∃ t > 0, φ t x = x) :
    ∃ γ : ℝ → X, Continuous γ ∧ γ 0 = γ 1 ∧ _root_.Set.InjOn γ (_root_.Set.Ico 0 1) ∧
      γ '' _root_.Set.Icc 0 1 = φ.orbit x := by
  obtain ⟨T, hT, hper, hinj, _⟩ :=
    exists_minimal_pos_period φ hnon hreturn
  let γ : ℝ → X := fun t ↦ φ (T * t) x
  have hγ : Continuous γ := φ.continuous (continuous_const.mul continuous_id) continuous_const
  have hclose : γ 0 = γ 1 := by
    simpa only [γ, _root_.MulZeroClass.mul_zero, mul_one, zero_add] using (hper 0).symm
  have hsimple : _root_.Set.InjOn γ (_root_.Set.Ico 0 1) := by
    intro s hs t ht he
    have hm (r : ℝ) (hr : r ∈ _root_.Set.Ico 0 1) : T * r ∈ _root_.Set.Ico 0 T :=
      ⟨mul_nonneg hT.le hr.1, by nlinarith [hr.2]⟩
    exact mul_left_cancel₀ hT.ne' (hinj (hm s hs) (hm t ht) he)
  have himage : γ '' _root_.Set.Icc 0 1 = φ.orbit x := by
    apply Subset.antisymm
    · rintro z ⟨t, _, rfl⟩
      exact φ.mem_orbit x (T * t)
    · rintro z ⟨s, rfl⟩
      obtain ⟨r, hr, he⟩ := hper.exists_mem_Ico₀ hT s
      refine ⟨r / T, ⟨div_nonneg hr.1 hT.le, (div_le_one hT).mpr hr.2.le⟩, ?_⟩
      change φ (T * (r / T)) x = φ s x
      have hcancel : T * (r / T) = r := by field_simp
      rw [hcancel]
      exact he.symm
  exact ⟨γ, hγ, hclose, hsimple, himage⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Flow.exists_simple_closed_curve_of_periodic_orbit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Flow.exists_simple_closed_curve_of_periodic_orbit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Flow.exists_simple_closed_curve_of_periodic_orbit ``Submission.DifferentialGeometry.Topology.Flow.exists_simple_closed_curve_of_periodic_orbit

theorem orbit_eq_univ_of_isOpenMap
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] (φ : _root_.Flow ℝ X)
    (hopen : ∀ x, IsOpenMap (fun t : ℝ => φ t x)) (x : X) : φ.orbit x = univ := by
  have ho (y : X) : IsOpen (φ.orbit y) := (hopen y).isOpen_range
  have hc : IsOpen (φ.orbit x)ᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    apply Filter.mem_of_superset ((ho y).mem_nhds (φ.mem_orbit_self y))
    rintro z ⟨t, rfl⟩ hz
    have hback := φ.mem_orbit_of_mem_orbit (-t) hz
    change φ (-t) (φ t y) ∈ φ.orbit x at hback
    apply hy
    simpa only [← φ.map_add, neg_add_cancel, φ.map_zero_apply] using hback
  exact IsClopen.eq_univ ⟨by simpa only [compl_compl] using hc.isClosed_compl, ho x⟩
    (φ.nonempty_orbit x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Flow.orbit_eq_univ_of_isOpenMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Flow.orbit_eq_univ_of_isOpenMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Flow.orbit_eq_univ_of_isOpenMap ``Submission.DifferentialGeometry.Topology.Flow.orbit_eq_univ_of_isOpenMap

theorem exists_pos_period_of_isOpenMap
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] [CompactSpace X]
    (φ : _root_.Flow ℝ X) (hopen : ∀ x, IsOpenMap (fun t : ℝ => φ t x)) (x : X) :
    ∃ T > 0, φ T x = x := by
  have hsurj : Function.Surjective (fun t : ℝ => φ t x) := by
    rw [← Set.range_eq_univ, ← φ.orbit_eq_range]
    exact orbit_eq_univ_of_isOpenMap φ hopen x
  by_contra hreturn
  push Not at hreturn
  have hlt : ∀ s t : ℝ, s < t → φ s x ≠ φ t x := by
    intro s t hst he
    apply hreturn (t - s) (sub_pos.mpr hst)
    calc
      φ (t - s) x = φ (-s) (φ t x) := by rw [← φ.map_add]; congr 1; ring
      _ = φ (-s) (φ s x) := congrArg (φ (-s)) he.symm
      _ = x := by rw [← φ.map_add, neg_add_cancel, φ.map_zero_apply]
  have hinj : Function.Injective (fun t : ℝ => φ t x) := by
    intro s t he
    rcases lt_trichotomy s t with hst | hst | hst
    · exact (hlt s t hst he).elim
    · exact hst
    · exact (hlt t s hst he.symm).elim
  let e : ℝ ≃ₜ X := (Equiv.ofBijective (fun t : ℝ => φ t x) ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen (φ.continuous continuous_id continuous_const) (hopen x)
  have hc : CompactSpace ℝ := e.symm.compactSpace
  exact (not_compactSpace_iff.mpr inferInstance) hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Flow.exists_pos_period_of_isOpenMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Flow.exists_pos_period_of_isOpenMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Flow.exists_pos_period_of_isOpenMap ``Submission.DifferentialGeometry.Topology.Flow.exists_pos_period_of_isOpenMap

end DifferentialGeometry.Topology.Flow
