import Submission.DifferentialGeometry.Topology.LoopSpace.UniformSmoothing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.ContinuousMap _root_.Function
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {K Q : Type*} [TopologicalSpace K] [TopologicalSpace Q]


def periodicLoop (f : ℝ → Q) (hp : _root_.Function.Periodic f 1) (hc : Continuous f) : freeLoop Q :=
  ⟨hp.lift, hc.quotient_liftOn' _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.periodicLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.periodicLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.periodicLoop ``Submission.DifferentialGeometry.Topology.periodicLoop

@[simp] theorem periodicLoop_coe (f : ℝ → Q) (hp : _root_.Function.Periodic f 1) (hc : Continuous f) (t : ℝ) :
    periodicLoop f hp hc (t : loopCircle) = f t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.periodicLoop_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.periodicLoop_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.periodicLoop_coe ``Submission.DifferentialGeometry.Topology.periodicLoop_coe



theorem continuous_periodic_family {f : K × ℝ → Q} (hf : Continuous f)
    (hp : ∀ k, _root_.Function.Periodic (fun t => f (k, t)) 1) :
    Continuous (fun p : K × loopCircle => (hp p.1).lift p.2) := by
  have hq := (_root_.IsOpenQuotientMap.id (X := K)).prodMap
    (QuotientAddGroup.isOpenQuotientMap_mk (N := AddSubgroup.zmultiples (1 : ℝ)))
  apply hq.isQuotientMap.continuous_iff.mpr
  exact hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_periodic_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_periodic_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_periodic_family ``Submission.DifferentialGeometry.Topology.continuous_periodic_family


theorem continuous_periodicLoop_family {f : K × ℝ → Q} (hf : Continuous f)
    (hp : ∀ k, _root_.Function.Periodic (fun t => f (k, t)) 1) :
    Continuous (fun k => periodicLoop (fun t => f (k, t)) (hp k)
      (hf.comp (continuous_const.prodMk continuous_id))) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_periodic_family hf hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_periodicLoop_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_periodicLoop_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_periodicLoop_family ``Submission.DifferentialGeometry.Topology.continuous_periodicLoop_family

open _root_.Set in
theorem continuous_of_continuousOn_Icc_of_add_one {K X : Type*} [TopologicalSpace K]
    [TopologicalSpace X] {g : K × ℝ → X} (hcont : ContinuousOn g (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hper : ∀ k t, g (k, t + 1) = g (k, t)) : Continuous g := by
  have hper_nat : ∀ n : ℕ, ∀ k t, g (k, t + (n : ℝ)) = g (k, t) := by
    intro n
    induction n with
    | zero => intro k t; simp
    | succ n ih =>
        intro k t
        have h1 : g (k, t + (n : ℝ) + 1) = g (k, t + (n : ℝ)) := hper k (t + (n : ℝ))
        have h2 : t + ((n : ℝ) + 1) = t + (n : ℝ) + 1 := by ring
        rw [Nat.cast_succ, h2, h1, ih]
  have hper_int : ∀ m : ℤ, ∀ k t, g (k, t + (m : ℝ)) = g (k, t) := by
    intro m k t
    rcases le_or_gt (0 : ℤ) m with hm | hm
    · have hcast : (m.toNat : ℝ) = (m : ℝ) := by
        exact_mod_cast (Int.toNat_of_nonneg hm : (m.toNat : ℤ) = m)
      rw [← hcast]
      exact hper_nat m.toNat k t
    · have hcast : ((-m).toNat : ℝ) = ((-m : ℤ) : ℝ) := by
        have h0 : (0 : ℤ) ≤ -m := by omega
        exact_mod_cast (Int.toNat_of_nonneg h0 : ((-m).toNat : ℤ) = -m)
      have h := hper_nat ((-m).toNat) k (t + (m : ℝ))
      rw [hcast] at h
      have h2 : t + (m : ℝ) + ((-m : ℤ) : ℝ) = t := by push_cast; ring
      rw [h2] at h
      exact h.symm
  have hstrip : ∀ m : ℤ, ContinuousOn g (_root_.Set.univ ×ˢ _root_.Set.Icc ((m : ℝ)) ((m : ℝ) + 1)) := by
    intro m
    have hshift : ContinuousOn (fun p : K × ℝ => (p.1, p.2 - (m : ℝ)))
        (_root_.Set.univ ×ˢ _root_.Set.Icc ((m : ℝ)) ((m : ℝ) + 1)) :=
      (continuous_fst.continuousOn).prodMk
        ((continuous_snd.continuousOn).sub continuous_const.continuousOn)
    have hmaps : _root_.Set.MapsTo (fun p : K × ℝ => (p.1, p.2 - (m : ℝ)))
        (_root_.Set.univ ×ˢ _root_.Set.Icc ((m : ℝ)) ((m : ℝ) + 1)) (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
      rintro ⟨k, t⟩ ⟨-, ht⟩
      refine ⟨trivial, ?_, ?_⟩ <;> linarith [ht.1, ht.2]
    have hcomp : ContinuousOn (g ∘ fun p : K × ℝ => (p.1, p.2 - (m : ℝ)))
        (_root_.Set.univ ×ˢ _root_.Set.Icc ((m : ℝ)) ((m : ℝ) + 1)) :=
      hcont.comp hshift hmaps
    refine hcomp.congr ?_
    rintro ⟨k, t⟩ -
    have h := hper_int m k (t - (m : ℝ))
    have hsub : t - (m : ℝ) + (m : ℝ) = t := by ring
    rw [hsub] at h
    exact h
  rw [continuous_iff_continuousAt]
  rintro ⟨k₀, t₀⟩
  set m : ℤ := ⌊t₀⌋ with hm
  have hlt : (m : ℝ) ≤ t₀ := by rw [hm]; exact Int.floor_le t₀
  have hgt : t₀ < (m : ℝ) + 1 := by rw [hm]; exact Int.lt_floor_add_one t₀
  have hc : ContinuousOn g (_root_.Set.univ ×ˢ _root_.Set.Icc ((m : ℝ) - 1) ((m : ℝ) + 1)) := by
    have h₁ := hstrip (m - 1)
    have h₂ := hstrip m
    have hcast : (((m - 1 : ℤ)) : ℝ) = (m : ℝ) - 1 := by push_cast; ring
    rw [hcast] at h₁
    have hadd : (m : ℝ) - 1 + 1 = (m : ℝ) := by ring
    rw [hadd] at h₁
    have hunion : ((_root_.Set.univ : Set K) ×ˢ _root_.Set.Icc ((m : ℝ) - 1) (m : ℝ)) ∪
        ((_root_.Set.univ : Set K) ×ˢ _root_.Set.Icc (m : ℝ) ((m : ℝ) + 1)) =
        (_root_.Set.univ : Set K) ×ˢ _root_.Set.Icc ((m : ℝ) - 1) ((m : ℝ) + 1) := by
      ext p
      simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, Set.mem_Icc, true_and]
      constructor
      · rintro (⟨ht1, ht2⟩ | ⟨ht1, ht2⟩)
        · exact ⟨by linarith, by linarith⟩
        · exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩
        rcases le_total p.2 (m : ℝ) with h | h
        · exact Or.inl ⟨h1, h⟩
        · exact Or.inr ⟨h, h2⟩
    rw [← hunion]
    have hc₁ : IsClosed ((_root_.Set.univ : Set K) ×ˢ _root_.Set.Icc ((m : ℝ) - 1) (m : ℝ)) :=
      isClosed_univ.prod isClosed_Icc
    have hc₂ : IsClosed ((_root_.Set.univ : Set K) ×ˢ _root_.Set.Icc ((m : ℝ)) ((m : ℝ) + 1)) :=
      isClosed_univ.prod isClosed_Icc
    exact h₁.union_of_isClosed h₂ hc₁ hc₂
  refine hc.continuousAt ?_
  have h1 : (m : ℝ) - 1 < t₀ := by linarith
  have h2 : t₀ < (m : ℝ) + 1 := by linarith
  refine Filter.mem_of_superset (prod_mem_nhds
    (Filter.univ_mem : (_root_.Set.univ : Set K) ∈ 𝓝 k₀)
    (Ioo_mem_nhds h1 h2)) ?_
  rintro ⟨k, t⟩ ⟨-, ht⟩
  exact ⟨trivial, le_of_lt ht.1, le_of_lt ht.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_of_continuousOn_Icc_of_add_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_of_continuousOn_Icc_of_add_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_of_continuousOn_Icc_of_add_one ``Submission.DifferentialGeometry.Topology.continuous_of_continuousOn_Icc_of_add_one

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]


def averagedLoop (φ : ContDiffBump (0 : ℝ)) (γ : freeLoop F) : freeLoop F :=
  periodicLoop (DifferentialGeometry.Analysis.smoothPeriodic φ (fun t : ℝ => γ (t : loopCircle)))
    (DifferentialGeometry.Analysis.smoothPeriodic_periodic φ (by
      intro t
      simp only [QuotientAddGroup.mk_add, AddCircle.coe_period, add_zero]))
    (DifferentialGeometry.Analysis.smoothPeriodic_contDiff φ
      (γ.continuous.comp (AddCircle.continuous_mk' (1 : ℝ)))).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.averagedLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.averagedLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.averagedLoop ``Submission.DifferentialGeometry.Topology.averagedLoop

@[simp] theorem averagedLoop_coe (φ : ContDiffBump (0 : ℝ)) (γ : freeLoop F) (t : ℝ) :
    averagedLoop φ γ (t : loopCircle) =
      DifferentialGeometry.Analysis.smoothPeriodic φ (fun s : ℝ => γ (s : loopCircle)) t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.averagedLoop_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.averagedLoop_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.averagedLoop_coe ``Submission.DifferentialGeometry.Topology.averagedLoop_coe

@[simp] theorem averagedLoop_const [CompleteSpace F] (φ : ContDiffBump (0 : ℝ)) (v : F) :
    averagedLoop φ (.const loopCircle v) = .const loopCircle v := by
  ext θ
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  exact congrFun (DifferentialGeometry.Analysis.smoothPeriodic_const φ v) t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.averagedLoop_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.averagedLoop_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.averagedLoop_const ``Submission.DifferentialGeometry.Topology.averagedLoop_const

theorem averagedLoop_continuous_family (φ : ContDiffBump (0 : ℝ))
    {Γ : K → freeLoop F} (hΓ : Continuous Γ) :
    Continuous (fun k => averagedLoop φ (Γ k)) := by
  have hf : Continuous (fun p : K × ℝ => Γ p.1 (p.2 : loopCircle)) :=
    continuous_eval.comp ((hΓ.comp continuous_fst).prodMk
      ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd))
  have hs := DifferentialGeometry.Analysis.continuous_iteratedDeriv_smoothPeriodic φ hf 0
  simp only [iteratedDeriv_zero] at hs
  exact continuous_periodicLoop_family hs _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.averagedLoop_continuous_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.averagedLoop_continuous_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.averagedLoop_continuous_family ``Submission.DifferentialGeometry.Topology.averagedLoop_continuous_family

end DifferentialGeometry.Topology
