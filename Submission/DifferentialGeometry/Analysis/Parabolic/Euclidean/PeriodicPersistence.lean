import Submission.DifferentialGeometry.Topology.Compactness.TimeInterval
import Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.PeriodicJet
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_Icc_firstJet_mem_and_pos_le_of_periodic
    {u : ℝ → ℝ → E} {s T : ℝ} (hsT : s < T)
    (hper : ∀ x t, u (x + 1) t = u x t)
    (hu : ContinuousOn (Function.uncurry u) (_root_.Set.Icc 0 1 ×ˢ _root_.Set.Icc s T))
    (hDu : ContinuousOn (fun p : ℝ × ℝ => deriv (fun y => u y p.2) p.1)
      (_root_.Set.Icc 0 1 ×ˢ _root_.Set.Icc s T))
    {U : Set (ℝ × E × E)} (hU : IsOpen U)
    {a : ℝ × E × E → ℝ} (ha : ContinuousOn a U)
    (hinit : ∀ x ∈ _root_.Set.Icc (0 : ℝ) 1, (s, u x s, deriv (fun y => u y s) x) ∈ U)
    (hapos : ∀ x ∈ _root_.Set.Icc (0 : ℝ) 1, 0 < a (s, u x s, deriv (fun y => u y s) x)) :
    ∃ τ δ : ℝ, 0 < τ ∧ τ ≤ T - s ∧ 0 < δ ∧
      ∀ x t, t ∈ _root_.Set.Icc s (s + τ) →
        (t, u x t, deriv (fun y => u y t) x) ∈ U ∧
        δ ≤ a (t, u x t, deriv (fun y => u y t) x) := by
  let Φ : ℝ × ℝ → ℝ × E × E :=
    fun p => (p.2, u p.1 p.2, deriv (fun y => u y p.2) p.1)
  have hΦ : ContinuousOn Φ (_root_.Set.Icc 0 1 ×ˢ _root_.Set.Icc s T) :=
    continuousOn_snd.prodMk (hu.prodMk hDu)
  have hΦs : ContinuousOn (fun x => Φ (x, s)) (_root_.Set.Icc 0 1) :=
    hΦ.comp (continuousOn_id.prodMk continuousOn_const)
      (fun _ hx => ⟨hx, le_rfl, hsT.le⟩)
  have has : ContinuousOn (fun x => a (Φ (x, s))) (_root_.Set.Icc 0 1) :=
    ha.comp hΦs hinit
  obtain ⟨d, hd, hdle⟩ := isCompact_Icc.exists_forall_le' has hapos
  let W := U ∩ a ⁻¹' _root_.Set.Ioi (d / 2)
  have hW : IsOpen W := ha.isOpen_inter_preimage hU isOpen_Ioi
  have hWinit : ∀ x ∈ _root_.Set.Icc (0 : ℝ) 1, Φ (x, s) ∈ W := by
    intro x hx
    exact ⟨hinit x hx, lt_of_lt_of_le (half_lt_self hd) (hdle x hx)⟩
  obtain ⟨τ, hτ, hτT, hτW⟩ :=
    IsCompact.exists_Icc_mapsTo_of_continuousOn _root_.CompactIccSpace.isCompact_Icc hsT hW hΦ hWinit
  refine ⟨τ, d / 2, hτ, hτT, half_pos hd, ?_⟩
  intro x t ht
  have hp : Function.Periodic (fun y => Φ (y, t)) 1 := by
    intro y
    dsimp only [Φ]
    rw [hper, (show Function.Periodic (fun z => u z t) 1 from fun z => hper z t).deriv y]
  obtain ⟨y, hy, hxy⟩ := hp.exists_mem_Ico₀ (by norm_num : (0 : ℝ) < 1) x
  have hw : Φ (x, t) ∈ W := hxy.symm ▸ hτW y ⟨hy.1, hy.2.le⟩ t ht
  exact ⟨hw.1, hw.2.le⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.exists_Icc_firstJet_mem_and_pos_le_of_periodic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.exists_Icc_firstJet_mem_and_pos_le_of_periodic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.exists_Icc_firstJet_mem_and_pos_le_of_periodic ``Submission.DifferentialGeometry.Analysis.Parabolic.exists_Icc_firstJet_mem_and_pos_le_of_periodic

end DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_Icc_firstJet_mem_and_projected_mem_of_periodic
    {u : ℝ → ℝ → E} {s T : ℝ} (hsT : s < T)
    (hper : ∀ x t, u (x + 1) t = u x t)
    (hu : ContinuousOn (Function.uncurry u) (_root_.Set.Icc 0 1 ×ˢ _root_.Set.Icc s T))
    (hDu : ContinuousOn (fun p : ℝ × ℝ => deriv (fun y => u y p.2) p.1)
      (_root_.Set.Icc 0 1 ×ˢ _root_.Set.Icc s T))
    {U : Set (ℝ × E × E)} (hU : IsOpen U)
    (hinit : ∀ x ∈ _root_.Set.Icc (0 : ℝ) 1,
      (s, u x s, deriv (fun y => u y s) x) ∈ U)
    {Z : Type*} [TopologicalSpace Z]
    {Q : (ℝ × E × E) → Z} (hQ : ContinuousOn Q U)
    {V : Set Z} (hV : IsOpen V)
    (hQinit : ∀ x ∈ _root_.Set.Icc (0 : ℝ) 1,
      Q (s, u x s, deriv (fun y => u y s) x) ∈ V) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ T - s ∧
      ∀ x t, t ∈ _root_.Set.Icc s (s + τ) →
        (t, u x t, deriv (fun y => u y t) x) ∈ U ∧
        Q (t, u x t, deriv (fun y => u y t) x) ∈ V := by
  let Φ : ℝ × ℝ → ℝ × E × E :=
    fun p => (p.2, u p.1 p.2, deriv (fun y => u y p.2) p.1)
  have hΦ : ContinuousOn Φ (_root_.Set.Icc 0 1 ×ˢ _root_.Set.Icc s T) :=
    continuousOn_snd.prodMk (hu.prodMk hDu)
  let W : Set (ℝ × E × E) := U ∩ Q ⁻¹' V
  have hW : IsOpen W := hQ.isOpen_inter_preimage hU hV
  have hWinit : ∀ x ∈ _root_.Set.Icc (0 : ℝ) 1, Φ (x, s) ∈ W := by
    intro x hx
    exact ⟨hinit x hx, hQinit x hx⟩
  obtain ⟨τ, hτ, hτT, hτW⟩ :=
    IsCompact.exists_Icc_mapsTo_of_continuousOn _root_.CompactIccSpace.isCompact_Icc hsT hW hΦ hWinit
  refine ⟨τ, hτ, hτT, ?_⟩
  intro x t ht
  have hp : Function.Periodic (fun y => Φ (y, t)) 1 := by
    intro y
    dsimp only [Φ]
    rw [hper, (show Function.Periodic (fun z => u z t) 1 from fun z => hper z t).deriv y]
  obtain ⟨y, hy, hxy⟩ := hp.exists_mem_Ico₀ (by norm_num : (0 : ℝ) < 1) x
  have hw : Φ (x, t) ∈ W := hxy.symm ▸ hτW y ⟨hy.1, hy.2.le⟩ t ht
  exact ⟨hw.1, hw.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.exists_Icc_firstJet_mem_and_projected_mem_of_periodic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.exists_Icc_firstJet_mem_and_projected_mem_of_periodic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.exists_Icc_firstJet_mem_and_projected_mem_of_periodic ``Submission.DifferentialGeometry.Analysis.Parabolic.exists_Icc_firstJet_mem_and_projected_mem_of_periodic

end DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_isCompact_firstJet_image_subset_of_periodic
    {u : ℝ → ℝ → E} {s T : ℝ} (hsT : s < T)
    (hper : ∀ x t, u (x + 1) t = u x t)
    (hu : ContinuousOn (Function.uncurry u) (_root_.Set.Icc 0 1 ×ˢ _root_.Set.Icc s T))
    (hDu : ContinuousOn (fun p : ℝ × ℝ => deriv (fun y => u y p.2) p.1)
      (_root_.Set.Icc 0 1 ×ˢ _root_.Set.Icc s T))
    {U : Set (ℝ × E × E)} (hU : IsOpen U)
    {Q : (ℝ × E × E) → ℝ × E × E} (hQ : ContinuousOn Q U)
    (hinit : ∀ x ∈ _root_.Set.Icc (0 : ℝ) 1,
      (s, u x s, deriv (fun y => u y s) x) ∈ U)
    (hQinit : ∀ x ∈ _root_.Set.Icc (0 : ℝ) 1,
      Q (s, u x s, deriv (fun y => u y s) x) =
        (s, u x s, deriv (fun y => u y s) x)) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ T - s ∧
      let K := (fun p : ℝ × ℝ => (p.2, u p.1 p.2, deriv (fun y => u y p.2) p.1)) ''
        (_root_.Set.univ ×ˢ _root_.Set.Icc s (s + τ))
      IsCompact K ∧ K ⊆ U ∩ Q ⁻¹' U := by
  obtain ⟨τ, hτ, hτT, hτmem⟩ :=
    exists_Icc_firstJet_mem_and_projected_mem_of_periodic hsT hper hu hDu hU hinit hQ hU
      (fun x hx => (hQinit x hx).symm ▸ hinit x hx)
  have hsub : _root_.Set.Icc s (s + τ) ⊆ _root_.Set.Icc s T :=
    _root_.Set.Icc_subset_Icc le_rfl (by linarith)
  refine ⟨τ, hτ, hτT, isCompact_image_firstJet_of_periodic hper
    (hu.mono (_root_.Set.prod_mono Subset.rfl hsub)) (hDu.mono (_root_.Set.prod_mono Subset.rfl hsub)), ?_⟩
  rintro _ ⟨⟨x, t⟩, hxt, rfl⟩
  exact hτmem x t hxt.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.exists_isCompact_firstJet_image_subset_of_periodic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.exists_isCompact_firstJet_image_subset_of_periodic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.exists_isCompact_firstJet_image_subset_of_periodic ``Submission.DifferentialGeometry.Analysis.Parabolic.exists_isCompact_firstJet_image_subset_of_periodic

end DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_isCompact_firstJet_image_subset_of_initial_curve_fixed
    {u : ℝ → ℝ → E} {s T : ℝ} (hsT : s < T)
    (hper : ∀ x t, u (x + 1) t = u x t)
    (hu : ContinuousOn (Function.uncurry u) (_root_.Set.Icc 0 1 ×ˢ _root_.Set.Icc s T))
    (hDu : ContinuousOn (fun p : ℝ × ℝ => deriv (fun y => u y p.2) p.1)
      (_root_.Set.Icc 0 1 ×ˢ _root_.Set.Icc s T))
    {U : Set (ℝ × E × E)} (hU : IsOpen U)
    {P : E → E} {V : Set E} (hV : IsOpen V) (hP : ContDiffOn ℝ 1 P V)
    (hUV : ∀ q ∈ U, q.2.1 ∈ V)
    (hinit : ∀ x ∈ _root_.Set.Icc (0 : ℝ) 1,
      (s, u x s, deriv (fun y => u y s) x) ∈ U)
    (hfix : ∀ x, P (u x s) = u x s)
    (hdinit : ∀ x ∈ _root_.Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ (fun y => u y s) x) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ T - s ∧
      let K := (fun p : ℝ × ℝ => (p.2, u p.1 p.2, deriv (fun y => u y p.2) p.1)) ''
        (_root_.Set.univ ×ˢ _root_.Set.Icc s (s + τ))
      IsCompact K ∧ K ⊆ U ∩
        (fun q : ℝ × E × E => (q.1, P q.2.1, fderiv ℝ P q.2.1 q.2.2)) ⁻¹' U := by
  let Q : (ℝ × E × E) → ℝ × E × E :=
    fun q => (q.1, P q.2.1, fderiv ℝ P q.2.1 q.2.2)
  have hQ : ContinuousOn Q U := by
    apply continuousOn_fst.prodMk
    apply ContinuousOn.prodMk
    · exact hP.continuousOn.comp continuousOn_snd.fst hUV
    · exact ((hP.continuousOn_fderiv_of_isOpen hV le_rfl).comp
        continuousOn_snd.fst hUV).clm_apply continuousOn_snd.snd
  apply exists_isCompact_firstJet_image_subset_of_periodic hsT hper hu hDu hU hQ hinit
  intro x hx
  have hdP : DifferentiableAt ℝ P (u x s) :=
    (hP.contDiffAt (hV.mem_nhds (hUV _ (hinit x hx)))).differentiableAt (by norm_num)
  have heq : P ∘ (fun y => u y s) = (fun y => u y s) := funext hfix
  have hd : fderiv ℝ P (u x s) (deriv (fun y => u y s) x) =
      deriv (fun y => u y s) x := by
    rw [← fderiv_comp_deriv x hdP (hdinit x hx), heq]
  exact Prod.ext rfl (Prod.ext (hfix x) hd)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.exists_isCompact_firstJet_image_subset_of_initial_curve_fixed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.exists_isCompact_firstJet_image_subset_of_initial_curve_fixed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.exists_isCompact_firstJet_image_subset_of_initial_curve_fixed ``Submission.DifferentialGeometry.Analysis.Parabolic.exists_isCompact_firstJet_image_subset_of_initial_curve_fixed

end DifferentialGeometry.Analysis.Parabolic
