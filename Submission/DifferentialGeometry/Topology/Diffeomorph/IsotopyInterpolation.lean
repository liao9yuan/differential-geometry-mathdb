import Submission.DifferentialGeometry.Analysis.Calculus.SmoothExtension.ConvexOpen
import Submission.DifferentialGeometry.Topology.Diffeomorph.SphereCollar
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric _root_.Filter
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace Diffeomorph
open _root_.Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ∞}

open _root_.Diffeomorph in
private theorem exists_contDiff_family_eqOn_of_time_map
    (Ψ P : ℝ → E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E)
    (hΨ : ContDiff ℝ n (fun z : ℝ × E => Ψ z.1 z.2))
    (hΨi : ContDiff ℝ n (fun z : ℝ × E => (Ψ z.1).symm z.2))
    (hP : ContDiff ℝ n (fun z : ℝ × E => P z.1 z.2))
    (hPi : ContDiff ℝ n (fun z : ℝ × E => (P z.1).symm z.2))
    {c : ℝ} (hc : P c = Ψ c) {J U : Set ℝ} {K : Set E}
    (himage : ∀ t ∈ J, P t '' K = Ψ t '' K)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ n ψ) (hψrange : _root_.Set.range ψ ⊆ J)
    (hψU : _root_.Set.EqOn ψ id U) (hψout : _root_.Set.EqOn ψ (fun _ => c) Jᶜ) :
    ∃ F : ℝ → E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E,
      ContDiff ℝ n (fun z : ℝ × E => F z.1 z.2) ∧
      ContDiff ℝ n (fun z : ℝ × E => (F z.1).symm z.2) ∧
      (∀ t x, F t x = Ψ t ((Ψ (ψ t)).symm (P (ψ t) x))) ∧
      _root_.Set.EqOn F P U ∧ _root_.Set.EqOn F Ψ Jᶜ ∧
      ∀ t, F t '' K = Ψ t '' K := by
  let F : ℝ → E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E :=
    fun t => (P (ψ t)).trans ((Ψ (ψ t)).symm.trans (Ψ t))
  have hψfst : ContDiff ℝ n (fun z : ℝ × E => ψ z.1) := hψ.comp contDiff_fst
  have hFP : ContDiff ℝ n (fun z : ℝ × E => P (ψ z.1) z.2) :=
    hP.comp (hψfst.prodMk contDiff_snd)
  have hF : ContDiff ℝ n (fun z : ℝ × E => F z.1 z.2) :=
    hΨ.comp (contDiff_fst.prodMk (hΨi.comp (hψfst.prodMk hFP)))
  have hFi : ContDiff ℝ n (fun z : ℝ × E => (F z.1).symm z.2) :=
    hPi.comp (hψfst.prodMk (hΨ.comp (hψfst.prodMk hΨi)))
  refine ⟨F, hF, hFi, (fun _ _ => rfl), ?_, ?_, ?_⟩
  · intro t ht
    ext x
    change Ψ t ((Ψ (ψ t)).symm (P (ψ t) x)) = P t x
    rw [hψU ht, id_eq, (Ψ t).apply_symm_apply]
  · intro t ht
    ext x
    change Ψ t ((Ψ (ψ t)).symm (P (ψ t) x)) = Ψ t x
    rw [hψout ht, hc, (Ψ c).symm_apply_apply]
  · intro t
    calc
      F t '' K = Ψ t '' ((Ψ (ψ t)).symm '' (P (ψ t) '' K)) := by
        rw [_root_.Set.image_image, _root_.Set.image_image]
        rfl
      _ = Ψ t '' K := by
        rw [himage (ψ t) (hψrange (_root_.Set.mem_range_self t)), (Ψ (ψ t)).symm_image_image]

run_cmd do
  let target := ``Submission.Diffeomorph.exists_contDiff_family_eqOn_of_time_map
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.exists_contDiff_family_eqOn_of_time_map target :: scope.openDecls } }

open _root_.Diffeomorph in
theorem exists_contDiff_family_eqOn_of_image_eq
    (Ψ P : ℝ → E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E)
    (hΨ : ContDiff ℝ n (fun z : ℝ × E => Ψ z.1 z.2))
    (hΨi : ContDiff ℝ n (fun z : ℝ × E => (Ψ z.1).symm z.2))
    (hP : ContDiff ℝ n (fun z : ℝ × E => P z.1 z.2))
    (hPi : ContDiff ℝ n (fun z : ℝ × E => (P z.1).symm z.2))
    {a b c : ℝ} (hac : a < c) (hcb : c < b) (hc : P c = Ψ c)
    {K : Set E} (himage : ∀ t ∈ _root_.Set.Ioo a b, P t '' K = Ψ t '' K) :
    ∃ ψ : ℝ → ℝ, ∃ ε > 0, ContDiff ℝ ∞ ψ ∧ _root_.Set.range ψ ⊆ _root_.Set.Ioo a b ∧
      _root_.Set.Ioo (c - ε) (c + ε) ⊆ _root_.Set.Ioo a b ∧
      _root_.Set.EqOn ψ id (_root_.Set.Ioo (c - ε) (c + ε)) ∧ _root_.Set.EqOn ψ (fun _ => c) (_root_.Set.Ioo a b)ᶜ ∧
      ∃ F : ℝ → E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E,
        ContDiff ℝ n (fun z : ℝ × E => F z.1 z.2) ∧
        ContDiff ℝ n (fun z : ℝ × E => (F z.1).symm z.2) ∧
        (∀ t x, F t x = Ψ t ((Ψ (ψ t)).symm (P (ψ t) x))) ∧
        _root_.Set.EqOn F P (_root_.Set.Ioo (c - ε) (c + ε)) ∧ _root_.Set.EqOn F Ψ (_root_.Set.Ioo a b)ᶜ ∧
        ∀ t, F t '' K = Ψ t '' K := by
  obtain ⟨ψ, ε, hε, hψ, hψrange, hεsub, hψid, hψout⟩ :=
    DifferentialGeometry.Analysis.exists_contDiff_range_subset_eqOn_nhds_Ioo hac hcb
  have hψn : ContDiff ℝ n ψ := hψ.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨F, hF, hFi, hFformula, hFU, hFout, hFK⟩ :=
    exists_contDiff_family_eqOn_of_time_map Ψ P hΨ hΨi hP hPi hc himage
      ψ hψn hψrange hψid hψout
  exact ⟨ψ, ε, hε, hψ, hψrange, hεsub, hψid, hψout,
    F, hF, hFi, hFformula, hFU, hFout, hFK⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.exists_contDiff_family_eqOn_of_image_eq then
    throwError "Refusing to shadow existing declaration Diffeomorph.exists_contDiff_family_eqOn_of_image_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.exists_contDiff_family_eqOn_of_image_eq ``Submission.Diffeomorph.exists_contDiff_family_eqOn_of_image_eq

open _root_.Diffeomorph in
theorem exists_contDiff_family_eqOn_of_isotopy
    (F C : ℝ → (E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E))
    (hF : ContDiff ℝ n (fun z : ℝ × E => F z.1 z.2))
    (hFi : ContDiff ℝ n (fun z : ℝ × E => (F z.1).symm z.2))
    (hC : ContDiff ℝ n (fun z : ℝ × E => C z.1 z.2))
    (hCi : ContDiff ℝ n (fun z : ℝ × E => (C z.1).symm z.2))
    {a b : ℝ} (hab : a < b) {K S : Set E}
    (hCK : ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, C t '' K = K)
    (hCS : ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, _root_.Set.EqOn (C t) (C 0) S) :
    ∃ G : ℝ → (E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E),
      ContDiff ℝ n (fun z : ℝ × E => G z.1 z.2) ∧
      ContDiff ℝ n (fun z : ℝ × E => (G z.1).symm z.2) ∧
      (∀ t ≤ a, G t = F t) ∧
      (∀ t, b ≤ t → G t = (C 1).trans ((C 0).symm.trans (F t))) ∧
      (∀ t, _root_.Set.EqOn (G t) (F t) S) ∧
      (∀ t, G t '' K = F t '' K) := by
  let θ : ℝ → ℝ := fun t => Real.smoothTransition ((t - a) / (b - a))
  have hθ : ContDiff ℝ n θ :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const (b - a))
  have hθmem (t : ℝ) : θ t ∈ _root_.Set.Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hθzero (t : ℝ) (ht : t ≤ a) : θ t = 0 :=
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_pos.mpr hab).le)
  have hθone (t : ℝ) (ht : b ≤ t) : θ t = 1 :=
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith))
  let G : ℝ → (E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E) := fun t => (C (θ t)).trans ((C 0).symm.trans (F t))
  have hG : ContDiff ℝ n (fun z : ℝ × E => G z.1 z.2) :=
    hF.comp (contDiff_fst.prodMk ((C 0).symm.contDiff.comp
      (hC.comp ((hθ.comp contDiff_fst).prodMk contDiff_snd))))
  have hGi : ContDiff ℝ n (fun z : ℝ × E => (G z.1).symm z.2) :=
    hCi.comp ((hθ.comp contDiff_fst).prodMk ((C 0).contDiff.comp hFi))
  have hCzeroK : (C 0).symm '' K = K := by
    rw [← hCK 0 ⟨le_rfl, zero_le_one⟩, (C 0).symm_image_image, hCK 0 ⟨le_rfl, zero_le_one⟩]
  refine ⟨G, hG, hGi, ?_, ?_, ?_, ?_⟩
  · intro t ht
    ext x
    change F t ((C 0).symm (C (θ t) x)) = F t x
    rw [hθzero t ht, (C 0).symm_apply_apply]
  · intro t ht
    dsimp only [G]
    rw [hθone t ht]
  · intro t x hx
    change F t ((C 0).symm (C (θ t) x)) = F t x
    rw [hCS (θ t) (hθmem t) hx, (C 0).symm_apply_apply]
  · intro t
    calc
      G t '' K = F t '' ((C 0).symm '' (C (θ t) '' K)) := by
        rw [_root_.Set.image_image, _root_.Set.image_image]
        rfl
      _ = F t '' K := by rw [hCK (θ t) (hθmem t), hCzeroK]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.exists_contDiff_family_eqOn_of_isotopy then
    throwError "Refusing to shadow existing declaration Diffeomorph.exists_contDiff_family_eqOn_of_isotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.exists_contDiff_family_eqOn_of_isotopy ``Submission.Diffeomorph.exists_contDiff_family_eqOn_of_isotopy

open _root_.Diffeomorph in
private theorem contDiff_ite_fst_le_of_eqOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ∞ω} {L R : ℝ × E → F}
    (hL : ContDiff ℝ n L) (hR : ContDiff ℝ n R)
    {c ε : ℝ} (hε : 0 < ε)
    (heq : ∀ t ∈ _root_.Set.Ioo (c - ε) (c + ε), ∀ x, L (t, x) = R (t, x)) :
    ContDiff ℝ n (fun z : ℝ × E => if z.1 ≤ c then L z else R z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z.1 < c + ε
  · apply hL.contDiffAt.congr_of_eventuallyEq
    have hnear : ∀ᶠ y : ℝ × E in 𝓝 z, y.1 < c + ε :=
      (isOpen_Iio.preimage continuous_fst).mem_nhds hz
    filter_upwards [hnear] with y hy
    split_ifs with h
    · rfl
    · exact (heq y.1 ⟨by linarith, hy⟩ y.2).symm
  · apply hR.contDiffAt.congr_of_eventuallyEq
    have hzc : c - ε < z.1 := by linarith
    have hnear : ∀ᶠ y : ℝ × E in 𝓝 z, c - ε < y.1 :=
      (isOpen_Ioi.preimage continuous_fst).mem_nhds hzc
    filter_upwards [hnear] with y hy
    split_ifs with h
    · exact heq y.1 ⟨hy, by linarith⟩ y.2
    · rfl

run_cmd do
  let target := ``Submission.Diffeomorph.contDiff_ite_fst_le_of_eqOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.contDiff_ite_fst_le_of_eqOn target :: scope.openDecls } }

open _root_.Diffeomorph in
theorem exists_contDiff_family_eqOn_Iio_Ioi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ∞}
    (P F : ℝ → E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E)
    (hP : ContDiff ℝ n (fun z : ℝ × E => P z.1 z.2))
    (hPi : ContDiff ℝ n (fun z : ℝ × E => (P z.1).symm z.2))
    (hF : ContDiff ℝ n (fun z : ℝ × E => F z.1 z.2))
    (hFi : ContDiff ℝ n (fun z : ℝ × E => (F z.1).symm z.2))
    {c ε : ℝ} (hε : 0 < ε) (heq : _root_.Set.EqOn P F (_root_.Set.Ioo (c - ε) (c + ε))) :
    ∃ H : ℝ → E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E,
      ContDiff ℝ n (fun z : ℝ × E => H z.1 z.2) ∧
      ContDiff ℝ n (fun z : ℝ × E => (H z.1).symm z.2) ∧
      EqOn H P (_root_.Set.Iio (c + ε)) ∧ _root_.Set.EqOn H F (_root_.Set.Ioi (c - ε)) := by
  let H (t : ℝ) := if t ≤ c then P t else F t
  have hH : ContDiff ℝ n (fun z : ℝ × E => H z.1 z.2) := by
    have hh := contDiff_ite_fst_le_of_eqOn hP hF hε
      (fun t ht x => congrArg (fun f : E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E => f x) (heq ht))
    convert hh using 1
    funext z
    simp only [H]
    split_ifs <;> rfl
  have hHi : ContDiff ℝ n (fun z : ℝ × E => (H z.1).symm z.2) := by
    have hh := contDiff_ite_fst_le_of_eqOn hPi hFi hε
      (fun t ht x => congrArg (fun f : E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E => f.symm x) (heq ht))
    convert hh using 1
    funext z
    simp only [H]
    split_ifs <;> rfl
  refine ⟨H, hH, hHi, ?_, ?_⟩
  · intro t ht
    dsimp only [H]
    split_ifs with h
    · rfl
    · exact (heq ⟨by linarith, ht⟩).symm
  · intro t ht
    dsimp only [H]
    split_ifs with h
    · exact heq ⟨ht, by linarith⟩
    · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.exists_contDiff_family_eqOn_Iio_Ioi then
    throwError "Refusing to shadow existing declaration Diffeomorph.exists_contDiff_family_eqOn_Iio_Ioi"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.exists_contDiff_family_eqOn_Iio_Ioi ``Submission.Diffeomorph.exists_contDiff_family_eqOn_Iio_Ioi

end Diffeomorph

namespace Diffeomorph
open _root_.Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

open _root_.Diffeomorph in
theorem exists_contDiff_family_eqOn_sphere_radial_collar
    (F : ℝ → (E ≃ₘ[ℝ] E)) (L U : E ≃ₘ[ℝ] E)
    (hF : ContDiff ℝ ∞ (fun z : ℝ × E => F z.1 z.2))
    (hFi : ContDiff ℝ ∞ (fun z : ℝ × E => (F z.1).symm z.2))
    {a b c r : ℝ} (hab : a < b) (hr : 0 < r)
    (hball : F c '' (L '' _root_.Metric.closedBall 0 r) = U '' _root_.Metric.closedBall 0 r) :
    ∃ C : E ≃ₘ[ℝ] E, C '' _root_.Metric.closedBall 0 r = _root_.Metric.closedBall 0 r ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      (∀ x ∈ _root_.Metric.sphere (0 : E) r, ∀ s ∈ _root_.Set.Icc (1 - δ) (1 + δ),
        C (s • x) = s • U.symm (F c (L x)) ∧
        C.symm (s • x) = s • L.symm ((F c).symm (U x))) ∧
      ∃ G : ℝ → (E ≃ₘ[ℝ] E),
        ContDiff ℝ ∞ (fun z : ℝ × E => G z.1 z.2) ∧
        ContDiff ℝ ∞ (fun z : ℝ × E => (G z.1).symm z.2) ∧
        (∀ t ≤ a, ∀ x, G t x = F t (L x)) ∧
        (∀ t, b ≤ t → ∀ x, G t x = F t ((F c).symm (U (C x)))) ∧
        (∀ t, _root_.Set.EqOn (G t) (fun x => F t (L x)) (_root_.Metric.sphere 0 r)) ∧
        (∀ t, G t '' _root_.Metric.closedBall 0 r = F t '' (L '' _root_.Metric.closedBall 0 r)) := by
  let B := L.trans ((F c).trans U.symm)
  have hB : B '' _root_.Metric.closedBall 0 r = _root_.Metric.closedBall 0 r := by
    calc
      _ = U.symm '' (F c '' (L '' _root_.Metric.closedBall 0 r)) := by
        rw [_root_.Set.image_image, _root_.Set.image_image]
        rfl
      _ = _root_.Metric.closedBall 0 r := by rw [hball, U.symm_image_image]
  obtain ⟨C, hC, hCi, hCzero, hCKS, δ, hδ, hδhalf, hrad⟩ :=
    B.exists_contDiff_isotopy_radial_collar_of_image_closedBall_eq 0 hr hB
  have hCL (t : ℝ) (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1) :
      EqOn (C t) (C 0) (_root_.Metric.sphere 0 r) := by rw [hCzero]; exact (hCKS t ht).2
  have hFL : ContDiff ℝ ∞ (fun z : ℝ × E => F z.1 (L z.2)) :=
    hF.comp (contDiff_fst.prodMk (L.contDiff.comp contDiff_snd))
  have hFLi : ContDiff ℝ ∞ (fun z : ℝ × E => L.symm ((F z.1).symm z.2)) :=
    L.symm.contDiff.comp hFi
  obtain ⟨G, hG, hGi, hGa, hGb, hGS, hGK⟩ :=
    exists_contDiff_family_eqOn_of_isotopy (fun t => L.trans (F t)) C
      hFL hFLi hC hCi hab (fun t ht => (hCKS t ht).1) hCL
  refine ⟨C 1, (hCKS 1 ⟨zero_le_one, le_rfl⟩).1, δ, hδ, hδhalf, ?_,
    G, hG, hGi, ?_, ?_, hGS, ?_⟩
  · intro x hx s hs
    have hBi : B.symm x = L.symm ((F c).symm (U x)) := by
      apply B.injective
      change B (B.symm x) = U.symm (F c (L (L.symm ((F c).symm (U x)))))
      rw [B.apply_symm_apply, L.apply_symm_apply, (F c).apply_symm_apply, U.symm_apply_apply]
    simpa only [zero_add, sub_zero, hBi, show B x = U.symm (F c (L x)) from rfl]
      using hrad x hx s hs
  · intro t ht x
    rw [hGa t ht]
    rfl
  · intro t ht x
    rw [hGb t ht, hCzero]
    change F t (L (L.symm ((F c).symm (U (C 1 x))))) = _
    rw [L.apply_symm_apply]
  · intro t
    rw [hGK t, _root_.Set.image_image]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.exists_contDiff_family_eqOn_sphere_radial_collar then
    throwError "Refusing to shadow existing declaration Diffeomorph.exists_contDiff_family_eqOn_sphere_radial_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.exists_contDiff_family_eqOn_sphere_radial_collar ``Submission.Diffeomorph.exists_contDiff_family_eqOn_sphere_radial_collar

end Diffeomorph
