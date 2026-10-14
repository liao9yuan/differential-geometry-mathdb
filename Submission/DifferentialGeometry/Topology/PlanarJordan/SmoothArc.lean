import Submission.DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import Submission.DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionBoundary
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion
import Submission.DifferentialGeometry.Topology.PlanarJordan.CutPair
import Submission.DifferentialGeometry.External.Schoenflies.FaceCyclesLand

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

noncomputable section

namespace Schoenflies

theorem isArcBetween_range_of_isEmbedding {α : unitInterval → Plane}
    (hα : Topology.IsEmbedding α) : IsArcBetween (_root_.Set.range α) (α 0) (α 1) := by
  let f : ℝ → Plane := fun t => α (_root_.Set.projIcc 0 1 (by norm_num) t)
  refine ⟨f, (hα.continuous.comp continuous_projIcc).continuousOn, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have h := hα.injective hxy
    simpa only [_root_.Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) hx,
      _root_.Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) hy, Subtype.mk.injEq] using h
  · apply Subset.antisymm
    · rintro z ⟨t, ht, rfl⟩
      exact _root_.Set.mem_range_self _
    · rintro z ⟨t, rfl⟩
      exact ⟨t, t.property, by
        dsimp [f]; rw [_root_.Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) t.property]⟩
  · simp [f]
  · simp [f]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.isArcBetween_range_of_isEmbedding then
    throwError "Refusing to shadow existing declaration Schoenflies.isArcBetween_range_of_isEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.isArcBetween_range_of_isEmbedding ``Submission.Schoenflies.isArcBetween_range_of_isEmbedding

end Schoenflies

namespace DifferentialGeometry.Topology.PlanarJordan

private theorem isSmoothEmbedding_interval_addCircle
    {γ : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hγ : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ)
    {a b : ℝ} (hab : a ≠ b) (hlen : |b - a| < 1) :
    Manifold.IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Schoenflies.Plane) ∞
      (fun t : unitInterval => γ ((a + (b - a) * (t : ℝ) : ℝ) : AddCircle (1 : ℝ))) := by
  have hlin : Manifold.IsImmersion 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t : ℝ => a + (b - a) * t) := by
    apply DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv (by simp)
      (contDiff_const.add (contDiff_const.mul contDiff_id)).contMDiff
    intro t
    rw [mfderiv_eq_fderiv]
    change Function.Injective (fderiv ℝ (fun t : ℝ => a + (b - a) * t) t)
    have hd : HasDerivAt (fun t : ℝ => a + (b - a) * t) (b - a) t := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul (b - a)).const_add a
    rw [hd.hasFDerivAt.fderiv]
    intro x y hxy
    change x * (b - a) = y * (b - a) at hxy
    exact mul_right_cancel₀ (sub_ne_zero.mpr hab.symm) (by simpa using hxy)
  have hq := DifferentialGeometry.Topology.Manifold.isImmersion_of_isLocalDiffeomorph
    AddCircle.isLocalDiffeomorph_coe
  have hi := hlin.comp hq (by simp)
  have hfull := hi.comp hγ.isImmersion (by simp)
  have himm := (isSmoothEmbedding_subtypeVal_Icc (x := (0 : ℝ)) (y := 1)
    (n := ∞)).isImmersion.comp_of_boundarylessManifold_middle hfull (by simp)
  refine ⟨himm, ?_⟩
  apply Topology.IsClosedEmbedding.isEmbedding
  apply himm.contMDiff.continuous.isClosedEmbedding
  intro x y hxy
  apply Subtype.ext
  have hmem (t : unitInterval) : a + (b - a) * (t : ℝ) ∈ _root_.Set.Ico (_root_.Min.min a b) (_root_.Min.min a b + 1) := by
    rcases le_total a b with h | h
    · rw [min_eq_left h]
      have hd := (abs_lt.mp hlen).2
      constructor <;> nlinarith [t.property.1, t.property.2]
    · rw [min_eq_right h]
      have hd := (abs_lt.mp hlen).1
      constructor <;> nlinarith [t.property.1, t.property.2]
  have h := (AddCircle.coe_eq_coe_iff_of_mem_Ico (hmem x) (hmem y)).mp
    (hγ.isEmbedding.injective hxy)
  have hmul : (b - a) * (x : ℝ) = (b - a) * (y : ℝ) := by linarith
  exact mul_left_cancel₀ (sub_ne_zero.mpr hab.symm) hmul

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PlanarJordan.isSmoothEmbedding_interval_addCircle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PlanarJordan.isSmoothEmbedding_interval_addCircle target :: scope.openDecls } }

private theorem exists_complementary_arc_affine_parameter
    {γ : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hγ : Topology.IsEmbedding γ) {A : Set Schoenflies.Plane} {p q : Schoenflies.Plane}
    (hA : Schoenflies.IsArcBetween A p q) (hsub : A ⊆ _root_.Set.range γ) :
    ∃ a b : ℝ, a ≠ b ∧ |b - a| < 1 ∧
      γ (a : AddCircle (1 : ℝ)) = p ∧ γ (b : AddCircle (1 : ℝ)) = q ∧
      Schoenflies.IsCutPair (_root_.Set.range γ) p q A
        ((fun t : ℝ => γ ((a + (b - a) * t : ℝ) : AddCircle (1 : ℝ))) '' _root_.Set.Icc 0 1) := by
  obtain ⟨z, hz⟩ := hsub hA.left_mem
  obtain ⟨w, hw⟩ := hsub hA.right_mem
  obtain ⟨a, _, ha⟩ := AddCircle.eq_coe_Ico z
  obtain ⟨θ, hθ, hθeq⟩ := AddCircle.eq_coe_Ico (w - z)
  have hθpos : 0 < θ := by
    apply hθ.1.lt_of_ne'
    intro hzero
    have hwz : w = z := sub_eq_zero.mp (by simpa [hzero] using hθeq.symm)
    exact hA.ne (hz.symm.trans (hwz ▸ hw))
  have hp : γ (a : AddCircle (1 : ℝ)) = p := ha ▸ hz
  have hq : γ ((a + θ : ℝ) : AddCircle (1 : ℝ)) = q := by
    rw [AddCircle.coe_add, ha, hθeq, add_sub_cancel]
    exact hw
  let f : ℝ → Schoenflies.Plane := fun t => γ ((a + t : ℝ) : AddCircle (1 : ℝ))
  have hf : Schoenflies.IsLoop f := by
    refine ⟨?_, ?_, ?_⟩
    · exact (hγ.continuous.comp (AddCircle.contMDiff_coe.continuous.comp
        (continuous_const.add continuous_id))).continuousOn
    · simp [f, AddCircle.coe_period]
    · intro x hx y hy hxy
      have he := hγ.injective hxy
      have hx' : a + x ∈ _root_.Set.Ico a (a + 1) := by constructor <;> linarith only [hx.1, hx.2]
      have hy' : a + y ∈ _root_.Set.Ico a (a + 1) := by constructor <;> linarith only [hy.1, hy.2]
      have := (AddCircle.coe_eq_coe_iff_of_mem_Ico hx' hy').mp he
      linarith only [this]
  have hrange : f '' _root_.Set.Icc (0 : ℝ) 1 = _root_.Set.range γ := by
    apply Subset.antisymm
    · rintro _ ⟨t, _, rfl⟩
      exact _root_.Set.mem_range_self _
    · rintro _ ⟨y, rfl⟩
      obtain ⟨t, ht, heq⟩ := AddCircle.eq_coe_Ico (y - (a : AddCircle (1 : ℝ)))
      refine ⟨t, ⟨ht.1, ht.2.le⟩, ?_⟩
      dsimp [f]
      rw [heq, add_sub_cancel]
  have hfront : f '' _root_.Set.Icc 0 0 ∪ f '' _root_.Set.Icc θ 1 = f '' _root_.Set.Icc θ 1 := by
    rw [_root_.Set.Icc_self, _root_.Set.image_singleton, hf.closes]
    exact union_eq_right.mpr (singleton_subset_iff.mpr ⟨1, ⟨hθ.2.le, le_rfl⟩, rfl⟩)
  have h0 : f 0 = p := by simpa only [f, add_zero] using hp
  have hθq : f θ = q := hq
  have hcut : Schoenflies.IsCutPair (_root_.Set.range γ) p q (f '' _root_.Set.Icc 0 θ) (f '' _root_.Set.Icc θ 1) := by
    rw [← hrange, ← h0, ← hθq]
    refine ⟨hf.middle_IsArcBetween Schoenflies.zero_mem_I ⟨hθpos.le, hθ.2.le⟩ hθ.2.ne hθpos,
      ?_, ?_, ?_⟩
    · simpa only [hf.closes] using
        (hf.back_IsArcBetween ⟨hθpos.le, hθ.2.le⟩ hθ.2.ne hθpos).reverse
    · simpa only [hfront] using
        (Schoenflies.IsLoop.pieces_cover (f := f) Schoenflies.zero_mem_I ⟨hθpos.le, hθ.2.le⟩)
    · simpa only [hfront] using (hf.pieces_meet_at_ends Schoenflies.zero_mem_I
        ⟨hθpos.le, hθ.2.le⟩ (by norm_num) hθ.2.ne hθpos)
  have himage (x y : ℝ) :
      (fun t : ℝ => γ ((a + x + (a + y - (a + x)) * t : ℝ) : AddCircle (1 : ℝ))) '' _root_.Set.Icc 0 1 =
        f '' _root_.Set.uIcc x y := by
    rw [← Schoenflies.subarc_image (f := f) (a := x) (b := y)]
    congr 1
    funext t
    apply congrArg (fun v : ℝ => γ (v : AddCircle (1 : ℝ)))
    dsimp only [Schoenflies.subarc, Schoenflies.reparam, f]
    ring
  rcases hA.eq_fst_or_eq_snd_of_subset hsub hcut with heq | heq
  · refine ⟨a + 1, a + θ, by linarith only [hθ.2], ?_, ?_, hq, ?_⟩
    · rw [show a + θ - (a + 1) = θ - 1 by ring, abs_of_neg (by linarith only [hθ.2])]
      linarith only [hθpos]
    · simpa only [AddCircle.coe_add, AddCircle.coe_period, add_zero] using hp
    · rw [himage 1 θ, _root_.Set.uIcc_of_ge hθ.2.le, heq]
      exact hcut
  · refine ⟨a, a + θ, by linarith only [hθpos], ?_, hp, hq, ?_⟩
    · rw [add_sub_cancel_left, abs_of_pos hθpos]
      exact hθ.2
    · have hi := himage 0 θ
      simp only [add_zero, _root_.Set.uIcc_of_le hθpos.le] at hi
      rw [hi, heq]
      exact hcut.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_complementary_arc_affine_parameter
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PlanarJordan.exists_complementary_arc_affine_parameter target :: scope.openDecls } }

private theorem exists_smooth_complementary_arc_parameter
    {γ : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hγ : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ)
    {A : Set Schoenflies.Plane} {p q : Schoenflies.Plane}
    (hA : Schoenflies.IsArcBetween A p q) (hsub : A ⊆ _root_.Set.range γ) :
    ∃ f : ℝ → Schoenflies.Plane, ContDiff ℝ ∞ f ∧
      (∀ t, deriv f t ≠ 0) ∧ (∀ t, f t ∈ _root_.Set.range γ) ∧ _root_.Set.InjOn f (_root_.Set.Icc 0 1) ∧ f 0 = p ∧ f 1 = q ∧
      Schoenflies.IsCutPair (_root_.Set.range γ) p q A (f '' _root_.Set.Icc 0 1) := by
  obtain ⟨a, b, hab, hlen, hp, hq, hcut⟩ :=
    exists_complementary_arc_affine_parameter hγ.isEmbedding hA hsub
  let l : ℝ → ℝ := fun t => a + (b - a) * t
  let f : ℝ → Schoenflies.Plane := fun t => γ (l t : AddCircle (1 : ℝ))
  have hlin : Manifold.IsImmersion 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ l := by
    apply DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv (by simp)
      (contDiff_const.add (contDiff_const.mul contDiff_id)).contMDiff
    intro t
    rw [mfderiv_eq_fderiv]
    change Function.Injective (fderiv ℝ l t)
    have hd : HasDerivAt l (b - a) t := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul (b - a)).const_add a
    rw [hd.hasFDerivAt.fderiv]
    intro x y hxy
    change x * (b - a) = y * (b - a) at hxy
    exact mul_right_cancel₀ (sub_ne_zero.mpr hab.symm) (by simpa using hxy)
  have hcoe := DifferentialGeometry.Topology.Manifold.isImmersion_of_isLocalDiffeomorph
    AddCircle.isLocalDiffeomorph_coe
  have hf := (hlin.comp hcoe (by simp)).comp hγ.isImmersion (by simp)
  refine ⟨f, hf.contMDiff.contDiff, ?_, fun t => _root_.Set.mem_range_self _, ?_, by simpa [f, l] using hp,
    by simpa [f, l] using hq, hcut⟩
  · intro t ht
    have hi := (hf.isImmersionAt t).injective_mfderiv (by simp)
    rw [mfderiv_eq_fderiv] at hi
    change Function.Injective (fderiv ℝ f t) at hi
    exact (one_ne_zero : (1 : ℝ) ≠ 0) (hi (ht.trans (map_zero _).symm))
  · intro x hx y hy heq
    have hmem (t : ℝ) (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1) : l t ∈ _root_.Set.Ico (_root_.Min.min a b) (_root_.Min.min a b + 1) := by
      rcases le_total a b with h | h
      · rw [min_eq_left h]
        have hd := (abs_lt.mp hlen).2
        constructor <;> dsimp only [l] <;> nlinarith [ht.1, ht.2]
      · rw [min_eq_right h]
        have hd := (abs_lt.mp hlen).1
        constructor <;> dsimp only [l] <;> nlinarith [ht.1, ht.2]
    have he := (AddCircle.coe_eq_coe_iff_of_mem_Ico (hmem x hx) (hmem y hy)).mp
      (hγ.isEmbedding.injective heq)
    have hmul : (b - a) * x = (b - a) * y := by linarith only [he]
    exact mul_left_cancel₀ (sub_ne_zero.mpr hab.symm) hmul

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_smooth_complementary_arc_parameter
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PlanarJordan.exists_smooth_complementary_arc_parameter target :: scope.openDecls } }

private theorem exists_smooth_parameter_of_circle_cut_pair
    {γ : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hγ : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ)
    {A C : Set Schoenflies.Plane} {p q : Schoenflies.Plane}
    (hcut : Schoenflies.IsCutPair (_root_.Set.range γ) p q A C) :
    ∃ f : ℝ → Schoenflies.Plane, ContDiff ℝ ∞ f ∧
      (∀ t, deriv f t ≠ 0) ∧ (∀ t, f t ∈ _root_.Set.range γ) ∧ _root_.Set.InjOn f (_root_.Set.Icc 0 1) ∧
      f 0 = p ∧ f 1 = q ∧ f '' _root_.Set.Icc 0 1 = C := by
  obtain ⟨f, hf, hdf, hfrange, hinj, h0, h1, hfcut⟩ :=
    exists_smooth_complementary_arc_parameter hγ hcut.fst hcut.fst_subset
  obtain ⟨x, hx, hxpq⟩ := Set.not_subset.mp hcut.fst.not_subset_pair
  exact ⟨f, hf, hdf, hfrange, hinj, h0, h1,
    (hfcut.eq_of_mem_diff hcut hx hx hxpq).2⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_smooth_parameter_of_circle_cut_pair
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PlanarJordan.exists_smooth_parameter_of_circle_cut_pair target :: scope.openDecls } }

theorem exists_smooth_parameter_of_arc_subset_circle
    {γ : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hγ : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ)
    {C : Set Schoenflies.Plane} {p q : Schoenflies.Plane}
    (hC : Schoenflies.IsArcBetween C p q) (hsub : C ⊆ _root_.Set.range γ) :
    ∃ f : ℝ → Schoenflies.Plane, ContDiff ℝ ∞ f ∧
      (∀ t, deriv f t ≠ 0) ∧ (∀ t, f t ∈ _root_.Set.range γ) ∧ _root_.Set.InjOn f (_root_.Set.Icc 0 1) ∧
      f 0 = p ∧ f 1 = q ∧ f '' _root_.Set.Icc 0 1 = C := by
  obtain ⟨_, _, _, _, _, _, _, hcut⟩ :=
    exists_smooth_complementary_arc_parameter hγ hC hsub
  exact exists_smooth_parameter_of_circle_cut_pair hγ hcut.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_smooth_parameter_of_arc_subset_circle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_smooth_parameter_of_arc_subset_circle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_smooth_parameter_of_arc_subset_circle ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_smooth_parameter_of_arc_subset_circle


theorem exists_isSmoothEmbedding_complementary_arc
    {γ : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hγ : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ)
    {A : Set Schoenflies.Plane} {p q : Schoenflies.Plane}
    (hA : Schoenflies.IsArcBetween A p q) (hsub : A ⊆ _root_.Set.range γ) :
    ∃ β : unitInterval → Schoenflies.Plane,
      Manifold.IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Schoenflies.Plane) ∞ β ∧
      β 0 = p ∧ β 1 = q ∧ Schoenflies.IsCutPair (_root_.Set.range γ) p q A (_root_.Set.range β) := by
  obtain ⟨a, b, hab, hlen, hp, hq, hcut⟩ :=
    exists_complementary_arc_affine_parameter hγ.isEmbedding hA hsub
  let β : unitInterval → Schoenflies.Plane := fun t =>
    γ ((a + (b - a) * (t : ℝ) : ℝ) : AddCircle (1 : ℝ))
  have hβ := isSmoothEmbedding_interval_addCircle hγ hab hlen
  have hrange : _root_.Set.range β =
      (fun t : ℝ => γ ((a + (b - a) * t : ℝ) : AddCircle (1 : ℝ))) '' _root_.Set.Icc 0 1 := by
    rw [← @Subtype.range_coe ℝ (_root_.Set.Icc (0 : ℝ) 1), ← _root_.Set.range_comp]
    rfl
  refine ⟨β, hβ, ?_, ?_, ?_⟩
  · simpa [β] using hp
  · simpa [β] using hq
  · rwa [hrange]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_isSmoothEmbedding_complementary_arc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_isSmoothEmbedding_complementary_arc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_isSmoothEmbedding_complementary_arc ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_isSmoothEmbedding_complementary_arc

theorem exists_isSmoothEmbedding_complementary_arc_of_isEmbedding
    {γ : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hγ : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ)
    {α : unitInterval → Schoenflies.Plane} (hα : Topology.IsEmbedding α)
    (hsub : _root_.Set.range α ⊆ _root_.Set.range γ) :
    ∃ β : unitInterval → Schoenflies.Plane,
      Manifold.IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Schoenflies.Plane) ∞ β ∧
      β 0 = α 0 ∧ β 1 = α 1 ∧
      range α ∪ _root_.Set.range β = _root_.Set.range γ ∧ _root_.Set.range α ∩ _root_.Set.range β = {α 0, α 1} := by
  obtain ⟨β, hβ, h0, h1, hcut⟩ := exists_isSmoothEmbedding_complementary_arc hγ
    (Schoenflies.isArcBetween_range_of_isEmbedding hα) hsub
  exact ⟨β, hβ, h0, h1, hcut.union_eq, hcut.inter_eq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_isSmoothEmbedding_complementary_arc_of_isEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_isSmoothEmbedding_complementary_arc_of_isEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_isSmoothEmbedding_complementary_arc_of_isEmbedding ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_isSmoothEmbedding_complementary_arc_of_isEmbedding

end DifferentialGeometry.Topology.PlanarJordan
