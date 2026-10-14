import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient
import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient.SmoothRegularity
import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient.Support
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Metric _root_.Filter _root_.Topology _root_.Set _root_.Function
open scoped _root_.ENNReal _root_.NNReal _root_.Convolution _root_.Pointwise _root_.BigOperators

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem locallyIntegrable_translate
    (k : Fin d) (h : ℝ) {u : E → ℝ}
    (hu : _root_.MeasureTheory.LocallyIntegrable u (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)) :
    LocallyIntegrable (translate k h u) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
  let τ : E ≃ₜ E := Homeomorph.addRight (h • EuclideanSpace.single k 1)
  have hτ_emb : MeasurableEmbedding τ := τ.measurableEmbedding
  have hτ_preserving : _root_.MeasureTheory.MeasurePreserving τ _root_.MeasureTheory.MeasureSpace.volume volume := by
    rw [show (τ : E → E) = fun x => x + h • EuclideanSpace.single k 1 from rfl]
    exact _root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume _
  intro x
  obtain ⟨V, hV_mem, hu_int⟩ := hu (τ x)
  refine ⟨τ ⁻¹' V, τ.continuous.continuousAt.preimage_mem_nhds hV_mem, ?_⟩
  have h_eq : translate k h u = u ∘ (τ : E → E) := rfl
  rw [h_eq]
  exact (hτ_preserving.integrableOn_comp_preimage hτ_emb (f := u) (s := V)).mpr hu_int

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.locallyIntegrable_translate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.locallyIntegrable_translate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.locallyIntegrable_translate ``Submission.DifferentialGeometry.Analysis.Sobolev.locallyIntegrable_translate

omit [NeZero d] in
theorem locallyIntegrable_diffQuot
    (k : Fin d) (h : ℝ) {u : E → ℝ}
    (hu : _root_.MeasureTheory.LocallyIntegrable u (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)) :
    LocallyIntegrable (diffQuot k h u) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
  by_cases hh : h = 0
  · subst hh
    rw [diffQuot_zero_h]
    exact _root_.MeasureTheory.locallyIntegrable_const _
  · have h_eq : diffQuot k h u =
        fun x => h⁻¹ * translate k h u x + (-h⁻¹) * u x := by
      funext x
      rw [diffQuot_apply_of_ne (d := d) k hh u x]
      change (u (x + h • EuclideanSpace.single k 1) - u x) / h =
        h⁻¹ * u (x + h • EuclideanSpace.single k 1) + (-h⁻¹) * u x
      field_simp
      ring
    rw [h_eq]
    have h_translate := locallyIntegrable_translate (d := d) k h hu
    have h_first : _root_.MeasureTheory.LocallyIntegrable
        (fun x : E => h⁻¹ * translate k h u x) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
      have h_smul :
          (fun x : E => h⁻¹ * translate k h u x) =
            h⁻¹ • translate k h u := by
        funext x
        rw [Pi.smul_apply, smul_eq_mul]
      rw [h_smul]
      exact h_translate.smul h⁻¹
    have h_second : _root_.MeasureTheory.LocallyIntegrable
        (fun x : E => (-h⁻¹) * u x) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
      have h_smul :
          (fun x : E => (-h⁻¹) * u x) = (-h⁻¹) • u := by
        funext x
        rw [Pi.smul_apply, smul_eq_mul]
      rw [h_smul]
      exact hu.smul (-h⁻¹)
    exact h_first.add h_second

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.locallyIntegrable_diffQuot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.locallyIntegrable_diffQuot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.locallyIntegrable_diffQuot ``Submission.DifferentialGeometry.Analysis.Sobolev.locallyIntegrable_diffQuot

omit [NeZero d] in
private lemma tsupport_subset_univ (φ : E → ℝ) :
    tsupport φ ⊆ (Set.univ : Set E) := fun _ _ => trivial

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.tsupport_subset_univ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.tsupport_subset_univ target :: scope.openDecls } }

omit [NeZero d] in
private theorem hasWeakPartialDeriv_translate_neg
    (k j : Fin d) (h : ℝ) {f g : E → ℝ}
    (hwp : DeGiorgi.HasWeakPartialDeriv (d := d) j g f Set.univ) :
    DeGiorgi.HasWeakPartialDeriv (d := d) j
      (translate k (-h) g) (translate k (-h) f) Set.univ := by
  intro φ hφ_smooth hφ_support _hφ_sub
  set ψ : E → ℝ := translate k h φ with hψ_def
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    contDiff_translate (d := d) k h hφ_smooth
  have hψ_cs : HasCompactSupport ψ :=
    hasCompactSupport_translate_of_hasCompactSupport (d := d) hφ_support k h
  have h_test :=
    hwp ψ hψ_smooth hψ_cs (tsupport_subset_univ ψ)
  rw [_root_.MeasureTheory.setIntegral_univ, _root_.MeasureTheory.setIntegral_univ] at h_test
  rw [_root_.MeasureTheory.setIntegral_univ, _root_.MeasureTheory.setIntegral_univ]
  have h_LHS_subst :
      ∫ x, f x * (fderiv ℝ ψ x) (EuclideanSpace.single j 1)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) =
        ∫ z, translate k (-h) f z *
          (fderiv ℝ φ z) (EuclideanSpace.single j 1)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
    have h_int_eq :=
      integral_add_right_eq_self (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E))
        (f := fun x : E =>
          f x * (fderiv ℝ ψ x) (EuclideanSpace.single j 1))
        ((-h) • EuclideanSpace.single k 1)
    rw [← h_int_eq]
    refine _root_.MeasureTheory.integral_congr_ae ?_
    filter_upwards with z
    have h_lhs_unfold : translate k (-h) f z =
        f (z + (-h) • EuclideanSpace.single k 1) := rfl
    rw [h_lhs_unfold]
    have hψ_eq_translate : ψ = translate k h φ := rfl
    rw [hψ_eq_translate]
    have h_apply :
        (fderiv ℝ (translate k h φ) (z + (-h) • EuclideanSpace.single k 1))
            (EuclideanSpace.single j 1) =
          (fderiv ℝ φ
            ((z + (-h) • EuclideanSpace.single k 1) +
              h • EuclideanSpace.single k 1))
            (EuclideanSpace.single j 1) :=
      fderiv_translate_apply (d := d) k j h hφ_smooth
        (z + (-h) • EuclideanSpace.single k 1)
    rw [h_apply]
    have h_cancel :
        (z + (-h) • EuclideanSpace.single k 1) +
            h • EuclideanSpace.single k 1 = z := by
      rw [add_assoc, ← add_smul]
      simp
    rw [h_cancel]
  have h_RHS_subst :
      ∫ x, g x * ψ x ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) =
        ∫ z, translate k (-h) g z * φ z ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
    have h_int_eq :=
      integral_add_right_eq_self (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E))
        (f := fun x : E => g x * ψ x)
        ((-h) • EuclideanSpace.single k 1)
    rw [← h_int_eq]
    refine _root_.MeasureTheory.integral_congr_ae ?_
    filter_upwards with z
    have h_g_unfold : translate k (-h) g z =
        g (z + (-h) • EuclideanSpace.single k 1) := rfl
    rw [h_g_unfold]
    have h_psi_eq : ψ (z + (-h) • EuclideanSpace.single k 1) = φ z := by
      change φ ((z + (-h) • EuclideanSpace.single k 1) +
            h • EuclideanSpace.single k 1) = φ z
      have : (z + (-h) • EuclideanSpace.single k 1) +
            h • EuclideanSpace.single k 1 = z := by
        rw [add_assoc, ← add_smul]
        simp
      rw [this]
    rw [h_psi_eq]
  rw [h_LHS_subst] at h_test
  rw [h_RHS_subst] at h_test
  exact h_test

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.hasWeakPartialDeriv_translate_neg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.hasWeakPartialDeriv_translate_neg target :: scope.openDecls } }

omit [NeZero d] in
theorem hasWeakPartialDeriv_translate
    (k j : Fin d) (h : ℝ) {f g : E → ℝ}
    (hwp : DeGiorgi.HasWeakPartialDeriv (d := d) j g f Set.univ) :
    DeGiorgi.HasWeakPartialDeriv (d := d) j
      (translate k h g) (translate k h f) Set.univ := by
  simpa using hasWeakPartialDeriv_translate_neg (d := d) k j (-h) hwp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.hasWeakPartialDeriv_translate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.hasWeakPartialDeriv_translate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.hasWeakPartialDeriv_translate ``Submission.DifferentialGeometry.Analysis.Sobolev.hasWeakPartialDeriv_translate

omit [NeZero d] in
private lemma locallyIntegrable_translate_restrict_univ
    (k : Fin d) (h : ℝ) {u : E → ℝ}
    (hu : _root_.MeasureTheory.LocallyIntegrable u ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Set.univ)) :
    _root_.MeasureTheory.LocallyIntegrable (translate k h u)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Set.univ) := by
  rw [Measure.restrict_univ] at hu ⊢
  exact locallyIntegrable_translate (d := d) k h hu

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.locallyIntegrable_translate_restrict_univ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.locallyIntegrable_translate_restrict_univ target :: scope.openDecls } }


omit [NeZero d] in
theorem hasWeakPartialDeriv_diffQuot
    (k j : Fin d) (h : ℝ) {u g_j : E → ℝ}
    (hu_localInt :
      _root_.MeasureTheory.LocallyIntegrable u ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Set.univ))
    (hg_j_localInt :
      _root_.MeasureTheory.LocallyIntegrable g_j ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Set.univ))
    (hwp : DeGiorgi.HasWeakPartialDeriv (d := d) j g_j u Set.univ) :
    DeGiorgi.HasWeakPartialDeriv (d := d) j
      (diffQuot k h g_j) (diffQuot k h u) Set.univ := by
  by_cases hh : h = 0
  · subst hh
    simp only [diffQuot_zero_h]
    intro φ _ _ _
    rw [_root_.MeasureTheory.setIntegral_univ, _root_.MeasureTheory.setIntegral_univ]
    simp
  · have h_diffQuot_u_eq : diffQuot k h u =
        fun x => h⁻¹ * (translate k h u x) + (-h⁻¹) * u x := by
      funext x
      rw [diffQuot_apply_of_ne (d := d) k hh u x]
      have htrans_x : translate k h u x =
          u (x + h • EuclideanSpace.single k 1) := rfl
      rw [htrans_x]
      field_simp
      ring
    have h_diffQuot_g_eq : diffQuot k h g_j =
        fun x => h⁻¹ * (translate k h g_j x) + (-h⁻¹) * g_j x := by
      funext x
      rw [diffQuot_apply_of_ne (d := d) k hh g_j x]
      have htrans_x : translate k h g_j x =
          g_j (x + h • EuclideanSpace.single k 1) := rfl
      rw [htrans_x]
      field_simp
      ring
    rw [h_diffQuot_u_eq, h_diffQuot_g_eq]
    have h_translate :
        DeGiorgi.HasWeakPartialDeriv (d := d) j
          (translate k h g_j) (translate k h u) Set.univ := by
      exact hasWeakPartialDeriv_translate (d := d) k j h hwp
    have h_translate_u_localInt :
        _root_.MeasureTheory.LocallyIntegrable (translate k h u)
          ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Set.univ) :=
      locallyIntegrable_translate_restrict_univ (d := d) k h hu_localInt
    have h_translate_g_localInt :
        _root_.MeasureTheory.LocallyIntegrable (translate k h g_j)
          ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Set.univ) :=
      locallyIntegrable_translate_restrict_univ (d := d) k h hg_j_localInt
    have h_smul_translate :
        DeGiorgi.HasWeakPartialDeriv (d := d) j
          (fun x => h⁻¹ * translate k h g_j x)
          (fun x => h⁻¹ * translate k h u x) Set.univ :=
      h_translate.const_smul h⁻¹
    have h_smul_orig :
        DeGiorgi.HasWeakPartialDeriv (d := d) j
          (fun x => (-h⁻¹) * g_j x)
          (fun x => (-h⁻¹) * u x) Set.univ :=
      hwp.const_smul (-h⁻¹)
    have h_smul_translate_u_localInt :
        _root_.MeasureTheory.LocallyIntegrable (fun x : E => h⁻¹ * translate k h u x)
          ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Set.univ) := by
      have h_eq : (fun x : E => h⁻¹ * translate k h u x) =
          h⁻¹ • translate k h u := by
        funext x; rw [Pi.smul_apply, smul_eq_mul]
      rw [h_eq]
      exact h_translate_u_localInt.smul h⁻¹
    have h_smul_translate_g_localInt :
        _root_.MeasureTheory.LocallyIntegrable (fun x : E => h⁻¹ * translate k h g_j x)
          ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Set.univ) := by
      have h_eq : (fun x : E => h⁻¹ * translate k h g_j x) =
          h⁻¹ • translate k h g_j := by
        funext x; rw [Pi.smul_apply, smul_eq_mul]
      rw [h_eq]
      exact h_translate_g_localInt.smul h⁻¹
    have h_smul_orig_u_localInt :
        _root_.MeasureTheory.LocallyIntegrable (fun x : E => (-h⁻¹) * u x)
          ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Set.univ) := by
      have h_eq : (fun x : E => (-h⁻¹) * u x) =
          (-h⁻¹) • u := by
        funext x; rw [Pi.smul_apply, smul_eq_mul]
      rw [h_eq]
      exact hu_localInt.smul (-h⁻¹)
    have h_smul_orig_g_localInt :
        _root_.MeasureTheory.LocallyIntegrable (fun x : E => (-h⁻¹) * g_j x)
          ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Set.univ) := by
      have h_eq : (fun x : E => (-h⁻¹) * g_j x) =
          (-h⁻¹) • g_j := by
        funext x; rw [Pi.smul_apply, smul_eq_mul]
      rw [h_eq]
      exact hg_j_localInt.smul (-h⁻¹)
    have h_add := h_smul_translate.add h_smul_orig
      h_smul_translate_u_localInt h_smul_orig_u_localInt
      h_smul_translate_g_localInt h_smul_orig_g_localInt
    exact h_add

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.hasWeakPartialDeriv_diffQuot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.hasWeakPartialDeriv_diffQuot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.hasWeakPartialDeriv_diffQuot ``Submission.DifferentialGeometry.Analysis.Sobolev.hasWeakPartialDeriv_diffQuot


end DifferentialGeometry.Analysis.Sobolev
