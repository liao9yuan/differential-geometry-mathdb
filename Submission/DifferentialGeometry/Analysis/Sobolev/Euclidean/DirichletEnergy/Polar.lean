import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.DifferentialGeometry.Analysis.Integration.PolarAnnulus
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

private theorem norm_sq_rotation (v w : F) (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ‖a • v + b • w‖ ^ 2 + ‖(-b) • v + a • w‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
  simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, real_inner_smul_right, neg_sq]
  linear_combination (‖v‖ ^ 2 + ‖w‖ ^ 2) * h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.norm_sq_rotation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.norm_sq_rotation target :: scope.openDecls } }

private theorem hasFDerivAt_complex_polar (p : ℝ × ℝ) :
    HasFDerivAt Complex.polarCoord.symm
      (Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp (fderivPolarCoordSymm p)) p := by
  change HasFDerivAt (Complex.equivRealProdCLM.symm ∘ polarCoord.symm) _ p
  exact Complex.equivRealProdCLM.symm.hasFDerivAt.comp p (hasFDerivAt_polarCoord_symm p)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.hasFDerivAt_complex_polar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.hasFDerivAt_complex_polar target :: scope.openDecls } }

private theorem complex_polar_derivative_radial (p : ℝ × ℝ) :
    (fderiv ℝ Complex.polarCoord.symm p) (1, 0) =
      Real.cos p.2 • (1 : ℂ) + Real.sin p.2 • Complex.I := by
  rw [(hasFDerivAt_complex_polar p).fderiv]
  simp [fderivPolarCoordSymm, Matrix.toLin_finTwoProd_toContinuousLinearMap,
    Complex.equivRealProdCLM_symm_apply, Complex.real_smul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.complex_polar_derivative_radial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.complex_polar_derivative_radial target :: scope.openDecls } }

private theorem complex_polar_derivative_angular (p : ℝ × ℝ) :
    (fderiv ℝ Complex.polarCoord.symm p) (0, 1) =
      p.1 • ((-Real.sin p.2) • (1 : ℂ) + Real.cos p.2 • Complex.I) := by
  rw [(hasFDerivAt_complex_polar p).fderiv]
  simp [fderivPolarCoordSymm, Matrix.toLin_finTwoProd_toContinuousLinearMap,
    Complex.equivRealProdCLM_symm_apply, Complex.real_smul]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.complex_polar_derivative_angular
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.complex_polar_derivative_angular target :: scope.openDecls } }

theorem polar_fderiv_energy_eq (g : ℂ → F) {p : ℝ × ℝ} (hp : p.1 ≠ 0)
    (hg : DifferentiableAt ℝ g (Complex.polarCoord.symm p)) :
    p.1 * (‖fderiv ℝ g (Complex.polarCoord.symm p) 1‖ ^ 2 +
      ‖fderiv ℝ g (Complex.polarCoord.symm p) Complex.I‖ ^ 2) / 2 =
      (p.1 * ‖fderiv ℝ (g ∘ Complex.polarCoord.symm) p (1, 0)‖ ^ 2 +
        ‖fderiv ℝ (g ∘ Complex.polarCoord.symm) p (0, 1)‖ ^ 2 / p.1) / 2 := by
  let A := fderiv ℝ g (Complex.polarCoord.symm p)
  have hchain := fderiv_comp p hg (hasFDerivAt_complex_polar p).differentiableAt
  have hr : fderiv ℝ (g ∘ Complex.polarCoord.symm) p (1, 0) =
      Real.cos p.2 • A 1 + Real.sin p.2 • A Complex.I := by
    rw [hchain, ContinuousLinearMap.comp_apply, complex_polar_derivative_radial]
    change A _ = _
    simp only [map_add, map_smul]
  have ht : fderiv ℝ (g ∘ Complex.polarCoord.symm) p (0, 1) =
      p.1 • ((-Real.sin p.2) • A 1 + Real.cos p.2 • A Complex.I) := by
    rw [hchain, ContinuousLinearMap.comp_apply, complex_polar_derivative_angular]
    simp only [map_smul, map_add]
    rfl
  rw [hr, ht, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hrot := norm_sq_rotation (A 1) (A Complex.I)
    (Real.cos p.2) (Real.sin p.2) (Real.cos_sq_add_sin_sq p.2)
  change p.1 * (‖A 1‖ ^ 2 + ‖A Complex.I‖ ^ 2) / 2 = _
  rw [← hrot]
  field_simp [hp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.polar_fderiv_energy_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.polar_fderiv_energy_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.polar_fderiv_energy_eq ``Submission.DifferentialGeometry.Analysis.polar_fderiv_energy_eq

theorem polar_fderiv_energy_le (g : ℂ → F) {p : ℝ × ℝ} (hp : 0 < p.1) :
    p.1 * (‖fderiv ℝ g (Complex.polarCoord.symm p) 1‖ ^ 2 +
      ‖fderiv ℝ g (Complex.polarCoord.symm p) Complex.I‖ ^ 2) / 2 ≤
      (p.1 * ‖fderiv ℝ (g ∘ Complex.polarCoord.symm) p (1, 0)‖ ^ 2 +
        ‖fderiv ℝ (g ∘ Complex.polarCoord.symm) p (0, 1)‖ ^ 2 / p.1) / 2 := by
  by_cases hg : DifferentiableAt ℝ g (Complex.polarCoord.symm p)
  · exact (polar_fderiv_energy_eq g hp.ne' hg).le
  · rw [fderiv_zero_of_not_differentiableAt hg]
    simp only [zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0),
      add_zero, _root_.MulZeroClass.mul_zero, zero_div]
    positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.polar_fderiv_energy_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.polar_fderiv_energy_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.polar_fderiv_energy_le ``Submission.DifferentialGeometry.Analysis.polar_fderiv_energy_le

end DifferentialGeometry.Analysis

end

noncomputable section

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

private theorem hasFDerivAt_affine_angle (c d : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => (q.1, c * q.2 + d))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (c • ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
  simpa only [Pi.smul_apply, smul_eq_mul] using!
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk
      (((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).const_smul c).add_const d)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.hasFDerivAt_affine_angle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.hasFDerivAt_affine_angle target :: scope.openDecls } }

theorem affine_polar_fderiv_energy_le (g : ℂ → F) (c d : ℝ) (hc : c ≠ 0)
    {p : ℝ × ℝ} (hp : 0 < p.1) :
    p.1 * (‖fderiv ℝ g (Complex.polarCoord.symm (p.1, c * p.2 + d)) 1‖ ^ 2 +
      ‖fderiv ℝ g (Complex.polarCoord.symm (p.1, c * p.2 + d)) Complex.I‖ ^ 2) / 2 ≤
      (p.1 * ‖fderiv ℝ (fun q : ℝ × ℝ =>
          g (Complex.polarCoord.symm (q.1, c * q.2 + d))) p (1, 0)‖ ^ 2 +
        ‖fderiv ℝ (fun q : ℝ × ℝ =>
          g (Complex.polarCoord.symm (q.1, c * q.2 + d))) p (0, 1)‖ ^ 2 /
            (c ^ 2 * p.1)) / 2 := by
  let A : ℝ × ℝ → ℝ × ℝ := fun q => (q.1, c * q.2 + d)
  let H : ℝ × ℝ → F := g ∘ Complex.polarCoord.symm
  have hp' : 0 < (A p).1 := hp
  by_cases hH : DifferentiableAt ℝ H (A p)
  · have hA := hasFDerivAt_affine_angle c d p
    have hchain := fderiv_comp p hH hA.differentiableAt
    have hr : fderiv ℝ (H ∘ A) p (1, 0) = fderiv ℝ H (A p) (1, 0) := by
      rw [hchain, hA.fderiv]
      simp
    have ht : fderiv ℝ (H ∘ A) p (0, 1) = c • fderiv ℝ H (A p) (0, 1) := by
      rw [hchain, hA.fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_apply,
        smul_eq_mul, mul_one]
      rw [show (0, c) = c • ((0, 1) : ℝ × ℝ) by ext <;> simp, map_smul]
    have h := polar_fderiv_energy_le g hp'
    change _ ≤ (p.1 * ‖fderiv ℝ (H ∘ A) p (1, 0)‖ ^ 2 +
      ‖fderiv ℝ (H ∘ A) p (0, 1)‖ ^ 2 / (c ^ 2 * p.1)) / 2
    rw [hr, ht, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hcancel : c ^ 2 * ‖fderiv ℝ H (A p) (0, 1)‖ ^ 2 / (c ^ 2 * p.1) =
        ‖fderiv ℝ H (A p) (0, 1)‖ ^ 2 / p.1 := by
      field_simp [hc, hp.ne']
    rw [hcancel]
    exact h
  · have h := polar_fderiv_energy_le g hp'
    change _ ≤ ((A p).1 * ‖fderiv ℝ H (A p) (1, 0)‖ ^ 2 +
      ‖fderiv ℝ H (A p) (0, 1)‖ ^ 2 / (A p).1) / 2 at h
    rw [fderiv_zero_of_not_differentiableAt hH] at h
    simp only [zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0),
      add_zero, _root_.MulZeroClass.mul_zero, zero_div] at h
    exact h.trans (by positivity)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.affine_polar_fderiv_energy_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.affine_polar_fderiv_energy_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.affine_polar_fderiv_energy_le ``Submission.DifferentialGeometry.Analysis.affine_polar_fderiv_energy_le

theorem normalized_polar_fderiv_energy_le (g : ℂ → F) {p : ℝ × ℝ} (hp : 0 < p.1) :
    p.1 * (‖fderiv ℝ g
        (Complex.polarCoord.symm (p.1, 2 * Real.pi * p.2 - Real.pi)) 1‖ ^ 2 +
      ‖fderiv ℝ g
        (Complex.polarCoord.symm (p.1, 2 * Real.pi * p.2 - Real.pi)) Complex.I‖ ^ 2) / 2 ≤
      (p.1 * ‖fderiv ℝ (fun q : ℝ × ℝ =>
          g (Complex.polarCoord.symm (q.1, 2 * Real.pi * q.2 - Real.pi))) p (1, 0)‖ ^ 2 +
        ‖fderiv ℝ (fun q : ℝ × ℝ =>
          g (Complex.polarCoord.symm (q.1, 2 * Real.pi * q.2 - Real.pi))) p (0, 1)‖ ^ 2 /
            ((2 * Real.pi) ^ 2 * p.1)) / 2 := by
  simpa only [sub_eq_add_neg] using
    affine_polar_fderiv_energy_le g (2 * Real.pi) (-Real.pi) (by positivity) hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.normalized_polar_fderiv_energy_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.normalized_polar_fderiv_energy_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.normalized_polar_fderiv_energy_le ``Submission.DifferentialGeometry.Analysis.normalized_polar_fderiv_energy_le

end DifferentialGeometry.Analysis

end

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Filter
open scoped _root_.Topology _root_.NNReal _root_.ContDiff

namespace DifferentialGeometry.Analysis

section Normed

variable {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private def columnEnergy (g : X → F) (v w x : X) : ℝ :=
  (‖fderiv ℝ g x v‖ ^ 2 + ‖fderiv ℝ g x w‖ ^ 2) / 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.columnEnergy
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.columnEnergy target :: scope.openDecls } }

private theorem columnEnergy_nonneg (g : X → F) (v w x : X) :
    0 ≤ columnEnergy g v w x := by
  unfold columnEnergy
  positivity

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.columnEnergy_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.columnEnergy_nonneg target :: scope.openDecls } }

private theorem columnEnergy_le_of_fderiv_bound (g : X → F) {v w x : X}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) {B : ℝ} (hB : 0 ≤ B)
    (hD : ‖fderiv ℝ g x‖ ≤ B) : columnEnergy g v w x ≤ B ^ 2 := by
  have hb (e : X) (he : ‖e‖ = 1) : ‖fderiv ℝ g x e‖ ≤ B := by
    have h := (fderiv ℝ g x).le_opNorm e
    rw [he, mul_one] at h
    exact h.trans hD
  have hvs := (sq_le_sq₀ (norm_nonneg _) hB).mpr (hb v hv)
  have hws := (sq_le_sq₀ (norm_nonneg _) hB).mpr (hb w hw)
  unfold columnEnergy
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.columnEnergy_le_of_fderiv_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.columnEnergy_le_of_fderiv_bound target :: scope.openDecls } }

private theorem measurable_columnEnergy [MeasurableSpace X] [OpensMeasurableSpace X]
    [CompleteSpace F] (g : X → F) (v w : X) : Measurable (columnEnergy g v w) := by
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  exact (((measurable_fderiv_apply_const ℝ g v).norm.pow_const 2).add
    ((measurable_fderiv_apply_const ℝ g w).norm.pow_const 2)).div_const 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.measurable_columnEnergy
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.measurable_columnEnergy target :: scope.openDecls } }

private theorem integrableOn_columnEnergy_of_fderiv_bound
    [MeasurableSpace X] [OpensMeasurableSpace X] [CompleteSpace F]
    (g : X → F) {v w : X} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    {s : Set X} (hs : MeasurableSet s) {μ : _root_.MeasureTheory.Measure X} [_root_.MeasureTheory.IsFiniteMeasure (μ.restrict s)]
    {B : ℝ} (hB : 0 ≤ B) (hD : ∀ x ∈ s, ‖fderiv ℝ g x‖ ≤ B) :
    IntegrableOn (columnEnergy g v w) s μ := by
  apply Integrable.mono' (_root_.MeasureTheory.integrable_const (B ^ 2))
    (measurable_columnEnergy g v w).aestronglyMeasurable
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem hs] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (columnEnergy_nonneg g v w x)]
  exact columnEnergy_le_of_fderiv_bound g hv hw hB (hD x hx)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.integrableOn_columnEnergy_of_fderiv_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.integrableOn_columnEnergy_of_fderiv_bound target :: scope.openDecls } }

private theorem contDiff_normalized_polar :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      Complex.polarCoord.symm (p.1, 2 * Real.pi * p.2 - Real.pi)) := by
  simp only [Complex.polarCoord_symm_apply]
  have hcast : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  fun_prop

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.contDiff_normalized_polar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.contDiff_normalized_polar target :: scope.openDecls } }

variable [CompleteSpace F]

theorem integrableOn_normalized_polar_fderiv_energy {g : ℂ → F} {L : ℝ≥0}
    (hg : LipschitzWith L g) (a R : ℝ) :
    _root_.MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (‖fderiv ℝ (fun q : ℝ × ℝ =>
          g (Complex.polarCoord.symm (q.1, 2 * Real.pi * q.2 - Real.pi))) p (1, 0)‖ ^ 2 +
        ‖fderiv ℝ (fun q : ℝ × ℝ =>
          g (Complex.polarCoord.symm (q.1, 2 * Real.pi * q.2 - Real.pi))) p (0, 1)‖ ^ 2) / 2)
      (_root_.Set.Icc a R ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
  let P : ℝ × ℝ → ℂ := fun p =>
    Complex.polarCoord.symm (p.1, 2 * Real.pi * p.2 - Real.pi)
  let K : Set (ℝ × ℝ) := _root_.Set.Icc (a - 1) (R + 1) ×ˢ _root_.Set.Icc (-1 : ℝ) 2
  have hKc : IsCompact K := isCompact_Icc.prod _root_.CompactIccSpace.isCompact_Icc
  have hKconv : Convex ℝ K := (convex_Icc _ _).prod (convex_Icc _ _)
  obtain ⟨J, hJ⟩ := contDiff_normalized_polar.contDiffOn.exists_lipschitzOnWith
    (by simp) hKconv hKc
  have hG : LipschitzOnWith (L * J) (g ∘ P) K := hg.comp_lipschitzOnWith hJ
  let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (_root_.Set.Icc a R ×ˢ _root_.Set.Icc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc.prod _root_.CompactIccSpace.isCompact_Icc).measure_lt_top.ne
  change _root_.MeasureTheory.IntegrableOn (columnEnergy (g ∘ P) (1, 0) (0, 1)) _
  apply integrableOn_columnEnergy_of_fderiv_bound (g ∘ P)
    (by simp) (by simp) (measurableSet_Icc.prod measurableSet_Icc) (L * J).coe_nonneg
  intro p hp
  have hnb : K ∈ 𝓝 p := by
    apply _root_.Filter.mem_of_superset ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds
      (show p ∈ _root_.Set.Ioo (a - 1) (R + 1) ×ˢ _root_.Set.Ioo (-1 : ℝ) 2 from
        ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
          ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩))
    exact _root_.Set.prod_mono _root_.Set.Ioo_subset_Icc_self _root_.Set.Ioo_subset_Icc_self
  exact norm_fderiv_le_of_lipschitzOn ℝ hnb hG

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integrableOn_normalized_polar_fderiv_energy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integrableOn_normalized_polar_fderiv_energy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integrableOn_normalized_polar_fderiv_energy ``Submission.DifferentialGeometry.Analysis.integrableOn_normalized_polar_fderiv_energy

end Normed

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem integral_annulus_fderiv_energy_le {g : ℂ → F} {L : ℝ≥0}
    (hg : LipschitzWith L g) {a R : ℝ} (ha : 0 < a) :
    (∫ z in {z : ℂ | ‖z‖ ∈ _root_.Set.Icc a R},
      (‖fderiv ℝ g z 1‖ ^ 2 + ‖fderiv ℝ g z Complex.I‖ ^ 2) / 2) ≤
      (2 * Real.pi) * _root_.Max.max R (((2 * Real.pi) ^ 2 * a)⁻¹) *
        ∫ p in _root_.Set.Icc a R ×ˢ _root_.Set.Icc (0 : ℝ) 1,
          (‖fderiv ℝ (fun q : ℝ × ℝ =>
              g (Complex.polarCoord.symm (q.1, 2 * Real.pi * q.2 - Real.pi))) p (1, 0)‖ ^ 2 +
            ‖fderiv ℝ (fun q : ℝ × ℝ =>
              g (Complex.polarCoord.symm (q.1, 2 * Real.pi * q.2 - Real.pi)))
              p (0, 1)‖ ^ 2) / 2 := by
  let P : ℝ × ℝ → ℂ := fun p =>
    Complex.polarCoord.symm (p.1, 2 * Real.pi * p.2 - Real.pi)
  let e : ℂ → ℝ := columnEnergy g 1 Complex.I
  let E : ℝ × ℝ → ℝ := columnEnergy (g ∘ P) (1, 0) (0, 1)
  let S : Set (ℝ × ℝ) := _root_.Set.Icc a R ×ˢ _root_.Set.Icc (0 : ℝ) 1
  let C : ℝ := _root_.Max.max R (((2 * Real.pi) ^ 2 * a)⁻¹)
  have he : Measurable e := measurable_columnEnergy g 1 Complex.I
  have he0 (z : ℂ) : 0 ≤ e z := columnEnergy_nonneg g 1 Complex.I z
  have heB (z : ℂ) : e z ≤ (L : ℝ) ^ 2 :=
    columnEnergy_le_of_fderiv_bound g _root_.NormOneClass.norm_one Complex.norm_I L.coe_nonneg
      (norm_fderiv_le_of_lipschitz ℝ hg)
  have heN (z : ℂ) : ‖e z‖ ≤ (L : ℝ) ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (he0 z)]
    exact heB z
  have hEi : _root_.MeasureTheory.IntegrableOn E S := integrableOn_normalized_polar_fderiv_energy hg a R
  have hwi : _root_.MeasureTheory.IntegrableOn (fun p => p.1 * e (P p)) S :=
    integrableOn_mul_comp_normalized_polar_of_bounded he ha (fun z _ => heN z)
  have hcoeff (p : ℝ × ℝ) (hp : p ∈ S) : p.1 * e (P p) ≤ C * E p := by
    have hp0 : 0 < p.1 := ha.trans_le hp.1.1
    have h := normalized_polar_fderiv_energy_le g hp0
    have hr : p.1 ≤ C := hp.1.2.trans (le_max_left _ _)
    have hd : ((2 * Real.pi) ^ 2 * p.1)⁻¹ ≤ C := by
      apply le_trans _ (le_max_right _ _)
      exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hp.1.1 (sq_nonneg _))
    have hcols := add_le_add
      (mul_le_mul_of_nonneg_right hr (sq_nonneg (‖fderiv ℝ (g ∘ P) p (1, 0)‖)))
      (mul_le_mul_of_nonneg_right hd (sq_nonneg (‖fderiv ℝ (g ∘ P) p (0, 1)‖)))
    change p.1 * (‖fderiv ℝ g (P p) 1‖ ^ 2 +
      ‖fderiv ℝ g (P p) Complex.I‖ ^ 2) / 2 ≤
      (p.1 * ‖fderiv ℝ (g ∘ P) p (1, 0)‖ ^ 2 +
        ‖fderiv ℝ (g ∘ P) p (0, 1)‖ ^ 2 / ((2 * Real.pi) ^ 2 * p.1)) / 2 at h
    change p.1 * ((‖fderiv ℝ g (P p) 1‖ ^ 2 +
      ‖fderiv ℝ g (P p) Complex.I‖ ^ 2) / 2) ≤
      C * ((‖fderiv ℝ (g ∘ P) p (1, 0)‖ ^ 2 +
        ‖fderiv ℝ (g ∘ P) p (0, 1)‖ ^ 2) / 2)
    simp only [div_eq_mul_inv] at h
    nlinarith [hcols]
  have hi : (∫ p in S, p.1 * e (P p)) ≤ C * ∫ p in S, E p := by
    have h := _root_.MeasureTheory.setIntegral_mono_on hwi (hEi.const_mul C)
      (measurableSet_Icc.prod measurableSet_Icc) hcoeff
    simpa only [_root_.MeasureTheory.integral_const_mul] using h
  have heq := integral_annulus_eq_integral_normalized_polar_of_bounded
    he ha (R := R) (fun z _ => heN z)
  change (∫ z in {z : ℂ | ‖z‖ ∈ _root_.Set.Icc a R}, e z) ≤
    (2 * Real.pi) * C * ∫ p in S, E p
  rw [heq]
  calc
    (2 * Real.pi) * ∫ p in S, p.1 * e (P p) ≤
        (2 * Real.pi) * (C * ∫ p in S, E p) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_annulus_fderiv_energy_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_annulus_fderiv_energy_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_annulus_fderiv_energy_le ``Submission.DifferentialGeometry.Analysis.integral_annulus_fderiv_energy_le

end InnerProduct

end DifferentialGeometry.Analysis

end
