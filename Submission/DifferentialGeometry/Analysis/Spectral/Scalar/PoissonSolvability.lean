import Submission.DifferentialGeometry.Analysis.Spectral.Scalar.Enumeration

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.lp
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry target :: scope.openDecls } }

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianEigenvalueOf_pos_of_ne_zero
    {g : SmoothRiemannianMetric I M}
    (μ : NonzeroResolventEigenvalue (I := I) (M := M) g)
    (h : laplacianEigenvalueOf μ.val ≠ 0) :
    0 < laplacianEigenvalueOf μ.val :=
  lt_of_le_of_ne (laplacianEigenvalueOf_nonneg (I := I) (M := M) μ) (Ne.symm h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianEigenvalueOf_pos_of_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianEigenvalueOf_pos_of_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianEigenvalueOf_pos_of_ne_zero ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianEigenvalueOf_pos_of_ne_zero

omit [NeZero (Module.finrank ℝ E)] in
theorem mem_nonzeroLaplacianEigenvalueSet_of_laplacianEigenvalueOf_ne_zero
    {g : SmoothRiemannianMetric I M}
    (μ : NonzeroResolventEigenvalue (I := I) (M := M) g)
    (h : laplacianEigenvalueOf μ.val ≠ 0) :
    laplacianEigenvalueOf μ.val ∈ nonzeroLaplacianEigenvalueSet (I := I) (M := M) g := by
  refine ⟨μ, ?_, rfl⟩
  have hle : μ.val ≤ 1 := nonzeroResolventEigenvalue_le_one (I := I) (M := M) μ
  have hne : μ.val ≠ 1 := by
    intro h1
    exact h (by rw [h1]; unfold laplacianEigenvalueOf; norm_num)
  exact lt_of_le_of_ne hle hne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.mem_nonzeroLaplacianEigenvalueSet_of_laplacianEigenvalueOf_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.mem_nonzeroLaplacianEigenvalueSet_of_laplacianEigenvalueOf_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.mem_nonzeroLaplacianEigenvalueSet_of_laplacianEigenvalueOf_ne_zero ``Submission.DifferentialGeometry.Analysis.Laplacian.mem_nonzeroLaplacianEigenvalueSet_of_laplacianEigenvalueOf_ne_zero

theorem summable_norm_sq_coeff_div_laplacianEigenvalueOf
    (g : SmoothRiemannianMetric I M) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hgap : ∀ lam ∈ nonzeroLaplacianEigenvalueSet (I := I) (M := M) g, c₀ ≤ lam)
    (w : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    Summable (fun i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
        Fin (Module.finrank ℝ (resolventEigenspace (I := I) (M := M) g μ.val)) =>
      ‖if laplacianEigenvalueOf i.1.val = 0 then 0
        else -(⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, w⟫_ℝ) /
          laplacianEigenvalueOf i.1.val‖ ^ 2) := by
  classical
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g with hb
  have hsum_w : Summable (fun i => (⟪b i, w⟫_ℝ) ^ 2) := by
    have h := b.summable_inner_mul_inner w w
    simpa only [real_inner_comm, sq] using h
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    (hsum_w.mul_left ((c₀⁻¹) ^ 2))
  by_cases h0 : laplacianEigenvalueOf i.1.val = 0
  · have hzero : (if laplacianEigenvalueOf i.1.val = 0 then 0
        else -(⟪b i, w⟫_ℝ) / laplacianEigenvalueOf i.1.val) = 0 := if_pos h0
    rw [hzero, norm_zero]
    simpa using mul_nonneg (sq_nonneg (c₀⁻¹)) (sq_nonneg (⟪b i, w⟫_ℝ))
  · have hne : (if laplacianEigenvalueOf i.1.val = 0 then 0
        else -(⟪b i, w⟫_ℝ) / laplacianEigenvalueOf i.1.val) =
        -(⟪b i, w⟫_ℝ) / laplacianEigenvalueOf i.1.val := if_neg h0
    rw [hne]
    have hpos := laplacianEigenvalueOf_pos_of_ne_zero (I := I) (M := M) i.1 h0
    have hgap_i := hgap _ (mem_nonzeroLaplacianEigenvalueSet_of_laplacianEigenvalueOf_ne_zero
      (I := I) (M := M) i.1 h0)
    have hnorm : ‖-(⟪b i, w⟫_ℝ) / laplacianEigenvalueOf i.1.val‖ ^ 2 =
        (⟪b i, w⟫_ℝ) ^ 2 / (laplacianEigenvalueOf i.1.val) ^ 2 := by
      rw [norm_div, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, div_pow, sq_abs]
      simp only [sq_abs]
    rw [hnorm]
    have hsq : c₀ ^ 2 ≤ (laplacianEigenvalueOf i.1.val) ^ 2 := by nlinarith
    calc (⟪b i, w⟫_ℝ) ^ 2 / (laplacianEigenvalueOf i.1.val) ^ 2
        ≤ (⟪b i, w⟫_ℝ) ^ 2 / c₀ ^ 2 :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hsq
      _ = (c₀⁻¹) ^ 2 * (⟪b i, w⟫_ℝ) ^ 2 := by rw [inv_pow, div_eq_inv_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.summable_norm_sq_coeff_div_laplacianEigenvalueOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.summable_norm_sq_coeff_div_laplacianEigenvalueOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.summable_norm_sq_coeff_div_laplacianEigenvalueOf ``Submission.DifferentialGeometry.Analysis.Laplacian.summable_norm_sq_coeff_div_laplacianEigenvalueOf

theorem exists_laplacianDomain_laplacianOp_eq_of_inner_eigenbasis_eq_zero
    (g : SmoothRiemannianMetric I M) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hgap : ∀ lam ∈ nonzeroLaplacianEigenvalueSet (I := I) (M := M) g, c₀ ≤ lam)
    (w : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (hw : ∀ i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
        Fin (Module.finrank ℝ (resolventEigenspace (I := I) (M := M) g μ.val)),
        laplacianEigenvalueOf i.1.val = 0 →
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, w⟫_ℝ = 0) :
    ∃ u_h : laplacianDomain (I := I) (M := M) g,
      laplacianOp (I := I) (M := M) g u_h = w := by
  classical
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g with hb
  set c : (Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ (resolventEigenspace (I := I) (M := M) g μ.val))) → ℝ :=
    fun i => if laplacianEigenvalueOf i.1.val = 0 then 0
      else -(⟪b i, w⟫_ℝ) / laplacianEigenvalueOf i.1.val with hc
  have hsum_c : Summable (fun i => ‖c i‖ ^ 2) := by
    simpa only [hc] using
      summable_norm_sq_coeff_div_laplacianEigenvalueOf (I := I) (M := M) g hc₀ hgap w
  have hc_mem : Memℓp c 2 := memℓp_gen (p := 2) (by simpa using hsum_c)
  set u : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    b.repr.symm (⟨c, hc_mem⟩ : ℓ²(_, ℝ)) with hu
  have hu_coeff : ∀ i, ⟪b i, u⟫_ℝ = c i := by
    intro i
    rw [← HilbertBasis.repr_apply_apply b u i, hu, LinearIsometryEquiv.apply_symm_apply]
  have hrel : ∀ i, ⟪b i, w⟫_ℝ =
      -(laplacianEigenvalueOf i.1.val) * ⟪b i, u⟫_ℝ := by
    intro i
    rw [hu_coeff i]
    by_cases h0 : laplacianEigenvalueOf i.1.val = 0
    · have hci : c i = 0 := by simp only [hc]; rw [if_pos h0]
      rw [hci, hw i h0, h0]
      ring
    · have hci : c i = -(⟪b i, w⟫_ℝ) / laplacianEigenvalueOf i.1.val := by
        simp only [hc]; rw [if_neg h0]
      rw [hci]
      field_simp
  obtain ⟨u_h, -, hlap⟩ :=
    (exists_laplacianDomain_lift_iff_inner_eigenbasis (I := I) (M := M) (g := g)
      (u := u) (w := w)).mpr hrel
  exact ⟨u_h, hlap⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.exists_laplacianDomain_laplacianOp_eq_of_inner_eigenbasis_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.exists_laplacianDomain_laplacianOp_eq_of_inner_eigenbasis_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.exists_laplacianDomain_laplacianOp_eq_of_inner_eigenbasis_eq_zero ``Submission.DifferentialGeometry.Analysis.Laplacian.exists_laplacianDomain_laplacianOp_eq_of_inner_eigenbasis_eq_zero

end Laplacian
end Analysis
end DifferentialGeometry

end
