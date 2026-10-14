import Submission.DifferentialGeometry.Analysis.Integration.Lp.ContinuousOn
import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletChartSourceDual
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Submission.DifferentialGeometry.Analysis.Parabolic.WeakEquationTensor

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

private theorem integrable_tensor_mul_lp
    {Z E : Type*} [MeasurableSpace Z] [MeasurableSpace E]
    {μ : _root_.MeasureTheory.Measure Z} {ν : _root_.MeasureTheory.Measure E} [_root_.MeasureTheory.IsFiniteMeasure μ] [_root_.MeasureTheory.IsFiniteMeasure ν]
    {τ : Z → ℝ} {ψ : E → ℝ} {c F : Z × E → ℝ}
    (hτ : _root_.MeasureTheory.MemLp τ ∞ μ) (hψ : _root_.MeasureTheory.MemLp ψ ∞ ν)
    (hc : _root_.MeasureTheory.MemLp c ∞ (μ.prod ν)) (hF : _root_.MeasureTheory.MemLp F 2 (μ.prod ν)) :
    Integrable (fun p => τ p.1 * (c p * F p) * ψ p.2) (μ.prod ν) := by
  have hτp := hτ.comp_fst ν
  have hψp := hψ.comp_snd μ
  have hm : _root_.MeasureTheory.MemLp (fun p => τ p.1 * (c p * F p) * ψ p.2) 2 (μ.prod ν) := by
    exact hψp.mul (r := 2) ((hF.mul (r := 2) hc).mul (r := 2) hτp)
  exact hm.integrable (by norm_num)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.integrable_tensor_mul_lp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.integrable_tensor_mul_lp target :: scope.openDecls } }

private theorem integrable_fixed_density_tensor_terms
    {d : ℕ} {μ : _root_.MeasureTheory.Measure ℝ} {ν : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))}
    [_root_.MeasureTheory.IsFiniteMeasure μ] [_root_.MeasureTheory.IsFiniteMeasure ν]
    {τ : ℝ → ℝ} {η ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    {r C : ℝ × EuclideanSpace ℝ (Fin d) → ℝ}
    {P : Fin d → ℝ × EuclideanSpace ℝ (Fin d) → ℝ}
    (hτ : _root_.MeasureTheory.MemLp τ ∞ μ) (hψ : _root_.MeasureTheory.MemLp ψ ∞ ν)
    (hdψ : ∀ j, _root_.MeasureTheory.MemLp (fun z => fderiv ℝ ψ z (EuclideanSpace.single j 1)) ∞ ν)
    (hη : _root_.MeasureTheory.MemLp η ∞ ν)
    (hηr : _root_.MeasureTheory.MemLp (fun p => η p.2 / r p) ∞ (μ.prod ν))
    (hdηr : ∀ j, _root_.MeasureTheory.MemLp (fun p => fderiv ℝ (fun z => η z.2 / r z) p
      (0, EuclideanSpace.single j 1)) ∞ (μ.prod ν))
    (hC : _root_.MeasureTheory.MemLp C 2 (μ.prod ν)) (hP : ∀ j, _root_.MeasureTheory.MemLp (P j) 2 (μ.prod ν)) :
    (∀ j, _root_.MeasureTheory.Integrable (fun p => τ p.1 * ((η p.2 / r p) * P j p) *
      fderiv ℝ ψ p.2 (EuclideanSpace.single j 1)) (μ.prod ν)) ∧
    (∀ j, _root_.MeasureTheory.Integrable (fun p => τ p.1 * (P j p *
      fderiv ℝ (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)) * ψ p.2) (μ.prod ν)) ∧
    Integrable (fun p => τ p.1 * (η p.2 * C p) * ψ p.2) (μ.prod ν) := by
  refine ⟨fun j => integrable_tensor_mul_lp hτ (hdψ j) hηr (hP j), ?_,
    integrable_tensor_mul_lp hτ hψ (hη.comp_snd μ) hC⟩
  intro j
  simpa only [mul_comm (P j _) (fderiv ℝ (fun z => η z.2 / r z) _
    (0, EuclideanSpace.single j 1))] using
    integrable_tensor_mul_lp hτ hψ (hdηr j) (hP j)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.integrable_fixed_density_tensor_terms
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.integrable_fixed_density_tensor_terms target :: scope.openDecls } }

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.ContDiff _root_.Manifold _root_.NNReal

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

omit [T2Space M] [CompactSpace M] in
private theorem smoothScalarDirichlet_chartInverse_bounds
    {q : SmoothRiemannianMetric I_hs M}
    (α : M) {Ω : Set EuStd} (hΩ : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (v : SmoothScalarDirichlet q) :
    let ψ := fun z => v.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    ContDiffOn ℝ (⊤ : ℕ∞) ψ Ω ∧ _root_.MeasureTheory.MemLp ψ ∞ (volume.restrict Ω) ∧
      ∀ j : Fin (Module.finrank ℝ EuN),
        MemLp (fun z => fderiv ℝ ψ z (EuclideanSpace.single j 1)) ∞ (volume.restrict Ω) := by
  intro ψ
  let U := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hU : IsOpen U := (toEuclidean (E := EuN)).toHomeomorph.isOpenMap _ isOpen_interior
  have hP : ContDiffOn ℝ (⊤ : ℕ∞) ψ U := by
    apply (scalarOnE_contDiffOn α v.smooth).comp
      (toEuclidean (E := EuN)).symm.contDiff.contDiffOn
    rintro z ⟨y, hy, rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using interior_subset hy
  refine ⟨hP.mono (subset_closure.trans hΩs),
    (hP.continuousOn.mono hΩs).memLp_top_of_subset_isCompact hΩc hΩ subset_closure, ?_⟩
  intro j
  have hc := (((hP.fderiv_of_isOpen hU (m := (⊤ : ℕ∞)) (by simp)).clm_apply
    (g := fun _ => EuclideanSpace.single j 1) contDiffOn_const).continuousOn).mono hΩs
  exact hc.memLp_top_of_subset_isCompact hΩc hΩ subset_closure

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothScalarDirichlet_chartInverse_bounds
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.smoothScalarDirichlet_chartInverse_bounds target :: scope.openDecls } }

theorem exists_lp_dual_of_fixed_density_cutoff_equation
    {q : SmoothRiemannianMetric I_hs M} (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : _root_.MeasureTheory.Measure ℝ} {a b : ℝ} [_root_.MeasureTheory.IsFiniteMeasure (μ.restrict (_root_.Set.Icc a b))]
    {O : Set (ℝ × EuStd)} (hO : IsOpen O) (hKO : _root_.Set.Icc a b ×ˢ closure Ω ⊆ O)
    {r W C : ℝ × EuStd → ℝ} {P : Fin (Module.finrank ℝ EuN) → ℝ × EuStd → ℝ}
    (hr : ContDiffOn ℝ (⊤ : ℕ∞) r O) (hrne : ∀ p ∈ O, r p ≠ 0)
    (hC : _root_.MeasureTheory.MemLp C 2 ((μ.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)))
    (hP : ∀ j, _root_.MeasureTheory.MemLp (P j) 2 ((μ.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)))
    (hweak : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ _root_.Set.Ioo a b ×ˢ Ω →
      (∫ p, W p * fderiv ℝ φ p (1, 0) ∂(μ.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) =
        (∑ j, ∫ p, P j p * fderiv ℝ (fun z => φ z / r z) p (0, EuclideanSpace.single j 1)
          ∂(μ.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) -
        ∫ p, C p * φ p ∂(μ.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω))
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω) :
    let ν := (μ.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)
    let Q := fun j p => (η p.2 / r p) * P j p
    let B := fun p => η p.2 * C p - ∑ j, P j p *
      fderiv ℝ (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)
    (∀ j, _root_.MeasureTheory.MemLp (Q j) 2 ν) ∧ _root_.MeasureTheory.MemLp B 2 ν ∧
    (∃ ℓ : _root_.MeasureTheory.Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 (μ.restrict (_root_.Set.Icc a b)),
      ∀ τ : _root_.MeasureTheory.Lp ℝ 2 (μ.restrict (_root_.Set.Icc a b)), ∀ v : H1ComplDirichlet q,
        (∫ t, τ t * ℓ t v ∂μ.restrict (_root_.Set.Icc a b)) =
          (∫ p, τ p.1 * B p * H1ComplDirichletToLp q v
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂ν) -
          ∑ j, ∫ p, τ p.1 * Q j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j v p.2 ∂ν) ∧
    ∀ (v : SmoothScalarDirichlet q) (τ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) τ →
      HasCompactSupport τ → tsupport τ ⊆ _root_.Set.Ioo a b →
      let ψ := fun z => v.toFun ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
      (∫ p, deriv τ p.1 * (η p.2 * W p) * ψ p.2 ∂ν) =
        (∑ j, ∫ p, τ p.1 * Q j p * fderiv ℝ ψ p.2 (EuclideanSpace.single j 1) ∂ν) -
        ∫ p, τ p.1 * B p * ψ p.2 ∂ν := by
  intro ν Q B
  classical
  let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict Ω) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, _root_.Set.univ_inter]
    exact (_root_.MeasureTheory.measure_mono subset_closure).trans_lt hΩc.measure_lt_top
  have hlift {f : ℝ × EuStd → ℝ} (hf : ContinuousOn f O) : _root_.MeasureTheory.MemLp f ∞ ν := by
    have hb := (hf.mono hKO).memLp_top_of_subset_isCompact
      (isCompact_Icc.prod hΩc) (measurableSet_Icc.prod hΩ.measurableSet)
      (_root_.Set.prod_mono Subset.rfl subset_closure) (μ := (μ.restrict (_root_.Set.Icc a b)).prod _root_.MeasureTheory.MeasureSpace.volume)
    rw [← Measure.prod_restrict, Measure.restrict_restrict_of_subset (Subset.rfl : _root_.Set.Icc a b ⊆ _root_.Set.Icc a b)] at hb
    exact hb
  have hηall : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × EuStd => η p.2) O :=
    (hη.comp contDiff_snd).contDiffOn
  have hηr : _root_.MeasureTheory.MemLp (fun p : ℝ × EuStd => η p.2 / r p) ∞ ν :=
    hlift (hηall.div hr hrne).continuousOn
  have hdηr (j) : _root_.MeasureTheory.MemLp (fun p => fderiv ℝ (fun z : ℝ × EuStd => η z.2 / r z) p
      (0, EuclideanSpace.single j 1)) ∞ ν :=
    hlift (((hηall.div hr hrne).fderiv_of_isOpen (m := (⊤ : ℕ∞)) hO (by simp)).clm_apply
      contDiffOn_const).continuousOn
  have hQ (j) : _root_.MeasureTheory.MemLp (Q j) 2 ν := (hP j).mul (r := 2) hηr
  have hB : _root_.MeasureTheory.MemLp B 2 ν := by
    apply (hC.mul (r := 2) (hlift hηall.continuousOn)).sub
    apply _root_.MeasureTheory.memLp_finsetSum
    intro j _
    exact (hdηr j).mul (r := 2) (hP j)
  refine ⟨hQ, hB, exists_lp_chart_source_sub_divergence_dual α hΩ hΩc hΩs hB hQ, ?_⟩
  intro v τ hτ hτc hτs ψ
  obtain ⟨hψ, hψmem, hdψmem⟩ :=
    smoothScalarDirichlet_chartInverse_bounds α hΩ.measurableSet hΩc hΩs v
  have hτmem : _root_.MeasureTheory.MemLp τ ∞ (μ.restrict (_root_.Set.Icc a b)) :=
    hτ.continuous.memLp_top_of_hasCompactSupport hτc _
  have hηsp : _root_.MeasureTheory.MemLp η ∞ (volume.restrict Ω) :=
    hη.continuous.memLp_top_of_hasCompactSupport hηc _
  obtain ⟨hmain, herr, hsource⟩ := integrable_fixed_density_tensor_terms
    hτmem hψmem hdψmem hηsp hηr hdηr hC hP
  have hmem : ∀ᵐ p ∂ν, p ∈ _root_.Set.Icc a b ×ˢ Ω := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.prod hΩ.measurableSet)).mpr
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem hΩ.measurableSet] with z hz
    exact ⟨ht, hz⟩
  have hgood : ∀ᵐ p ∂ν, DifferentiableAt ℝ ψ p.2 ∧ DifferentiableAt ℝ r p ∧ r p ≠ 0 := by
    filter_upwards [hmem] with p hp
    have hpO := hKO ⟨hp.1, subset_closure hp.2⟩
    exact ⟨(hψ.contDiffAt (hΩ.mem_nhds hp.2)).differentiableAt (by simp),
      (hr.contDiffAt (hO.mem_nhds hpO)).differentiableAt (by simp), hrne p hpO⟩
  exact integral_fixed_density_tensor_test (fun j => EuclideanSpace.single j 1)
    hΩ hη hηc hηs hψ hgood hweak hτ hτc hτs hmain herr hsource

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_lp_dual_of_fixed_density_cutoff_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_lp_dual_of_fixed_density_cutoff_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_lp_dual_of_fixed_density_cutoff_equation ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_lp_dual_of_fixed_density_cutoff_equation

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
