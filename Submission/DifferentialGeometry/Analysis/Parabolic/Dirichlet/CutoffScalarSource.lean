import Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.CutoffForcing
import Submission.DifferentialGeometry.Analysis.Integration.Lp.Pairing
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Characterization.CanonicalConnection
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.DivergenceForm
import Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficientRegularity
import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletChartSourceIdentification

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

section Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem exists_lp_scalar_source_of_weak_gradient
    {μ : _root_.MeasureTheory.Measure ℝ} [_root_.MeasureTheory.IsLocallyFiniteMeasure μ] {Ω : Set E} (hΩ : IsOpen Ω)
    (B V : _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (H : Fin d → _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    {A : Fin d → Fin d → ℝ × E → ℝ}
    (hA : ∀ i j, _root_.MeasureTheory.MemLp (A i j) ∞ (μ.prod (volume.restrict Ω)))
    (hDA : ∀ i j, _root_.MeasureTheory.MemLp
      (fun p => fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1))
      ∞ (μ.prod (volume.restrict Ω)))
    (hAsmooth : ∀ i j, ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A i j (t, x)) Ω)
    (hweak : ∀ j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => H j (t, x)) (fun x => V (t, x)) Ω) :
    ∃ f : _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω)),
      (f =ᵐ[μ.prod (volume.restrict Ω)] fun p => B p - ∑ i, ∑ j,
        (A i j p * H j p +
          fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * V p)) ∧
      ∀ (φ : ℝ × E → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ (_root_.Set.univ : Set ℝ) ×ˢ Ω →
        (∫ p, f p * φ p ∂μ.prod (volume.restrict Ω)) =
          (∫ p, B p * φ p ∂μ.prod (volume.restrict Ω)) +
            ∑ j, ∫ p, (∑ i, A i j p * V p) *
              fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω) := by
  obtain ⟨D, hD, hDtest⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_lp_divergence_of_weakPartials
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ (fun _ => V) (fun _ => H)
      hA hDA hAsmooth (fun _ => hweak)
  refine ⟨B - D, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_sub B D, hD] with p hp hDp
    simpa only [Pi.sub_apply, hDp] using hp
  · intro φ hφ hφc hφs
    have hBint : _root_.MeasureTheory.Integrable (fun p => B p * φ p) (μ.prod (volume.restrict Ω)) :=
      (Lp.memLp B).locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport
        hφ.continuous hφc
    have hDint : _root_.MeasureTheory.Integrable (fun p => D p * φ p) (μ.prod (volume.restrict Ω)) :=
      (Lp.memLp D).locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport
        hφ.continuous hφc
    have heq : (∫ p, (B - D) p * φ p ∂μ.prod (volume.restrict Ω)) =
        (∫ p, B p * φ p ∂μ.prod (volume.restrict Ω)) -
          ∫ p, D p * φ p ∂μ.prod (volume.restrict Ω) := by
      rw [← _root_.MeasureTheory.integral_sub hBint hDint]
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [Lp.coeFn_sub B D] with p hp
      simp only [hp, Pi.sub_apply, sub_mul]
    rw [heq, hDtest φ hφ hφc hφs, sub_neg_eq_add]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [Finset.sum_mul]
    symm
    apply _root_.MeasureTheory.integral_finsetSum
    intro i _
    have hflux : _root_.MeasureTheory.MemLp (fun p => A i j p * V p) 2 (μ.prod (volume.restrict Ω)) :=
      (Lp.memLp V).mul (hA i j)
    exact (hflux.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hφc.fderiv_apply ℝ (0, EuclideanSpace.single j 1))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_lp_scalar_source_of_weak_gradient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_lp_scalar_source_of_weak_gradient target :: scope.openDecls } }

end Euclidean

open _root_.Manifold
open scoped _root_.ContDiff _root_.Manifold

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]
local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry target :: scope.openDecls } }

omit [T2Space M] [CompactSpace M] in
private theorem exists_lp_scalar_source_of_cutoff_gradient
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : _root_.MeasureTheory.Measure ℝ} [_root_.MeasureTheory.IsLocallyFiniteMeasure μ] (hμ : μ ≤ volume.restrict J)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (B V : _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (H : Fin (Module.finrank ℝ EuN) → _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (hweak : ∀ j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => H j (t, x)) (fun x => V (t, x)) Ω) :
    let A := fun i j (p : ℝ × EuStd) =>
      (MetricExtension.densityOnEuclid q α p.2 *
        MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
          fderiv ℝ η p.2 (EuclideanSpace.single i 1)
    ∃ f : _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω)),
      (f =ᵐ[μ.prod (volume.restrict Ω)] fun p => B p - ∑ i, ∑ j,
        (A i j p * H j p +
          fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * V p)) ∧
      ∀ (φ : ℝ × EuStd → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ (_root_.Set.univ : Set ℝ) ×ˢ Ω →
        (∫ p, f p * φ p ∂μ.prod (volume.restrict Ω)) =
          (∫ p, B p * φ p ∂μ.prod (volume.restrict Ω)) +
            ∑ j, ∫ p, (∑ i, A i j p * V p) *
              fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω) := by
  intro A
  let U := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hU : IsOpen U := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  have hUt : U ⊆ MetricExtension.chartTargetEuclid (I := I_hs) α :=
    _root_.Set.image_mono interior_subset
  have hA (i j) : ContDiffOn ℝ (⊤ : ℕ∞) (A i j) (D.regular ×ˢ U) := by
    have hden : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × EuStd => MetricExtension.densityOnEuclid q α p.2)
        (D.regular ×ˢ U) :=
      (MetricExtension.densityOnEuclid_contDiffOn q α).comp contDiff_snd.contDiffOn
        (fun p hp => hUt hp.2)
    have hηd : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × EuStd => fderiv ℝ η p.2 (EuclideanSpace.single i 1)) :=
      (hη.contDiff_fderiv_apply (by simp)).comp (contDiff_snd.prodMk contDiff_const)
    exact (hden.mul (MetricExtension.invGramOnEuclid_family_contDiffOn
      hG Subset.rfl α (show U ⊆ U from Subset.rfl) i j)).mul hηd.contDiffOn
  have hAmem (i j) : _root_.MeasureTheory.MemLp (A i j) ∞ (μ.prod (volume.restrict Ω)) := by
    have h := ((hA i j).continuousOn.mono (_root_.Set.prod_mono hJ hΩs)).memLp_top_of_subset_isCompact
      (hJc.prod hΩc) (hJc.measurableSet.prod hΩ.measurableSet) (_root_.Set.prod_mono Subset.rfl subset_closure)
      (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ).prod _root_.MeasureTheory.MeasureSpace.volume)
    rw [← Measure.prod_restrict] at h
    exact h.mono_measure (Measure.prod_mono hμ le_rfl)
  have hDA (i j) : _root_.MeasureTheory.MemLp
      (fun p => fderiv ℝ (fun x => A i j (p.1, x)) p.2 (EuclideanSpace.single j 1))
      ∞ (μ.prod (volume.restrict Ω)) := by
    have hc := (spatialFDeriv_contDiffOn (G := fun t x => A i j (t, x))
      D.regular_isOpen.uniqueDiffOn hU (hA i j)).clm_apply
      (contDiffOn_const (c := EuclideanSpace.single j 1))
    have h := (hc.continuousOn.mono (_root_.Set.prod_mono hJ hΩs)).memLp_top_of_subset_isCompact
      (hJc.prod hΩc) (hJc.measurableSet.prod hΩ.measurableSet) (_root_.Set.prod_mono Subset.rfl subset_closure)
      (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ).prod _root_.MeasureTheory.MeasureSpace.volume)
    rw [← Measure.prod_restrict] at h
    exact h.mono_measure (Measure.prod_mono hμ le_rfl)
  have hAsmooth (i j) : ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A i j (t, x)) Ω := by
    filter_upwards [(_root_.MeasureTheory.ae_restrict_mem hJc.measurableSet).filter_mono (_root_.MeasureTheory.ae_mono hμ)] with t ht
    exact (hA i j).comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x hx => ⟨hJ ht, hΩs (subset_closure hx)⟩)
  exact exists_lp_scalar_source_of_weak_gradient hΩ B V H
    hAmem hDA hAsmooth hweak

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_lp_scalar_source_of_cutoff_gradient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_lp_scalar_source_of_cutoff_gradient target :: scope.openDecls } }

theorem exists_lp_scalar_source_of_cutoff_pairing
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : _root_.MeasureTheory.Measure ℝ} (hμ : μ ≤ volume.restrict J)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηs : tsupport η ⊆ Ω)
    {B V : ℝ × EuStd → ℝ}
    (hB : _root_.MeasureTheory.MemLp B 2 (μ.prod (volume.restrict Ω)))
    (hV : _root_.MeasureTheory.MemLp V 2 (μ.prod (volume.restrict Ω)))
    (H : Fin (Module.finrank ℝ EuN) → _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (hweak : ∀ j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => H j (t, x)) (fun x => hV.toLp V (t, x)) Ω)
    (β : _root_.MeasureTheory.Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ)
    (hβ :
      let E := fun j p => ∑ i,
        (MetricExtension.densityOnEuclid q α p.2 *
          MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
            fderiv ℝ η p.2 (EuclideanSpace.single i 1) * V p
      ∀ (τ : _root_.MeasureTheory.Lp ℝ 2 μ) (z : H1ComplDirichlet q),
        (∫ t, τ t * β t z ∂μ) =
          (∫ p, τ p.1 * B p * H1ComplDirichletToLp q z
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
            ∂μ.prod (volume.restrict Ω)) +
          ∑ j, ∫ p, τ p.1 * E j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z p.2
            ∂μ.prod (volume.restrict Ω)) :
    ∃ f : _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω)),
      let P := fun i j (p : ℝ × EuStd) =>
        (MetricExtension.densityOnEuclid q α p.2 *
          MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
            fderiv ℝ η p.2 (EuclideanSpace.single i 1)
      (f =ᵐ[μ.prod (volume.restrict Ω)] fun p => B p - ∑ i, ∑ j,
        (P i j p * H j p +
          fderiv ℝ (fun x => P i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * V p)) ∧
      ∀ z : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ,
        (∫ t, β t (z t) ∂μ) =
          ∫ t, (∫ x in Ω, f (t, x) * H1ComplDirichletToLp q (z t)
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))) ∂μ := by
  let : _root_.MeasureTheory.IsLocallyFiniteMeasure μ := Measure.isLocallyFiniteMeasure_of_le hμ
  have hηc : HasCompactSupport η :=
    hΩc.of_isClosed_subset (isClosed_tsupport η) (hηs.trans subset_closure)
  let ν := μ.prod (volume.restrict Ω)
  let σ := fun (p : ℝ × EuStd) => MetricExtension.densityOnEuclid q α p.2
  let E := fun j p => ∑ i,
    (σ p * MetricExtension.invGramOnEuclid (G.metric p.1) α i j p.2) *
      fderiv ℝ η p.2 (EuclideanSpace.single i 1) * V p
  let W : _root_.MeasureTheory.Lp ℝ 2 ν := hV.toLp V
  have hW : W =ᵐ[ν] V := hV.coeFn_toLp
  let BW : _root_.MeasureTheory.Lp ℝ 2 ν := hB.toLp B
  have hBWeq : BW =ᵐ[ν] B := hB.coeFn_toLp
  obtain ⟨f, hf, hftest⟩ := exists_lp_scalar_source_of_cutoff_gradient q hG hJc hJ
    α hΩ hΩc hΩs (μ := μ) hμ hη BW W H hweak
  refine ⟨f, ?_⟩
  classical
  intro P
  have hfeq : f =ᵐ[ν] fun p => B p - ∑ i, ∑ j,
      (P i j p * H j p +
        fderiv ℝ (fun x => P i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * V p) := by
    filter_upwards [hf, hW, hBWeq] with p hp hWp hBp
    simpa only [hWp, hBp] using hp
  have htest (φ : ℝ × EuStd → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ (_root_.Set.univ : Set ℝ) ×ˢ Ω) :
      (∫ p, f p * φ p ∂ν) = (∫ p, B p * φ p ∂ν) +
        ∑ j, ∫ p, E j p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν := by
    rw [hftest φ hφ hφc hφs]
    apply congrArg₂ (fun a b : ℝ => a + b)
    · apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [hBWeq] with p hp
      rw [hp]
    · apply Finset.sum_congr rfl
      intro j _
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [hW] with p hp
      rw [hp]
  have hPs (t : ℝ) (i j) : tsupport (fun x => P i j (t, x)) ⊆ tsupport η :=
    tsupport_mul_subset_right.trans (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1))
  have hPzero (p : ℝ × EuStd) (hp : p.2 ∉ tsupport η) (i j) : P i j p = 0 := by
    exact image_eq_zero_of_notMem_tsupport (f := fun x => P i j (p.1, x))
      (fun hx => hp (hPs p.1 i j hx))
  have hDPzero (p : ℝ × EuStd) (hp : p.2 ∉ tsupport η) (i j) :
      fderiv ℝ (fun x => P i j (p.1, x)) p.2 (EuclideanSpace.single j 1) = 0 := by
    rw [fderiv_of_notMem_tsupport ℝ (fun hx => hp (hPs p.1 i j hx))]
    rfl
  have hS : ∀ᵐ p ∂ν, p.2 ∉ tsupport η → f p - B p = 0 := by
    filter_upwards [hfeq] with p hp hout
    simp only [hp, hPzero p hout, hDPzero p hout, _root_.MulZeroClass.zero_mul, add_zero,
      Finset.sum_const_zero, sub_zero, sub_self]
  have hE : ∀ j, ∀ᵐ p ∂ν, p.2 ∉ tsupport η → E j p = 0 := by
    intro j
    exact Filter.Eventually.of_forall fun p hp => by
      change (∑ i, P i j p * V p) = 0
      simp only [hPzero p hp, _root_.MulZeroClass.zero_mul, Finset.sum_const_zero]
  refine ⟨hfeq, ?_⟩
  exact integral_chart_source_dual_eq_of_compact_flux_pairing α hΩ hΩc hΩs
    hηc.isCompact hηs f hB hS hE htest β hβ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_lp_scalar_source_of_cutoff_pairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_lp_scalar_source_of_cutoff_pairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_lp_scalar_source_of_cutoff_pairing ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_lp_scalar_source_of_cutoff_pairing

open _root_.Submission.DifferentialGeometry.Geometry.Connection in
theorem exists_lp_scalar_source_of_cutoff_flux
    (q : SmoothRiemannianMetric I_hs M)
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : _root_.MeasureTheory.Measure ℝ} (hμ : μ ≤ volume.restrict J)
    (H : _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (K : Fin (Module.finrank ℝ EuN) → _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (v : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ)
    (ℓ : _root_.MeasureTheory.Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : tsupport η ⊆ Ω)
    (hweak : ∀ j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun z => K j (t, z)) (fun z => H (t, z)) Ω)
    (Q : Fin (Module.finrank ℝ EuN) → ℝ × EuStd → ℝ) (B : ℝ × EuStd → ℝ)
    (hQ : ∀ j, _root_.MeasureTheory.MemLp (Q j) 2 (μ.prod (volume.restrict Ω)))
    (hB : _root_.MeasureTheory.MemLp B 2 (μ.prod (volume.restrict Ω)))
    (hℓ : ∀ (τ : _root_.MeasureTheory.Lp ℝ 2 μ) (z : H1ComplDirichlet q),
      (∫ t, τ t * ℓ t z ∂μ) =
        (∫ p, τ p.1 * B p * H1ComplDirichletToLp q z
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂μ.prod (volume.restrict Ω)) -
          ∑ j, ∫ p, τ p.1 * Q j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z p.2
            ∂μ.prod (volume.restrict Ω)) :
    let c := fun i j (p : ℝ × EuStd) => MetricExtension.densityOnEuclid q α p.2 *
      MetricExtension.invGramOnEuclid (g p.1) α i j p.2
    let P := fun i j (p : ℝ × EuStd) => c i j p * fderiv ℝ η p.2 (EuclideanSpace.single i 1)
    let E := fun j p => ∑ i, P i j p * H p
    (∀ j, ∀ᵐ t ∂μ, ∀ᵐ x ∂volume.restrict Ω,
      Q j (t, x) = (∑ i, c i j (t, x) * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) x) - E j (t, x)) →
    ∃ β : _root_.MeasureTheory.Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
      ∃ f : _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω)),
        (∀ (τ : _root_.MeasureTheory.Lp ℝ 2 μ) (z : H1ComplDirichlet q),
          (∫ t, τ t * β t z ∂μ) =
            (∫ p, τ p.1 * B p * H1ComplDirichletToLp q z
              ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂μ.prod (volume.restrict Ω)) +
              ∑ j, ∫ p, τ p.1 * E j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j z p.2
                ∂μ.prod (volume.restrict Ω)) ∧
        (∀ z : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ,
          (∫ t, ℓ t (z t) ∂μ) = (∫ t, β t (z t) ∂μ) -
            ∫ t, (∑ i, ∑ j, ∫ y in Ω,
              dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) y *
                c i j (t, y) * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (z t) y) ∂μ) ∧
        (f =ᵐ[μ.prod (volume.restrict Ω)] fun p => B p - ∑ i, ∑ j,
          (P i j p * K j p +
            fderiv ℝ (fun x => P i j (p.1, x)) p.2 (EuclideanSpace.single j 1) * H p)) ∧
        ∀ z : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ,
          (∫ t, β t (z t) ∂μ) =
            ∫ t, (∫ x in Ω, f (t, x) * H1ComplDirichletToLp q (z t)
              ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))) ∂μ := by
  let : SeminormedAddCommGroup (H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ) :=
    @ContinuousLinearMap.toSeminormedAddCommGroup ℝ ℝ
      (H1ComplDirichlet q) (H1ComplDirichlet q →L[ℝ] ℝ)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (RingHom.id ℝ) inferInstance
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  let : _root_.MeasureTheory.IsLocallyFiniteMeasure μ := Measure.isLocallyFiniteMeasure_of_le hμ
  intro c P E hflux
  have hexForm := exists_local_dirichlet_bilinear_form_family q (G := G) hG
    hJc hJ α hΩ hΩc hΩs
  let form := Classical.choose hexForm
  have hform := (Classical.choose_spec hexForm).1
  change ∀ t u z, form t u z = _ at hform
  obtain ⟨Lm, hβ, hLm⟩ := exists_cutoff_forcing_dual q (G := G) hG hJc hJ
    α hΩ hΩc hΩs hμ (fun p => H p) (Lp.memLp H) hη v ℓ form hform
    Q B hQ hℓ hflux
  have hweak' (j) : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => K j (t, x))
      (fun x => (Lp.memLp H).toLp H (t, x)) Ω := by
    simpa only [Lp.toLp_coeFn] using hweak j
  obtain ⟨f, hf, hfsource⟩ := exists_lp_scalar_source_of_cutoff_pairing q (G := G) hG
    hJc hJ α hΩ hΩc hΩs hμ hη hηs hB (Lp.memLp H) K hweak' (ℓ + Lm) hβ
  refine ⟨ℓ + Lm, f, hβ, ?_, hf, hfsource⟩
  intro z
  have he := Lp.integral_add_apply ℓ Lm z
  rw [hLm] at he
  simp only [hform] at he
  change _ = _ + _ at he
  exact eq_sub_of_add_eq he.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_lp_scalar_source_of_cutoff_flux then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_lp_scalar_source_of_cutoff_flux"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_lp_scalar_source_of_cutoff_flux ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_lp_scalar_source_of_cutoff_flux

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
