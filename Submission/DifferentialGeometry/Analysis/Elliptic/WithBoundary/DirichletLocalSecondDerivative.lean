import Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEquationLocal
import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.CutoffDiffQuotLp
import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotientProductWeakLimitLocal
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.WeakPartial

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry target :: scope.openDecls } }

private theorem exists_ae_weak_partial_local_partial_of_diffQuot_bound
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω Ω₀ : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : _root_.MeasureTheory.Measure ℝ} [_root_.MeasureTheory.IsLocallyFiniteMeasure μ] (v : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ)
    {η : EuStd → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hΩ₀ : IsOpen Ω₀) (hηone : ∀ z ∈ Ω₀, η z = 1)
    {δ C : ℝ} (hδ : 0 < δ) (hroom : _root_.Metric.cthickening δ (tsupport η) ⊆ Ω)
    (hbound : ∀ k h, 0 < |h| → |h| ≤ δ →
      (∫ t, (∑ i, ∫ z, (η z * diffQuot k h
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) z) ^ 2) ∂μ) ≤ C)
    (i k : Fin (Module.finrank ℝ EuN)) :
    ∃ H : _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω₀)),
      ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) Ω₀ := by
  let A := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i
  let w := dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs μ i v
  obtain ⟨L, hL, hinverse⟩ :=
    exists_ae_hasWeakPartialDeriv_of_integral_sq_diffQuot_cutoff_le (μ := μ) hη hηc
  have hnorm : ∀ h : ℝ, 0 < |h| → |h| ≤ δ →
      (∫ t, (∫ z, (η z * diffQuot k h (fun y => w (t, y)) z) ^ 2) ∂μ) ≤ C := by
    intro h hhpos hh
    have hroomh : _root_.Metric.cthickening |h| (tsupport η) ⊆ Ω :=
      (_root_.Metric.cthickening_mono hh _).trans hroom
    have heq := integral_sq_cutoff_diffQuot_uncurry_compLpL hΩ.measurableSet A v η k h hroomh
    change (∫ t, (∫ z, (η z * diffQuot k h
      (fun y => Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
        (A.compLpL 2 μ v) (t,y)) z) ^ 2) ∂μ) ≤ C
    rw [heq]
    have hηLp : _root_.MeasureTheory.MemLp η ∞ volume := hη.continuous.memLp_of_hasCompactSupport hηc
    have hI (j) : _root_.MeasureTheory.Integrable (fun t => ∫ z, (η z * diffQuot k h
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (v t)) z) ^ 2) μ :=
      integrable_integral_sq_cutoff_diffQuot_comp hΩ.measurableSet hηLp k h hroomh
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j) (Lp.memLp v)
    apply le_trans ?_ (hbound k h hhpos hh)
    apply _root_.MeasureTheory.integral_mono (hI i) (_root_.MeasureTheory.integrable_finsetSum _ fun j _ => hI j)
    intro t
    let f := fun j => ∫ z, (η z * diffQuot k h
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (v t)) z) ^ 2
    have hf : ∀ j ∈ Finset.univ, 0 ≤ f j := fun _ _ => _root_.MeasureTheory.integral_nonneg fun _ => sq_nonneg _
    exact Finset.single_le_sum hf (Finset.mem_univ i)
  obtain ⟨H, _, hweak⟩ := hinverse hΩ.measurableSet hΩ₀ hηone (Lp.memLp w) k hδ hroom hnorm
  refine ⟨H, ?_⟩
  have hsub : Ω₀ ⊆ Ω := by
    intro z hz
    apply hroom
    apply _root_.Metric.self_subset_cthickening
    exact subset_tsupport η (by change η z ≠ 0; rw [hηone z hz]; norm_num)
  filter_upwards [hweak, dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs μ i v]
    with t ht hwt
  have hsource := hwt.filter_mono (_root_.MeasureTheory.ae_mono (Measure.restrict_mono hsub le_rfl))
  intro ψ hψ hψc hψs
  have he := ht ψ hψ hψc hψs
  have heq : (∫ z in Ω₀, w (t,z) * fderiv ℝ ψ z (EuclideanSpace.single k 1)) =
      ∫ z in Ω₀, dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) z *
        fderiv ℝ ψ z (EuclideanSpace.single k 1) := by
    apply _root_.MeasureTheory.integral_congr_ae
    exact hsource.mono fun z hz => congrArg (fun r => r * fderiv ℝ ψ z (EuclideanSpace.single k 1)) hz
  exact heq.symm.trans he

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_ae_weak_partial_local_partial_of_diffQuot_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_ae_weak_partial_local_partial_of_diffQuot_bound target :: scope.openDecls } }

theorem exists_lp_second_weak_derivative_of_local_diffQuot_bound
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω Ω₀ : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : _root_.MeasureTheory.Measure ℝ} [_root_.MeasureTheory.IsLocallyFiniteMeasure μ] (v : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ)
    {η : EuStd → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hΩ₀ : IsOpen Ω₀) (hηone : ∀ z ∈ Ω₀, η z = 1)
    {δ C : ℝ} (hδ : 0 < δ) (hroom : _root_.Metric.cthickening δ (tsupport η) ⊆ Ω)
    (hbound : ∀ k h, 0 < |h| → |h| ≤ δ →
      (∫ t, (∑ i, ∫ z, (η z * diffQuot k h
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) z) ^ 2) ∂μ) ≤ C) :
    ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω₀)),
      (∀ i k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) Ω₀) ∧
      ∀ᵐ t ∂μ, MemWkp 2 2
        (fun z => H1ComplDirichletToLp q (v t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₀ := by
  have hsecond (i k : Fin (Module.finrank ℝ EuN)) :=
    exists_ae_weak_partial_local_partial_of_diffQuot_bound q α hΩ hΩc hΩs
      v hη hηc hΩ₀ hηone hδ hroom hbound i k
  choose H hH using hsecond
  refine ⟨H, hH, ?_⟩
  have hsecond' := ae_all_iff.mpr (fun i => ae_all_iff.mpr (hH i))
  have hHLp := ae_all_iff.mpr (fun i => ae_all_iff.mpr
    (fun k => (Lp.memLp (H i k)).prodMk_left (by norm_num)))
  filter_upwards [hsecond', hHLp] with t hwt hHt
  let g := fun i => dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)
  have hsub : Ω₀ ⊆ Ω := by
    intro z hz
    apply hroom
    apply _root_.Metric.self_subset_cthickening
    exact subset_tsupport η (by change η z ≠ 0; rw [hηone z hz]; norm_num)
  apply memWkp_two_of_hasWeakPartialDeriv (by norm_num) hΩ₀
    ((memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs (v t)).memLp.mono_measure
      (Measure.restrict_mono hsub le_rfl)) (g := fun i z => g i z)
  · intro i
    exact ⟨(Lp.memLp (g i)).mono_measure (Measure.restrict_mono hsub le_rfl),
      fun k => ⟨fun z => H i k (t, z), hHt i k, hwt i k⟩⟩
  · intro i
    exact DeGiorgi.HasWeakPartialDeriv.restrict hΩ₀ hsub
      (hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_second_weak_derivative_of_local_diffQuot_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_second_weak_derivative_of_local_diffQuot_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_second_weak_derivative_of_local_diffQuot_bound ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_second_weak_derivative_of_local_diffQuot_bound


theorem exists_lp_second_weak_derivative_of_local_diffQuot_bound_restrict
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω Ω₀ : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {μ : _root_.MeasureTheory.Measure ℝ} (S : Set ℝ) [_root_.MeasureTheory.IsLocallyFiniteMeasure (μ.restrict S)]
    (v : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ)
    {η : EuStd → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hΩ₀ : IsOpen Ω₀) (hηone : ∀ z ∈ Ω₀, η z = 1)
    {δ C : ℝ} (hδ : 0 < δ) (hroom : _root_.Metric.cthickening δ (tsupport η) ⊆ Ω)
    (hbound : ∀ k h, 0 < |h| → |h| ≤ δ →
      (∫ t, (∑ i, ∫ z, (η z * diffQuot k h
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) z) ^ 2) ∂μ.restrict S) ≤ C) :
    ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        _root_.MeasureTheory.Lp ℝ 2 ((μ.restrict S).prod (volume.restrict Ω₀)),
      (∀ i k, ∀ᵐ t ∂μ.restrict S, DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) Ω₀) ∧
      ∀ᵐ t ∂μ.restrict S, MemWkp 2 2
        (fun z => H1ComplDirichletToLp q (v t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₀ := by
  have hvS : _root_.MeasureTheory.MemLp (v : ℝ → H1ComplDirichlet q) 2 (μ.restrict S) :=
    (Lp.memLp v).mono_measure Measure.restrict_le_self
  let vS : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 (μ.restrict S) := hvS.toLp v
  have hvSeq : (vS : ℝ → H1ComplDirichlet q) =ᵐ[μ.restrict S] v := hvS.coeFn_toLp
  have hboundS : ∀ k h, 0 < |h| → |h| ≤ δ →
      (∫ t, (∑ i, ∫ z, (η z * diffQuot k h
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (vS t)) z) ^ 2)
        ∂μ.restrict S) ≤ C := by
    intro k h hhpos hh
    have heq : (∫ t, (∑ i, ∫ z, (η z * diffQuot k h
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (vS t)) z) ^ 2)
        ∂μ.restrict S) =
        ∫ t, (∑ i, ∫ z, (η z * diffQuot k h
          (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) z) ^ 2)
          ∂μ.restrict S := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [hvSeq] with t ht
      rw [ht]
    rw [heq]
    exact hbound k h hhpos hh
  obtain ⟨H, hH, hW⟩ := exists_lp_second_weak_derivative_of_local_diffQuot_bound
    q α hΩ hΩc hΩs vS hη hηc hΩ₀ hηone hδ hroom hboundS
  refine ⟨H, ?_, ?_⟩
  · intro i k
    filter_upwards [hH i k, hvSeq] with t ht hvt
    simpa only [hvt] using ht
  · filter_upwards [hW, hvSeq] with t ht hvt
    simpa only [hvt] using ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_second_weak_derivative_of_local_diffQuot_bound_restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_second_weak_derivative_of_local_diffQuot_bound_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_second_weak_derivative_of_local_diffQuot_bound_restrict ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_second_weak_derivative_of_local_diffQuot_bound_restrict

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
