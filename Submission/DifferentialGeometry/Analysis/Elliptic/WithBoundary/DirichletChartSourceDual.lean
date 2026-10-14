import Submission.DifferentialGeometry.Analysis.Integration.Lp.SpacetimeDual
import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakChartCutoff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.NNReal _root_.Topology _root_.InnerProductSpace
namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
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
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry : MeasurableSpace EuStd := WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry target :: scope.openDecls } }

theorem exists_lp_chart_source_dual
    {q : SmoothRiemannianMetric I_hs M} (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {Z : Type*} [MeasurableSpace Z] {μ : _root_.MeasureTheory.Measure Z}
    (F : _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω))) :
    ∃ ℓ : _root_.MeasureTheory.Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ, ∀ η : _root_.MeasureTheory.Lp ℝ 2 μ, ∀ v : H1ComplDirichlet q,
      (∫ t, η t * ℓ t v ∂μ) =
        ∫ p, η p.1 * F p * H1ComplDirichletToLp q v
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂μ.prod (volume.restrict Ω) := by
  let J : H1ComplDirichlet q →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (volume.restrict Ω) :=
    (chartRestrictionLp q α hΩ.measurableSet hΩc
      (hΩs.trans (_root_.Set.image_mono interior_subset)) 2).comp (H1ComplDirichletToLp q)
  obtain ⟨ℓ, hℓ⟩ := MeasureTheory.Lp.exists_lp_dual_integral_prod J F
  refine ⟨ℓ, ?_⟩
  intro η v
  rw [hℓ η v]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_snd (μ := μ)
      (ν := volume.restrict Ω).ae
      (chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc
        (hΩs.trans (_root_.Set.image_mono interior_subset)) 2 (H1ComplDirichletToLp q v))] with p hp
  change η p.1 * _root_.Inner.inner ℝ (F p)
    ((chartRestrictionLp q α hΩ.measurableSet hΩc
      (hΩs.trans (_root_.Set.image_mono interior_subset)) 2) (H1ComplDirichletToLp q v) p.2) = _
  rw [hp]
  simp only [Real.inner_apply, mul_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_source_dual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_source_dual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_source_dual ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_source_dual
theorem exists_lp_chart_divergence_dual
    {q : SmoothRiemannianMetric I_hs M} (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {Z : Type*} [MeasurableSpace Z] {μ : _root_.MeasureTheory.Measure Z}
    (F : Fin (Module.finrank ℝ EuN) → _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω))) :
    ∃ ℓ : _root_.MeasureTheory.Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ, ∀ η : _root_.MeasureTheory.Lp ℝ 2 μ, ∀ v : H1ComplDirichlet q,
      (∫ t, η t * ℓ t v ∂μ) =
        ∑ j, ∫ p, η p.1 * F j p *
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j v p.2 ∂μ.prod (volume.restrict Ω) := by
  classical
  have hparts (j : Fin (Module.finrank ℝ EuN)) :=
    MeasureTheory.Lp.exists_lp_dual_integral_prod
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j) (F j)
  choose L hL using hparts
  refine ⟨∑ j, L j, ?_⟩
  intro η v
  have hint (j : Fin (Module.finrank ℝ EuN)) : _root_.MeasureTheory.Integrable (fun t => η t * L j t v) μ := by
    exact (Lp.memLp η).integrable_mul ((ContinuousLinearMap.apply ℝ ℝ v).comp_memLp (L j))
  calc
    (∫ t, η t * (∑ j, L j) t v ∂μ) = ∫ t, ∑ j, η t * L j t v ∂μ := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [Lp.coeFn_finsetSum Finset.univ L] with t ht
      rw [ht]
      simp only [Finset.sum_apply]
      change η t * ((ContinuousLinearMap.apply ℝ ℝ v) (∑ j, L j t)) = _
      rw [map_sum, Finset.mul_sum]
      rfl
    _ = ∑ j, ∫ t, η t * L j t v ∂μ := _root_.MeasureTheory.integral_finsetSum _ (fun j _ => hint j)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hL j η v]
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards with p
      simp only [Real.inner_apply, mul_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_divergence_dual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_divergence_dual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_divergence_dual ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_divergence_dual

theorem exists_lp_chart_source_sub_divergence_dual
    {q : SmoothRiemannianMetric I_hs M} (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {Z : Type*} [MeasurableSpace Z] {μ : _root_.MeasureTheory.Measure Z}
    {B : Z × EuStd → ℝ} {Q : Fin (Module.finrank ℝ EuN) → Z × EuStd → ℝ}
    (hB : _root_.MeasureTheory.MemLp B 2 (μ.prod (volume.restrict Ω)))
    (hQ : ∀ j, _root_.MeasureTheory.MemLp (Q j) 2 (μ.prod (volume.restrict Ω))) :
    ∃ ℓ : _root_.MeasureTheory.Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ, ∀ τ : _root_.MeasureTheory.Lp ℝ 2 μ, ∀ v : H1ComplDirichlet q,
      (∫ t, τ t * ℓ t v ∂μ) =
        (∫ p, τ p.1 * B p * H1ComplDirichletToLp q v
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2)) ∂μ.prod (volume.restrict Ω)) -
        ∑ j, ∫ p, τ p.1 * Q j p * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j v p.2
          ∂μ.prod (volume.restrict Ω) := by
  obtain ⟨Ls, hLs⟩ := exists_lp_chart_source_dual α hΩ hΩc hΩs (hB.toLp B)
  obtain ⟨Ld, hLd⟩ := exists_lp_chart_divergence_dual α hΩ hΩc hΩs
    (fun j => (hQ j).toLp (Q j))
  refine ⟨Ls - Ld, ?_⟩
  intro τ v
  have hints : _root_.MeasureTheory.Integrable (fun t => τ t * Ls t v) μ :=
    (Lp.memLp τ).integrable_mul ((ContinuousLinearMap.apply ℝ ℝ v).comp_memLp Ls)
  have hintd : _root_.MeasureTheory.Integrable (fun t => τ t * Ld t v) μ :=
    (Lp.memLp τ).integrable_mul ((ContinuousLinearMap.apply ℝ ℝ v).comp_memLp Ld)
  calc
    (∫ t, τ t * (Ls - Ld) t v ∂μ) =
        (∫ t, τ t * Ls t v ∂μ) - ∫ t, τ t * Ld t v ∂μ := by
      rw [← _root_.MeasureTheory.integral_sub hints hintd]
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [Lp.coeFn_sub Ls Ld] with t ht
      rw [ht]
      change τ t * (Ls t v - Ld t v) = _
      ring
    _ = _ := by
      rw [hLs, hLd]
      apply congrArg₂ (fun a b : ℝ => a - b)
      · apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards [hB.coeFn_toLp] with p hp
        rw [hp]
      · apply Finset.sum_congr rfl
        intro j _
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards [(hQ j).coeFn_toLp] with p hp
        rw [hp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_source_sub_divergence_dual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_source_sub_divergence_dual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_source_sub_divergence_dual ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_source_sub_divergence_dual


theorem exists_lp_chart_source_dual_integral
    {Z : Type*} [MeasurableSpace Z] {μ : _root_.MeasureTheory.Measure Z} [_root_.MeasureTheory.SFinite μ]
    {q : SmoothRiemannianMetric I_hs M} (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (F : _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω))) :
    ∃ ℓ : _root_.MeasureTheory.Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
      (∀ τ : _root_.MeasureTheory.Lp ℝ 2 μ, ∀ z : H1ComplDirichlet q,
        (∫ t, τ t * ℓ t z ∂μ) =
          ∫ p, τ p.1 * F p * H1ComplDirichletToLp q z
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm p.2))
              ∂μ.prod (volume.restrict Ω)) ∧
      (∀ z : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ,
        (∫ t, ℓ t (z t) ∂μ) =
          ∫ p, F p * ((Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
            (((chartRestrictionLp q α hΩ.measurableSet hΩc
              (hΩs.trans (_root_.Set.image_mono interior_subset)) 2).comp
              (H1ComplDirichletToLp q)).compLpL 2 μ z)) p) ∂μ.prod (volume.restrict Ω)) ∧
      ∀ z : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ,
        (∫ t, ℓ t (z t) ∂μ) =
          ∫ t, (∫ x in Ω, F (t, x) * H1ComplDirichletToLp q (z t)
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))) ∂μ := by
  let J : H1ComplDirichlet q →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (volume.restrict Ω) :=
    (chartRestrictionLp q α hΩ.measurableSet hΩc
      (hΩs.trans (_root_.Set.image_mono interior_subset)) 2).comp (H1ComplDirichletToLp q)
  have hex := MeasureTheory.Lp.exists_lp_scalar_dual_integral_uncurry J F
  let ℓ := Classical.choose hex
  have hℓ := (Classical.choose_spec hex).1
  have hvariable := (Classical.choose_spec hex).2
  have hR (z : H1ComplDirichlet q) :
      (J z : EuStd → ℝ) =ᵐ[volume.restrict Ω] fun x => H1ComplDirichletToLp q z
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x)) :=
    chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc
      (hΩs.trans (_root_.Set.image_mono interior_subset)) 2 (H1ComplDirichletToLp q z)
  refine ⟨ℓ, ?_, ?_, ?_⟩
  · intro τ z
    apply (hℓ τ z).trans
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := μ)
      (ν := volume.restrict Ω)).ae (hR z)] with p hp
    exact congrArg (fun r : ℝ => τ p.1 * F p * r) hp
  · intro z
    exact hvariable z
  · intro z
    apply (hvariable z).trans
    have hscalar : (∫ p, F p * (Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
        (J.compLpL 2 μ z)) p ∂μ.prod (volume.restrict Ω)) =
        ∫ p, _root_.Inner.inner ℝ (F p) ((Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
          (J.compLpL 2 μ z)) p) ∂μ.prod (volume.restrict Ω) :=
      _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => mul_comm _ _)
    apply hscalar.trans
    apply (MeasureTheory.Lp.integral_inner_uncurry_compLpL_eq_integral_integral
      (A := Z) (B := EuStd) (E := ℝ) (V := H1ComplDirichlet q)
      (μ := μ) (ν := volume.restrict Ω) J F z).trans
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards with t
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hR (z t)] with x hx
    rw [hx]
    exact mul_comm _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_source_dual_integral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_source_dual_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_source_dual_integral ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_source_dual_integral

theorem exists_lp_chart_divergence_dual_uncurry
    {q : SmoothRiemannianMetric I_hs M} (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {Z : Type*} [MeasurableSpace Z] {μ : _root_.MeasureTheory.Measure Z}
    (F : Fin (Module.finrank ℝ EuN) → _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω))) :
    ∃ ℓ : _root_.MeasureTheory.Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
      (∀ η : _root_.MeasureTheory.Lp ℝ 2 μ, ∀ v : H1ComplDirichlet q,
        (∫ t, η t * ℓ t v ∂μ) =
          ∑ j, ∫ p, η p.1 * F j p *
            dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j v p.2
              ∂μ.prod (volume.restrict Ω)) ∧
      (∀ z : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ,
        (∫ t, ℓ t (z t) ∂μ) =
          ∑ j, ∫ p, F j p * (Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
            ((dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j).compLpL 2 μ z)) p
              ∂μ.prod (volume.restrict Ω)) := by
  classical
  have hparts (j : Fin (Module.finrank ℝ EuN)) :=
    MeasureTheory.Lp.exists_lp_dual_integral_uncurry
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j) (F j)
  choose L hL hLv using hparts
  refine ⟨∑ j, L j, ?_, ?_⟩
  · intro η v
    have hint (j : Fin (Module.finrank ℝ EuN)) : _root_.MeasureTheory.Integrable (fun t => η t * L j t v) μ := by
      exact (Lp.memLp η).integrable_mul ((ContinuousLinearMap.apply ℝ ℝ v).comp_memLp (L j))
    calc
      (∫ t, η t * (∑ j, L j) t v ∂μ) = ∫ t, ∑ j, η t * L j t v ∂μ := by
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards [Lp.coeFn_finsetSum Finset.univ L] with t ht
        rw [ht]
        simp only [Finset.sum_apply]
        change η t * ((ContinuousLinearMap.apply ℝ ℝ v) (∑ j, L j t)) = _
        rw [map_sum, Finset.mul_sum]
        rfl
      _ = ∑ j, ∫ t, η t * L j t v ∂μ := _root_.MeasureTheory.integral_finsetSum _ (fun j _ => hint j)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hL j η v]
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards with p
        simp only [Real.inner_apply, mul_assoc]
  · intro z
    have hint (j : Fin (Module.finrank ℝ EuN)) : _root_.MeasureTheory.Integrable (fun t => L j t (z t)) μ := by
      apply ((Lp.memLp (L j)).norm.integrable_mul (Lp.memLp z).norm).mono'
      · exact (ContinuousLinearMap.apply ℝ ℝ).aestronglyMeasurable_comp₂
          (Lp.aestronglyMeasurable z) (Lp.aestronglyMeasurable (L j))
      · exact Eventually.of_forall fun t => (L j t).le_opNorm (z t)
    calc
      (∫ t, (∑ j, L j) t (z t) ∂μ) = ∫ t, ∑ j, L j t (z t) ∂μ := by
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards [Lp.coeFn_finsetSum Finset.univ L] with t ht
        rw [ht]
        simp only [Finset.sum_apply]
        change ((ContinuousLinearMap.apply ℝ ℝ (z t)) (∑ j, L j t)) = _
        rw [map_sum]
        rfl
      _ = ∑ j, ∫ t, L j t (z t) ∂μ := _root_.MeasureTheory.integral_finsetSum _ (fun j _ => hint j)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        exact (hLv j z).trans (_root_.MeasureTheory.integral_congr_ae
          (Eventually.of_forall fun p => by
            exact mul_comm _ _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_divergence_dual_uncurry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_divergence_dual_uncurry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_divergence_dual_uncurry ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_divergence_dual_uncurry

theorem exists_lp_chart_divergence_dual_integral_integral
    {q : SmoothRiemannianMetric I_hs M} (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {Z : Type*} [MeasurableSpace Z] {μ : _root_.MeasureTheory.Measure Z} [_root_.MeasureTheory.SFinite μ]
    (F : Fin (Module.finrank ℝ EuN) → _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω))) :
    ∃ ℓ : _root_.MeasureTheory.Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ,
      (∀ η : _root_.MeasureTheory.Lp ℝ 2 μ, ∀ v : H1ComplDirichlet q,
        (∫ t, η t * ℓ t v ∂μ) =
          ∑ j, ∫ p, η p.1 * F j p *
            dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j v p.2
              ∂μ.prod (volume.restrict Ω)) ∧
      (∀ z : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ,
        (∫ t, ℓ t (z t) ∂μ) =
          ∑ j, ∫ p, F j p * (Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
            ((dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j).compLpL 2 μ z)) p
              ∂μ.prod (volume.restrict Ω)) ∧
      (∀ z : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ,
        (∫ t, ℓ t (z t) ∂μ) =
          ∑ j, ∫ t, ∫ x, F j (t, x) *
            dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (z t) x
              ∂volume.restrict Ω ∂μ) := by
  classical
  have hparts (j : Fin (Module.finrank ℝ EuN)) :=
    MeasureTheory.Lp.exists_lp_dual_integral_uncurry
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j) (F j)
  choose L hL hLv using hparts
  refine ⟨∑ j, L j, ?_, ?_, ?_⟩
  · intro η v
    have hint (j : Fin (Module.finrank ℝ EuN)) : _root_.MeasureTheory.Integrable (fun t => η t * L j t v) μ := by
      exact (Lp.memLp η).integrable_mul ((ContinuousLinearMap.apply ℝ ℝ v).comp_memLp (L j))
    calc
      (∫ t, η t * (∑ j, L j) t v ∂μ) = ∫ t, ∑ j, η t * L j t v ∂μ := by
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards [Lp.coeFn_finsetSum Finset.univ L] with t ht
        rw [ht]
        simp only [Finset.sum_apply]
        change η t * ((ContinuousLinearMap.apply ℝ ℝ v) (∑ j, L j t)) = _
        rw [map_sum, Finset.mul_sum]
        rfl
      _ = ∑ j, ∫ t, η t * L j t v ∂μ := _root_.MeasureTheory.integral_finsetSum _ (fun j _ => hint j)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hL j η v]
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards with p
        simp only [Real.inner_apply, mul_assoc]
  · intro z
    have hint (j : Fin (Module.finrank ℝ EuN)) : _root_.MeasureTheory.Integrable (fun t => L j t (z t)) μ := by
      apply ((Lp.memLp (L j)).norm.integrable_mul (Lp.memLp z).norm).mono'
      · exact (ContinuousLinearMap.apply ℝ ℝ).aestronglyMeasurable_comp₂
          (Lp.aestronglyMeasurable z) (Lp.aestronglyMeasurable (L j))
      · exact Eventually.of_forall fun t => (L j t).le_opNorm (z t)
    calc
      (∫ t, (∑ j, L j) t (z t) ∂μ) = ∫ t, ∑ j, L j t (z t) ∂μ := by
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards [Lp.coeFn_finsetSum Finset.univ L] with t ht
        rw [ht]
        simp only [Finset.sum_apply]
        change ((ContinuousLinearMap.apply ℝ ℝ (z t)) (∑ j, L j t)) = _
        rw [map_sum]
        rfl
      _ = ∑ j, ∫ t, L j t (z t) ∂μ := _root_.MeasureTheory.integral_finsetSum _ (fun j _ => hint j)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        exact (hLv j z).trans (_root_.MeasureTheory.integral_congr_ae
          (Eventually.of_forall fun p => by
            exact mul_comm _ _))
  · intro z
    have hint (j : Fin (Module.finrank ℝ EuN)) : _root_.MeasureTheory.Integrable (fun t => L j t (z t)) μ := by
      apply ((Lp.memLp (L j)).norm.integrable_mul (Lp.memLp z).norm).mono'
      · exact (ContinuousLinearMap.apply ℝ ℝ).aestronglyMeasurable_comp₂
          (Lp.aestronglyMeasurable z) (Lp.aestronglyMeasurable (L j))
      · exact Eventually.of_forall fun t => (L j t).le_opNorm (z t)
    calc
      (∫ t, (∑ j, L j) t (z t) ∂μ) = ∫ t, ∑ j, L j t (z t) ∂μ := by
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards [Lp.coeFn_finsetSum Finset.univ L] with t ht
        rw [ht]
        simp only [Finset.sum_apply]
        change ((ContinuousLinearMap.apply ℝ ℝ (z t)) (∑ j, L j t)) = _
        rw [map_sum]
        rfl
      _ = ∑ j, ∫ t, L j t (z t) ∂μ := _root_.MeasureTheory.integral_finsetSum _ (fun j _ => hint j)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        have hid := (hLv j z).trans
          (MeasureTheory.Lp.integral_inner_uncurry_compLpL_eq_integral_integral
            (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j) (F j) z)
        exact hid.trans (_root_.MeasureTheory.integral_congr_ae (Eventually.of_forall fun t =>
          _root_.MeasureTheory.integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_divergence_dual_integral_integral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_divergence_dual_integral_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_divergence_dual_integral_integral ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_chart_divergence_dual_integral_integral


end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
