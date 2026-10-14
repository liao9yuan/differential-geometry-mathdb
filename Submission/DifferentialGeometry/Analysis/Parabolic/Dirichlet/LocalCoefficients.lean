import Submission.DifferentialGeometry.Analysis.Elliptic.Coefficients
import Submission.DifferentialGeometry.Analysis.Elliptic.MetricExtension
import Submission.DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityFamily
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.LocalVariation
import Submission.DifferentialGeometry.Analysis.Integration.Lp.ContinuousOn
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Submission.DifferentialGeometry.Tensor.Coordinates.ModelBasis

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

set_option autoImplicit false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.InnerProductSpace _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Analysis.Laplacian.MetricExtension

open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [IsManifold I ∞ M] in
private theorem chartInverse_prod_continuousOn {Z : Type*} [TopologicalSpace Z] (α : M) (J : Set Z) :
    ContinuousOn
      (fun p : Z × EuclN =>
        (p.1, (extChartAt I α).symm ((toEuclidean (E := E)).symm p.2)))
      (J ×ˢ chartTargetEuclid (I := I) α) := by
  apply continuous_fst.continuousOn.prodMk
  apply (continuousOn_extChartAt_symm (I := I) α).comp
    ((toEuclidean (E := E)).symm.continuous.comp continuous_snd).continuousOn
  intro p hp
  exact toEuclidean_symm_mem_target hp.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartInverse_prod_continuousOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartInverse_prod_continuousOn target :: scope.openDecls } }

private theorem chartInverse_prod_mapsTo_baseSet {Z : Type*} (α : M) (J : Set Z) :
    _root_.Set.MapsTo
      (fun p : Z × EuclN =>
        (p.1, (extChartAt I α).symm ((toEuclidean (E := E)).symm p.2)))
      (J ×ˢ chartTargetEuclid (I := I) α)
      (J ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) := by
  intro p hp
  refine ⟨hp.1, ?_⟩
  rw [trivializationAt_baseSet_eq_chartAt_source,
    ← extChartAt_source_eq_chartAt_source (I := I)]
  exact (extChartAt I α).map_target (toEuclidean_symm_mem_target hp.2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartInverse_prod_mapsTo_baseSet
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartInverse_prod_mapsTo_baseSet target :: scope.openDecls } }

theorem densityOnEuclid_family_continuousOn
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric) {J : Set ℝ} (hJ : J ⊆ D.regular)
    (α : M) :
    ContinuousOn (fun p : ℝ × EuclN => densityOnEuclid (I := I) (G.metric p.1) α p.2)
      (J ×ˢ chartTargetEuclid (I := I) α) := by
  have hd : ContinuousOn (fun p : ℝ × M => chartDensity (I := I) (G.metric p.1) α p.2)
      (J ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :=
    (chartDensity_family_contMDiffOn (I := I) G.metric α
      (hG.chartGramMatrix_contDiffOn (I := I) hJ α)).continuousOn
  have hc := hd.comp (chartInverse_prod_continuousOn (I := I) α J)
    (chartInverse_prod_mapsTo_baseSet (I := I) α J)
  exact hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_family_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_family_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_family_continuousOn ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_family_continuousOn

theorem gramOnEuclid_family_continuousOn
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric) {J : Set ℝ} (hJ : J ⊆ D.regular)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun p : ℝ × EuclN => gramOnEuclid (I := I) (G.metric p.1) α i j p.2)
      (J ×ˢ chartTargetEuclid (I := I) α) := by
  have hg := hG.chartGramMatrix_continuousOn (I := I) hJ α i j
  have hc := hg.comp (chartInverse_prod_continuousOn (I := I) α J)
    (chartInverse_prod_mapsTo_baseSet (I := I) α J)
  exact hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.gramOnEuclid_family_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.gramOnEuclid_family_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.gramOnEuclid_family_continuousOn ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.gramOnEuclid_family_continuousOn

theorem invGramOnEuclid_family_continuousOn
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric) {J : Set ℝ} (hJ : J ⊆ D.regular)
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun p : ℝ × EuclN => invGramOnEuclid (I := I) (G.metric p.1) α i j p.2)
      (J ×ˢ chartTargetEuclid (I := I) α) := by
  let A := fun p : ℝ × EuclN =>
    chartGramMatrix (I := I) (G.metric p.1) α
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm p.2))
  have hA : ContinuousOn A (J ×ˢ chartTargetEuclid (I := I) α) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact gramOnEuclid_family_continuousOn hG hJ α i j
  intro p hp
  have hdet : (A p).det ≠ 0 := ne_of_gt
    (chartGramMatrix_det_pos (G.metric p.1) α
      ((chartInverse_prod_mapsTo_baseSet (I := I) α J) hp).2)
  have hinv : ContinuousAt Ring.inverse (A p).det := by
    simpa only [Ring.inverse_eq_inv'] using _root_.ContinuousInv₀.continuousAt_inv₀ hdet
  have hc := (continuousAt_matrix_inv (A p) hinv).comp_continuousWithinAt (hA p hp)
  exact (continuous_apply j).continuousAt.comp_continuousWithinAt
    ((continuous_apply i).continuousAt.comp_continuousWithinAt hc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_family_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_family_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_family_continuousOn ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_family_continuousOn

theorem exists_uniform_inv_gram_quadratic_lower_bound
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular) (α : M)
    {K : Set EuclN} (hKc : IsCompact K) (hKs : K ⊆ chartTargetEuclid (I := I) α) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ J, ∀ y ∈ K, ∀ ξ : EuclN,
      c * ‖ξ‖ ^ 2 ≤
        ⟪ξ, DeGiorgi.matMulE (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
          invGramOnEuclid (I := I) (G.metric t) α i j y)) ξ⟫_ℝ := by
  obtain ⟨c, hc, hbound⟩ := Schauder.exists_uniform_matrix_quadratic_lower_bound (hJc.prod hKc)
    (fun p : ℝ × EuclN => Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      invGramOnEuclid (I := I) (G.metric p.1) α i j p.2))
    (fun i j => (invGramOnEuclid_family_continuousOn hG hJ α i j).mono
      (_root_.Set.prod_mono Subset.rfl hKs))
    (fun p hp => invGramOnEuclid_posDef (I := I) (G.metric p.1) α (hKs hp.2))
  refine ⟨c, hc, ?_⟩
  intro t ht y hy ξ
  change c * ‖ξ‖ ^ 2 ≤ (DeGiorgi.matMulE _ ξ).ofLp ⬝ᵥ _root_.Star.star ξ.ofLp
  rw [DeGiorgi.matMulE_ofLp, dotProduct_comm]
  exact hbound (t, y) ⟨ht, hy⟩ ξ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_uniform_inv_gram_quadratic_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_uniform_inv_gram_quadratic_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_uniform_inv_gram_quadratic_lower_bound ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_uniform_inv_gram_quadratic_lower_bound

theorem exists_uniform_weighted_inv_gram_quadratic_lower_bound
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular) (α : M)
    {K : Set EuclN} (hKc : IsCompact K) (hKs : K ⊆ chartTargetEuclid (I := I) α) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ J, ∀ y ∈ K, ∀ ξ : EuclN,
      c * ‖ξ‖ ^ 2 ≤
        ⟪ξ, DeGiorgi.matMulE (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
          weightedInvGramOnEuclid (I := I) (G.metric t) α i j y)) ξ⟫_ℝ := by
  obtain ⟨c, hc, hbound⟩ := Schauder.exists_uniform_matrix_quadratic_lower_bound (hJc.prod hKc)
    (fun p : ℝ × EuclN => Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      weightedInvGramOnEuclid (I := I) (G.metric p.1) α i j p.2))
    (fun i j => ((densityOnEuclid_family_continuousOn hG hJ α).mul
      (invGramOnEuclid_family_continuousOn hG hJ α i j)).mono (_root_.Set.prod_mono Subset.rfl hKs))
    (fun p hp => weightedInvGramOnEuclid_posDef (I := I) (G.metric p.1) α (hKs hp.2))
  refine ⟨c, hc, ?_⟩
  intro t ht y hy ξ
  change c * ‖ξ‖ ^ 2 ≤ (DeGiorgi.matMulE _ ξ).ofLp ⬝ᵥ _root_.Star.star ξ.ofLp
  rw [DeGiorgi.matMulE_ofLp, dotProduct_comm]
  exact hbound (t, y) ⟨ht, hy⟩ ξ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_uniform_weighted_inv_gram_quadratic_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_uniform_weighted_inv_gram_quadratic_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_uniform_weighted_inv_gram_quadratic_lower_bound ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.exists_uniform_weighted_inv_gram_quadratic_lower_bound

theorem _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.chartCoeff_family_continuousOn
    {Z : Type*} [TopologicalSpace Z]
    (X : Z → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {J : Set Z} (α : M)
    (hX : ContinuousOn (fun p : Z × M => TotalSpace.mk' E p.2 (X p.1 p.2))
      (J ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet))
    (i : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun p : Z × M => chartCoeff (I := I) α (X p.1) i p.2)
      (J ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) := by
  let e := _root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) α
  have hc : ContinuousOn (fun p : Z × M =>
      (e (TotalSpace.mk' E p.2 (X p.1 p.2))).2) (J ×ˢ e.baseSet) := by
    apply continuous_snd.comp_continuousOn
    apply e.continuousOn.comp hX
    intro p hp
    exact e.mem_source.mpr hp.2
  let L := ((chartModelBasis E).coord i).toContinuousLinearMap
  have hcomp := L.continuous.comp_continuousOn hc
  refine hcomp.congr ?_
  intro p _
  change (chartModelBasis E).repr ((e (TotalSpace.mk' E p.2 (X p.1 p.2))).2) i =
    (chartModelBasis E).coord i ((e (TotalSpace.mk' E p.2 (X p.1 p.2))).2)
  rw [Module.Basis.coord_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.chartCoeff_family_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.chartCoeff_family_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.chartCoeff_family_continuousOn ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.chartCoeff_family_continuousOn

theorem chartCoeffOnE_comp_toEuclidean_symm_family_continuousOn
    {Z : Type*} [TopologicalSpace Z]
    (X : Z → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {J : Set Z} (α : M)
    (hX : ContinuousOn (fun p : Z × M => TotalSpace.mk' E p.2 (X p.1 p.2))
      (J ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)) (i : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun p : Z × EuclN =>
      chartCoeffOnE (I := I) α (X p.1) i ((toEuclidean (E := E)).symm p.2))
      (J ×ˢ chartTargetEuclid (I := I) α) := by
  have hc := chartCoeff_family_continuousOn (I := I) X α
    hX i
  have hcomp := hc.comp (chartInverse_prod_continuousOn (I := I) α J)
    (chartInverse_prod_mapsTo_baseSet (I := I) α J)
  exact hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartCoeffOnE_comp_toEuclidean_symm_family_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartCoeffOnE_comp_toEuclidean_symm_family_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartCoeffOnE_comp_toEuclidean_symm_family_continuousOn ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartCoeffOnE_comp_toEuclidean_symm_family_continuousOn

theorem traceTimeDerivMetric_comp_chartInverse_continuousOn
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric) {J : Set ℝ} (hJ : J ⊆ D.regular)
    (α : M) :
    ContinuousOn (fun p : ℝ × EuclN =>
      traceTimeDerivMetric (I := I) G.metric p.1
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm p.2)))
      (J ×ˢ chartTargetEuclid (I := I) α) := by
  apply (continuousOn_traceTimeDerivMetric_of_chartGram_contMDiffOn
    D.regular_isOpen (fun β i j => hG.chartGramMatrix_contDiffOn (I := I) Subset.rfl β i j)).comp
    (chartInverse_prod_continuousOn (I := I) α J)
  intro p hp
  exact ⟨hJ hp.1, _root_.Set.mem_univ _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.traceTimeDerivMetric_comp_chartInverse_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.traceTimeDerivMetric_comp_chartInverse_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.traceTimeDerivMetric_comp_chartInverse_continuousOn ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.traceTimeDerivMetric_comp_chartInverse_continuousOn

theorem densityOnEuclid_family_memLp_top
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular) (α : M)
    {Ω : Set EuclN} (hΩm : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ chartTargetEuclid (I := I) α) (μ : _root_.MeasureTheory.Measure (ℝ × EuclN)) :
    MemLp (fun p : ℝ × EuclN => densityOnEuclid (I := I) (G.metric p.1) α p.2) ∞
      (μ.restrict (J ×ˢ Ω)) := by
  exact (densityOnEuclid_family_continuousOn hG hJ α).mono
    (_root_.Set.prod_mono Subset.rfl hΩs) |>.memLp_top_of_subset_isCompact
      (hJc.prod hΩc) (hJc.measurableSet.prod hΩm)
      (_root_.Set.prod_mono Subset.rfl subset_closure)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_family_memLp_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_family_memLp_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_family_memLp_top ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_family_memLp_top

theorem invGramOnEuclid_family_memLp_top
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular) (α : M)
    {Ω : Set EuclN} (hΩm : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ chartTargetEuclid (I := I) α) (i j : Fin (Module.finrank ℝ E)) (μ : _root_.MeasureTheory.Measure (ℝ × EuclN)) :
    MemLp (fun p : ℝ × EuclN => invGramOnEuclid (I := I) (G.metric p.1) α i j p.2) ∞
      (μ.restrict (J ×ˢ Ω)) := by
  exact (invGramOnEuclid_family_continuousOn hG hJ α i j).mono
    (_root_.Set.prod_mono Subset.rfl hΩs) |>.memLp_top_of_subset_isCompact
      (hJc.prod hΩc) (hJc.measurableSet.prod hΩm)
      (_root_.Set.prod_mono Subset.rfl subset_closure)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_family_memLp_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_family_memLp_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_family_memLp_top ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_family_memLp_top

theorem weightedInvGramOnEuclid_family_memLp_top
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular) (α : M)
    {Ω : Set EuclN} (hΩm : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ chartTargetEuclid (I := I) α) (i j : Fin (Module.finrank ℝ E)) (μ : _root_.MeasureTheory.Measure (ℝ × EuclN)) :
    MemLp (fun p : ℝ × EuclN => weightedInvGramOnEuclid (I := I) (G.metric p.1) α i j p.2) ∞
      (μ.restrict (J ×ˢ Ω)) := by
  exact MemLp.mul' (p := ∞) (q := ∞) (r := ∞)
    (invGramOnEuclid_family_memLp_top hG hJc hJ α hΩm hΩc hΩs i j μ)
    (densityOnEuclid_family_memLp_top hG hJc hJ α hΩm hΩc hΩs μ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_family_memLp_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_family_memLp_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_family_memLp_top ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_family_memLp_top

theorem chartCoeffOnE_comp_toEuclidean_symm_family_memLp_top
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (X : Z → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {J : Set Z} (hJc : IsCompact J) (hJm : MeasurableSet J) (α : M)
    (hX : ContinuousOn (fun p : Z × M => TotalSpace.mk' E p.2 (X p.1 p.2))
      (J ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet))
    {Ω : Set EuclN} (hΩm : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ chartTargetEuclid (I := I) α)
    (i : Fin (Module.finrank ℝ E)) (μ : _root_.MeasureTheory.Measure (Z × EuclN)) :
    _root_.MeasureTheory.MemLp (fun p : Z × EuclN =>
      chartCoeffOnE (I := I) α (X p.1) i ((toEuclidean (E := E)).symm p.2)) ∞
      (μ.restrict (J ×ˢ Ω)) := by
  exact (chartCoeffOnE_comp_toEuclidean_symm_family_continuousOn X α hX i).mono
    (_root_.Set.prod_mono Subset.rfl hΩs) |>.memLp_top_of_subset_isCompact
      (hJc.prod hΩc) (hJm.prod hΩm)
      (_root_.Set.prod_mono Subset.rfl subset_closure)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartCoeffOnE_comp_toEuclidean_symm_family_memLp_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartCoeffOnE_comp_toEuclidean_symm_family_memLp_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartCoeffOnE_comp_toEuclidean_symm_family_memLp_top ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartCoeffOnE_comp_toEuclidean_symm_family_memLp_top

theorem traceTimeDerivMetric_comp_chartInverse_memLp_top
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular) (α : M)
    {Ω : Set EuclN} (hΩm : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ chartTargetEuclid (I := I) α) (μ : _root_.MeasureTheory.Measure (ℝ × EuclN)) :
    _root_.MeasureTheory.MemLp (fun p : ℝ × EuclN =>
      traceTimeDerivMetric (I := I) G.metric p.1
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm p.2))) ∞
      (μ.restrict (J ×ˢ Ω)) := by
  exact (traceTimeDerivMetric_comp_chartInverse_continuousOn hG hJ α).mono
    (_root_.Set.prod_mono Subset.rfl hΩs) |>.memLp_top_of_subset_isCompact
      (hJc.prod hΩc) (hJc.measurableSet.prod hΩm)
      (_root_.Set.prod_mono Subset.rfl subset_closure)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.traceTimeDerivMetric_comp_chartInverse_memLp_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.traceTimeDerivMetric_comp_chartInverse_memLp_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.traceTimeDerivMetric_comp_chartInverse_memLp_top ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.traceTimeDerivMetric_comp_chartInverse_memLp_top

end DifferentialGeometry.Analysis.Laplacian.MetricExtension
