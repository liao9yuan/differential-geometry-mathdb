import Submission.DifferentialGeometry.Analysis.Parabolic.WeakEquation.GaussianCoordinates
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.WeightedSpatialLp
import Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficients
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Formula

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold

namespace DifferentialGeometry.Analysis.Parabolic

open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.instBorelSpace_differentialGeometry target :: scope.openDecls } }

local notation "V" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private theorem chartGradientBilin_fderiv_toEuclidean
    (g : SmoothRiemannianMetric I M) (α : M) (f : E → ℝ) (φ : V → ℝ) (y : E) :
    chartGradientBilin g α ((extChartAt I α).symm y)
      (fderiv ℝ f y) (fderiv ℝ (φ ∘ toEuclidean (E := E)) y) =
        ∑ i, ∑ j, invGramOnEuclid g α i j ((toEuclidean (E := E)) y) *
          fderiv ℝ (f ∘ (toEuclidean (E := E)).symm) ((toEuclidean (E := E)) y)
            (EuclideanSpace.single j 1) *
          fderiv ℝ φ ((toEuclidean (E := E)) y) (EuclideanSpace.single i 1) := by
  have hf (j : Fin (Module.finrank ℝ E)) :
      fderiv ℝ (f ∘ (toEuclidean (E := E)).symm) ((toEuclidean (E := E)) y)
          (EuclideanSpace.single j 1) = fderiv ℝ f y (chartModelBasis E j) := by
    rw [(toEuclidean (E := E)).symm.comp_right_fderiv]
    simp only [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, chartModelBasis_apply]
  have hφ (i : Fin (Module.finrank ℝ E)) :
      fderiv ℝ (φ ∘ toEuclidean (E := E)) y (chartModelBasis E i) =
        fderiv ℝ φ ((toEuclidean (E := E)) y) (EuclideanSpace.single i 1) := by
    rw [(toEuclidean (E := E)).comp_right_fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      chartModelBasis_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [chartGradientBilin_apply]
  simp only [hf, hφ, invGramOnEuclid, ContinuousLinearEquiv.symm_apply_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.chartGradientBilin_fderiv_toEuclidean
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.chartGradientBilin_fderiv_toEuclidean target :: scope.openDecls } }

private theorem integrable_toEuclidean_chartGaussianResidual
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn (I := I) D g) (α : M)
    {a b : ℝ} (hreg : _root_.Set.Icc a b ⊆ D.regular)
    {Ω : Set V} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩt : closure Ω ⊆ chartTargetEuclid (I := I) α)
    {f u : ℝ × E → ℝ}
    (hf : LocallyLipschitzOn (_root_.Set.Icc a b ×ˢ closure Ω)
      (fun q : ℝ × V => f (q.1, (toEuclidean (E := E)).symm q.2)))
    (hu : LocallyLipschitzOn (_root_.Set.Icc a b ×ˢ closure Ω)
      (fun q : ℝ × V => u (q.1, (toEuclidean (E := E)).symm q.2)))
    {φ : ℝ × V → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Integrable (fun q : ℝ × V => densityOnEuclid (I := I) (g q.1) α q.2 *
      u (q.1, (toEuclidean (E := E)).symm q.2) *
      (fderiv ℝ φ q (1, 0) +
        ∑ i, ∑ j, invGramOnEuclid (I := I) (g q.1) α i j q.2 *
          fderiv ℝ (fun y => f (q.1, (toEuclidean (E := E)).symm y)) q.2
            (EuclideanSpace.single j 1) *
          fderiv ℝ φ q (0, EuclideanSpace.single i 1)))
      ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) := by
  let G : MetricConnectionFamilyOn (I := I) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  have hρ : ContinuousOn (fun q : ℝ × V => densityOnEuclid (I := I) (g q.1) α q.2)
      (_root_.Set.Icc a b ×ˢ closure Ω) :=
    (densityOnEuclid_family_continuousOn (G := G) hg hreg α).mono
      (_root_.Set.prod_mono Subset.rfl hΩt)
  have hA (i j : Fin (Module.finrank ℝ E)) :
      ContinuousOn (fun q : ℝ × V => invGramOnEuclid (I := I) (g q.1) α i j q.2)
        (_root_.Set.Icc a b ×ˢ closure Ω) :=
    (invGramOnEuclid_family_continuousOn (G := G) hg hreg α i j).mono
      (_root_.Set.prod_mono Subset.rfl hΩt)
  have htime : _root_.MeasureTheory.Integrable
      (fun q : ℝ × V => densityOnEuclid (I := I) (g q.1) α q.2 *
        u (q.1, (toEuclidean (E := E)).symm q.2) * fderiv ℝ φ q (1, 0))
      ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) := by
    have htest : ContinuousOn (fun q : ℝ × V => fderiv ℝ φ q (1, 0))
        (_root_.Set.Icc a b ×ˢ closure Ω) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const |>.continuousOn
    have hc : ContinuousOn
        (fun q : ℝ × V => densityOnEuclid (I := I) (g q.1) α q.2 *
          u (q.1, (toEuclidean (E := E)).symm q.2) * fderiv ℝ φ q (1, 0))
        (_root_.Set.Icc a b ×ˢ closure Ω) :=
      (hρ.mul hu.continuousOn).mul htest
    rw [Measure.prod_restrict]
    exact (hc.integrableOn_compact (isCompact_Icc.prod hΩc)).mono_set
      (_root_.Set.prod_mono Subset.rfl subset_closure)
  have hterm (i j : Fin (Module.finrank ℝ E)) : _root_.MeasureTheory.Integrable
      (fun q : ℝ × V => densityOnEuclid (I := I) (g q.1) α q.2 *
        u (q.1, (toEuclidean (E := E)).symm q.2) *
        invGramOnEuclid (I := I) (g q.1) α i j q.2 *
        fderiv ℝ (fun y => f (q.1, (toEuclidean (E := E)).symm y)) q.2
          (EuclideanSpace.single j 1) *
        fderiv ℝ φ q (0, EuclideanSpace.single i 1))
      ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) := by
    have hdf : _root_.MeasureTheory.MemLp
        (fun q : ℝ × V => fderiv ℝ (fun y => f (q.1, (toEuclidean (E := E)).symm y)) q.2
          (EuclideanSpace.single j 1)) 1
        ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) :=
      memLp_spatial_fderiv_of_locallyLipschitzOn hΩ hΩc hf 1 j
    have htest : ContinuousOn
        (fun q : ℝ × V => fderiv ℝ φ q (0, EuclideanSpace.single i 1))
        (_root_.Set.Icc a b ×ˢ closure Ω) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const |>.continuousOn
    have hc : ContinuousOn
        (fun q : ℝ × V => densityOnEuclid (I := I) (g q.1) α q.2 *
          u (q.1, (toEuclidean (E := E)).symm q.2) *
          invGramOnEuclid (I := I) (g q.1) α i j q.2 *
          fderiv ℝ φ q (0, EuclideanSpace.single i 1))
        (_root_.Set.Icc a b ×ˢ closure Ω) :=
      ((hρ.mul hu.continuousOn).mul (hA i j)).mul htest
    have hcMem : _root_.MeasureTheory.MemLp
        (fun q : ℝ × V => densityOnEuclid (I := I) (g q.1) α q.2 *
          u (q.1, (toEuclidean (E := E)).symm q.2) *
          invGramOnEuclid (I := I) (g q.1) α i j q.2 *
          fderiv ℝ φ q (0, EuclideanSpace.single i 1)) ∞
        ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) := by
      rw [Measure.prod_restrict]
      exact (hc.memLp_top_of_subset_isCompact (isCompact_Icc.prod hΩc)
        (measurableSet_Icc.prod hΩ.measurableSet) (_root_.Set.prod_mono Subset.rfl subset_closure))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      memLp_one_iff_integrable.mp (hdf.mul' (r := 1) hcMem)
  have hgrad : _root_.MeasureTheory.Integrable
      (fun q : ℝ × V => densityOnEuclid (I := I) (g q.1) α q.2 *
        u (q.1, (toEuclidean (E := E)).symm q.2) *
        (∑ i, ∑ j, invGramOnEuclid (I := I) (g q.1) α i j q.2 *
          fderiv ℝ (fun y => f (q.1, (toEuclidean (E := E)).symm y)) q.2
            (EuclideanSpace.single j 1) *
          fderiv ℝ φ q (0, EuclideanSpace.single i 1)))
      ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) := by
    have hs : _root_.MeasureTheory.Integrable
        (fun q : ℝ × V => ∑ i, ∑ j, densityOnEuclid (I := I) (g q.1) α q.2 *
          u (q.1, (toEuclidean (E := E)).symm q.2) *
          (invGramOnEuclid (I := I) (g q.1) α i j q.2 *
            fderiv ℝ (fun y => f (q.1, (toEuclidean (E := E)).symm y)) q.2
              (EuclideanSpace.single j 1) *
            fderiv ℝ φ q (0, EuclideanSpace.single i 1)))
        ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) := by
      apply _root_.MeasureTheory.integrable_finsetSum Finset.univ
      intro i _
      apply _root_.MeasureTheory.integrable_finsetSum Finset.univ
      intro j _
      simpa only [mul_assoc] using hterm i j
    convert hs using 1
    funext q
    simp only [Finset.mul_sum, mul_assoc]
  convert htime.add hgrad using 1 <;>
    first | rfl | (funext q; simp only [Pi.add_apply, mul_add])

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.integrable_toEuclidean_chartGaussianResidual
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.integrable_toEuclidean_chartGaussianResidual target :: scope.openDecls } }

theorem integrable_chartGaussianResidual_of_locallyLipschitzOn
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn (I := I) D g) (α : M)
    {a b : ℝ} (hreg : _root_.Set.Icc a b ⊆ D.regular)
    {Ω : Set V} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩt : closure Ω ⊆ chartTargetEuclid (I := I) α)
    {f u : ℝ × E → ℝ}
    (hf : LocallyLipschitzOn (_root_.Set.Icc a b ×ˢ closure Ω)
      (fun q : ℝ × V => f (q.1, (toEuclidean (E := E)).symm q.2)))
    (hu : LocallyLipschitzOn (_root_.Set.Icc a b ×ˢ closure Ω)
      (fun q : ℝ × V => u (q.1, (toEuclidean (E := E)).symm q.2)))
    {φ : ℝ × V → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Integrable (fun z : ℝ × E => chartDensity (I := I) (g z.1) α
        ((extChartAt I α).symm z.2) * u z *
      (deriv (fun t => φ (t, (toEuclidean (E := E)) z.2)) z.1 +
        chartGradientBilin (I := I) (g z.1) α ((extChartAt I α).symm z.2)
          (fderiv ℝ (fun y => f (z.1, y)) z.2)
          (fderiv ℝ (fun y => φ (z.1, (toEuclidean (E := E)) y)) z.2)))
      ((volume.restrict (_root_.Set.Ioc a b)).prod
        ((modelHaar (E := E)).restrict ((toEuclidean (E := E)) ⁻¹' Ω))) := by
  rw [Measure.restrict_congr_set _root_.MeasureTheory.Ioc_ae_eq_Icc]
  let T : (ℝ × E) ≃L[ℝ] (ℝ × V) :=
    (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (toEuclidean (E := E))
  have hspace : _root_.MeasureTheory.MeasurePreserving (toEuclidean (E := E))
      (modelHaar (E := E)) volume :=
    ⟨(toEuclidean (E := E)).continuous.measurable, map_toEuclidean_modelHaar_eq_volume⟩
  have hspaceR := hspace.restrict_preimage_emb
    (toEuclidean (E := E)).toHomeomorph.measurableEmbedding Ω
  have hT : _root_.MeasureTheory.MeasurePreserving T
      ((volume.restrict (_root_.Set.Icc a b)).prod
        ((modelHaar (E := E)).restrict ((toEuclidean (E := E)) ⁻¹' Ω)))
      ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) :=
    (MeasurePreserving.id (volume.restrict (_root_.Set.Icc a b))).prod hspaceR
  let R : ℝ × V → ℝ := fun q => densityOnEuclid (I := I) (g q.1) α q.2 *
    u (q.1, (toEuclidean (E := E)).symm q.2) *
    (fderiv ℝ φ q (1, 0) +
      ∑ i, ∑ j, invGramOnEuclid (I := I) (g q.1) α i j q.2 *
        fderiv ℝ (fun y => f (q.1, (toEuclidean (E := E)).symm y)) q.2
          (EuclideanSpace.single j 1) *
        fderiv ℝ φ q (0, EuclideanSpace.single i 1))
  have hRV : _root_.MeasureTheory.Integrable R ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) :=
    integrable_toEuclidean_chartGaussianResidual D g hg α hreg hΩ hΩc hΩt hf hu hφ
  have hRT : _root_.MeasureTheory.Integrable (R ∘ T)
      ((volume.restrict (_root_.Set.Icc a b)).prod
        ((modelHaar (E := E)).restrict ((toEuclidean (E := E)) ⁻¹' Ω))) :=
    (hT.integrable_comp_emb T.toHomeomorph.measurableEmbedding).mpr hRV
  apply hRT.congr
  apply Filter.Eventually.of_forall
  intro z
  have hd := hφ.differentiable (by simp) (z.1, (toEuclidean (E := E)) z.2)
  have ht : deriv (fun t => φ (t, (toEuclidean (E := E)) z.2)) z.1 =
      fderiv ℝ φ (z.1, (toEuclidean (E := E)) z.2) (1, 0) := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply] using
      (hd.hasFDerivAt.comp z.1
        (hasFDerivAt_prodMk_left z.1 ((toEuclidean (E := E)) z.2))).hasDerivAt.deriv
  have hs (i : Fin (Module.finrank ℝ E)) :
      fderiv ℝ (fun y : V => φ (z.1, y)) ((toEuclidean (E := E)) z.2)
          (EuclideanSpace.single i 1) =
        fderiv ℝ φ (z.1, (toEuclidean (E := E)) z.2)
          (0, EuclideanSpace.single i 1) := by
    have heq : fderiv ℝ (fun y : V => φ (z.1, y)) ((toEuclidean (E := E)) z.2) =
        (fderiv ℝ φ (z.1, (toEuclidean (E := E)) z.2)).comp
          (ContinuousLinearMap.inr ℝ ℝ V) :=
      (hd.hasFDerivAt.comp ((toEuclidean (E := E)) z.2)
        (hasFDerivAt_prodMk_right z.1 ((toEuclidean (E := E)) z.2))).fderiv
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using
      congrArg (fun L : V →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) heq
  have hgrad := chartGradientBilin_fderiv_toEuclidean (g z.1) α
    (fun y => f (z.1, y)) (fun y : V => φ (z.1, y)) z.2
  simpa only [R, T, Function.comp_def, ContinuousLinearEquiv.prodCongr_apply,
    ContinuousLinearEquiv.refl_apply, densityOnEuclid,
    ContinuousLinearEquiv.symm_apply_apply, ht, hs] using
      (congrArg (fun r => chartDensity (g z.1) α ((extChartAt I α).symm z.2) * u z *
        (fderiv ℝ φ (z.1, (toEuclidean (E := E)) z.2) (1, 0) + r)) hgrad).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.integrable_chartGaussianResidual_of_locallyLipschitzOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.integrable_chartGaussianResidual_of_locallyLipschitzOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.integrable_chartGaussianResidual_of_locallyLipschitzOn ``Submission.DifferentialGeometry.Analysis.Parabolic.integrable_chartGaussianResidual_of_locallyLipschitzOn

end DifferentialGeometry.Analysis.Parabolic
