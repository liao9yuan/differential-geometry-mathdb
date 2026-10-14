import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.DirichletForm.RotatedTestSection
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.InteriorRegularity.PrincipalForm
import Submission.DifferentialGeometry.Analysis.Elliptic.Operator.ChartMeasureEquiv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity


open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivPointwiseInner_integral_chart_pull
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M)
    (hS_support : tsupport S.toFun ⊆ (chartAt H α).source) :
    ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (covPrincipalIntegrand (I := I) (M := M) g r s S T α y +
            covLowerOrderIntegrand (I := I) (M := M) g r s S T α y)
        ∂(MeasureTheory.Measure.map (toEuclidean : E →
            EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
            (modelHaar (E := E))) := by
  classical
  have hcont : Continuous
      (tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T) :=
    tensorCovDerivPointwiseInner_continuous (I := I) (M := M) g r s S T
  have hsupp : tsupport
      (tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T) ⊆
      (chartAt H α).source :=
    (tensorCovDerivPointwiseInner_tsupport_subset_left
      (I := I) (M := M) g r s S T).trans hS_support
  rw [integral_riemannianVolumeMeasure_eq_euclidean_chartTarget
    (I := I) (M := M) g α hcont hsupp]
  have hctE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M)
      α).measurableSet
  refine _root_.MeasureTheory.setIntegral_congr_fun hctE_meas (fun y hy => ?_)
  rw [tensorCovDerivPointwiseInner_chart_eq (I := I) (M := M) g r s S T α hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorCovDerivPointwiseInner_integral_chart_pull then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorCovDerivPointwiseInner_integral_chart_pull"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorCovDerivPointwiseInner_integral_chart_pull ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.tensorCovDerivPointwiseInner_integral_chart_pull

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem chartPushedRaw_bump_contDiffOn
    (α : M) {χ : M → ℝ}
    (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source) :
    ContDiffOn ℝ ∞ (chartPushedRaw I α χ)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hχ_extsrc : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hχs
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hmaps : Set.MapsTo (extChartAt I α).symm (extChartAt I α).target
      (extChartAt I α).source := fun y hy => (extChartAt I α).map_target hy
  have hcomp_E : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (χ ∘ (extChartAt I α).symm) (extChartAt I α).target :=
    hχ_extsrc.comp hsymm hmaps
  have hcontDiff_E : ContDiffOn ℝ ∞
      (χ ∘ (extChartAt I α).symm) (extChartAt I α).target :=
    hcomp_E.contDiffOn
  have hcomp_eucl : ContDiffOn ℝ ∞
      ((χ ∘ (extChartAt I α).symm) ∘
        (toEuclidean.symm :
          EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E))
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine hcontDiff_E.comp ?_ ?_
    · exact (toEuclidean (E := E)).symm.contDiff.contDiffOn
    · intro y hy
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
  refine hcomp_eucl.congr (fun z hz => ?_)
  exact chartPushedRaw_apply_of_mem (I := I) (M := M) α χ hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartPushedRaw_bump_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartPushedRaw_bump_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartPushedRaw_bump_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartPushedRaw_bump_contDiffOn

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
lemma euclidPartial_mul
    (l : Fin (Module.finrank ℝ E))
    {f h : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hf : DifferentiableAt ℝ f y) (hh : DifferentiableAt ℝ h y) :
    euclidPartial (E := E) l (fun z => f z * h z) y =
      euclidPartial (E := E) l f y * h y + f y * euclidPartial (E := E) l h y := by
  rw [euclidPartial_def, euclidPartial_def, euclidPartial_def,
    fderiv_fun_mul hf hh]
  rw [add_apply, smul_apply,
    smul_apply, smul_eq_mul, smul_eq_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_mul ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_mul

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
    [SigmaCompactSpace M] in
private lemma euclidPartial_contDiffOn_chartTarget
    (α : M) (l : Fin (Module.finrank ℝ E))
    {u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (hu : ContDiffOn ℝ ∞ u (chartTargetEuclid (I := I) (M := M) α)) :
    ContDiffOn ℝ ∞ (euclidPartial (E := E) l u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
  have hfderiv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ u z)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have hsucc : ContDiffOn ℝ ((∞ : WithTop ℕ∞) + 1) u
        (chartTargetEuclid (I := I) (M := M) α) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl]; exact hu
    have hfw : ContDiffOn ℝ ∞ (fderivWithin ℝ u
        (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
      ((contDiffOn_succ_iff_fderivWithin hopen.uniqueDiffOn).mp hsucc).2.2
    refine hfw.congr (fun z hz => ?_)
    exact (fderivWithin_of_isOpen (f := u) (𝕜 := ℝ) hopen hz).symm
  have hcomp : ContDiffOn ℝ ∞
      ((fun L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] ℝ =>
          L (EuclideanSpace.single l 1)) ∘ (fun z => fderiv ℝ u z))
      (chartTargetEuclid (I := I) (M := M) α) :=
    (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single l 1)).contDiff.comp_contDiffOn hfderiv
  refine hcomp.congr (fun z _ => ?_)
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_contDiffOn_chartTarget
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_contDiffOn_chartTarget target :: scope.openDecls } }

noncomputable def gramInvEntry
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Q P₀ : CompIdx E r s) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y => covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.gramInvEntry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.gramInvEntry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.gramInvEntry ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.gramInvEntry

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma gramInvEntry_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Q P₀ : CompIdx E r s) :
    ContDiffOn ℝ ∞ (gramInvEntry (I := I) (M := M) g r s α Q P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
  covChartMetricGramInv_entry_contDiffOn (I := I) (M := M) g r s α Q P₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.gramInvEntry_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.gramInvEntry_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.gramInvEntry_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.gramInvEntry_contDiffOn

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartPushedRaw_rotatedTestSection_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r s) :
    Set.EqOn
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s
          (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
          α Q.1 Q.2))
      (fun y => gramInvEntry (I := I) (M := M) g r s α Q P₀ y *
        chartPushedRaw I α χ y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
  rw [rotatedTestSection_chartComp (I := I) (M := M) g r s α P₀ hχs hχt Q hy]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartPushedRaw_rotatedTestSection_eqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartPushedRaw_rotatedTestSection_eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartPushedRaw_rotatedTestSection_eqOn ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.chartPushedRaw_rotatedTestSection_eqOn

noncomputable def covPrincipalRotationRemainder
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    (χ : M → ℝ)
    :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    ∑ P : CompIdx E r s,
      ∑ Q : CompIdx E r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramEuclid (I := I) g α k l y *
                  euclidPartial (E := E) k
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M)
                        g r s S α P.1 P.2)) y *
                (euclidPartial (E := E) l
                    (gramInvEntry (I := I) (M := M) g r s α Q P₀) y *
                  chartPushedRaw I α χ y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covPrincipalRotationRemainder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covPrincipalRotationRemainder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covPrincipalRotationRemainder ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covPrincipalRotationRemainder

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma covPrincipalRotationRemainder_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ}
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    covPrincipalRotationRemainder (I := I) (M := M) g r s S α P₀ χ y =
      ∑ P : CompIdx E r s,
        ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramEuclid (I := I) g α k l y *
                    euclidPartial (E := E) k
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s S α P.1 P.2)) y *
                  (euclidPartial (E := E) l
                      (gramInvEntry (I := I) (M := M) g r s α Q P₀) y *
                    chartPushedRaw I α χ y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covPrincipalRotationRemainder_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covPrincipalRotationRemainder_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covPrincipalRotationRemainder_def ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covPrincipalRotationRemainder_def

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covPrincipalRotationRemainder_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source) :
    ContDiffOn ℝ ∞
      (covPrincipalRotationRemainder (I := I) (M := M) g r s S α P₀ χ)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hbump : ContDiffOn ℝ ∞ (chartPushedRaw I α χ)
      (chartTargetEuclid (I := I) (M := M) α) :=
    chartPushedRaw_bump_contDiffOn (I := I) (M := M) α hχs
  have hsummand : ∀ P Q : CompIdx E r s,
      ContDiffOn ℝ ∞
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramEuclid (I := I) g α k l y *
                    euclidPartial (E := E) k
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s S α P.1 P.2)) y *
                  (euclidPartial (E := E) l
                      (gramInvEntry (I := I) (M := M) g r s α Q P₀) y *
                    chartPushedRaw I α χ y))
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro P Q
    have hgram : ContDiffOn ℝ ∞
        (covChartMetricGram (I := I) (M := M) g r s α P Q)
        (chartTargetEuclid (I := I) (M := M) α) :=
      covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q
    have hSpartial : ∀ k : Fin (Module.finrank ℝ E),
        ContDiffOn ℝ ∞
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M)
                g r s S α P.1 P.2)))
          (chartTargetEuclid (I := I) (M := M) α) := fun k =>
      euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M)
        g r s S α k P.1 P.2
    have hGinvPartial : ∀ l : Fin (Module.finrank ℝ E),
        ContDiffOn ℝ ∞
          (euclidPartial (E := E) l
            (gramInvEntry (I := I) (M := M) g r s α Q P₀))
          (chartTargetEuclid (I := I) (M := M) α) := fun l =>
      euclidPartial_contDiffOn_chartTarget (I := I) (M := M) α l
        (gramInvEntry_contDiffOn (I := I) (M := M) g r s α Q P₀)
    have hinner : ∀ k l : Fin (Module.finrank ℝ E),
        ContDiffOn ℝ ∞
          (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            chartInvGramEuclid (I := I) g α k l y *
                euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M)
                      g r s S α P.1 P.2)) y *
              (euclidPartial (E := E) l
                  (gramInvEntry (I := I) (M := M) g r s α Q P₀) y *
                chartPushedRaw I α χ y))
          (chartTargetEuclid (I := I) (M := M) α) := by
      intro k l
      have hGinv : ContDiffOn ℝ ∞ (chartInvGramEuclid (I := I) g α k l)
          (chartTargetEuclid (I := I) (M := M) α) :=
        chartInvGramEuclid_contDiffOn (I := I) (M := M) g α k l
      exact ((hGinv.mul (hSpartial k)).mul
        ((hGinvPartial l).mul hbump))
    have hklsum : ContDiffOn ℝ ∞
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramEuclid (I := I) g α k l y *
                  euclidPartial (E := E) k
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M)
                        g r s S α P.1 P.2)) y *
                (euclidPartial (E := E) l
                    (gramInvEntry (I := I) (M := M) g r s α Q P₀) y *
                  chartPushedRaw I α χ y))
        (chartTargetEuclid (I := I) (M := M) α) :=
      ContDiffOn.sum (fun k _ => ContDiffOn.sum (fun l _ => hinner k l))
    exact hgram.mul hklsum
  have hsum : ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        ∑ P : CompIdx E r s,
          ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramEuclid (I := I) g α k l y *
                      euclidPartial (E := E) k
                        (chartPushedRaw I α
                          (tensorChartComponentRaw (I := I) (M := M)
                            g r s S α P.1 P.2)) y *
                    (euclidPartial (E := E) l
                        (gramInvEntry (I := I) (M := M) g r s α Q P₀) y *
                      chartPushedRaw I α χ y))
      (chartTargetEuclid (I := I) (M := M) α) :=
    ContDiffOn.sum (fun P _ => ContDiffOn.sum (fun Q _ => hsummand P Q))
  exact hsum

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covPrincipalRotationRemainder_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covPrincipalRotationRemainder_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covPrincipalRotationRemainder_contDiffOn ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covPrincipalRotationRemainder_contDiffOn

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma euclidPartial_chartPushedRaw_rotatedTestSection_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r s) (l : Fin (Module.finrank ℝ E)) :
    Set.EqOn
      (euclidPartial (E := E) l
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s
            (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
            α Q.1 Q.2)))
      (fun y =>
        euclidPartial (E := E) l
            (gramInvEntry (I := I) (M := M) g r s α Q P₀) y *
          chartPushedRaw I α χ y +
        gramInvEntry (I := I) (M := M) g r s α Q P₀ y *
          euclidPartial (E := E) l (chartPushedRaw I α χ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
  have hGinv : ContDiffOn ℝ ∞ (gramInvEntry (I := I) (M := M) g r s α Q P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
    gramInvEntry_contDiffOn (I := I) (M := M) g r s α Q P₀
  have hbump : ContDiffOn ℝ ∞ (chartPushedRaw I α χ)
      (chartTargetEuclid (I := I) (M := M) α) :=
    chartPushedRaw_bump_contDiffOn (I := I) (M := M) α hχs
  have heqOn := chartPushedRaw_rotatedTestSection_eqOn (I := I) (M := M)
    g r s α P₀ hχs hχt Q
  intro y hy
  have hpartial_eq : euclidPartial (E := E) l
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s
            (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
            α Q.1 Q.2)) y =
      euclidPartial (E := E) l
        (fun z => gramInvEntry (I := I) (M := M) g r s α Q P₀ z *
          chartPushedRaw I α χ z) y := by
    rw [euclidPartial_def, euclidPartial_def]
    have hfderiv_eq :=
      Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (x := y)
        (Filter.eventuallyEq_of_mem (hopen.mem_nhds hy) heqOn)
    rw [hfderiv_eq]
  rw [hpartial_eq]
  have hGinv_diff : DifferentiableAt ℝ
      (gramInvEntry (I := I) (M := M) g r s α Q P₀) y :=
    (hGinv.differentiableOn (by simp)).differentiableAt
      (hopen.mem_nhds hy)
  have hbump_diff : DifferentiableAt ℝ (chartPushedRaw I α χ) y :=
    (hbump.differentiableOn (by simp)).differentiableAt
      (hopen.mem_nhds hy)
  exact euclidPartial_mul (E := E) l hGinv_diff hbump_diff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_chartPushedRaw_rotatedTestSection_eqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_chartPushedRaw_rotatedTestSection_eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_chartPushedRaw_rotatedTestSection_eqOn ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.euclidPartial_chartPushedRaw_rotatedTestSection_eqOn

omit [CompleteSpace E] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covPrincipalIntegrand_rotated_collapse
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    covPrincipalIntegrand (I := I) (M := M) g r s S
        (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt) α y =
      (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramEuclid (I := I) g α k l y *
              euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M)
                    g r s S α P₀.1 P₀.2)) y *
            euclidPartial (E := E) l (chartPushedRaw I α χ) y) +
        covPrincipalRotationRemainder (I := I) (M := M) g r s S α P₀ χ y := by
  classical
  rw [covPrincipalIntegrand_def, covPrincipalRotationRemainder_def]
  have hleibniz : ∀ Q : CompIdx E r s, ∀ l : Fin (Module.finrank ℝ E),
      euclidPartial (E := E) l
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s
              (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)
              α Q.1 Q.2)) y =
        euclidPartial (E := E) l
            (gramInvEntry (I := I) (M := M) g r s α Q P₀) y *
          chartPushedRaw I α χ y +
        gramInvEntry (I := I) (M := M) g r s α Q P₀ y *
          euclidPartial (E := E) l (chartPushedRaw I α χ) y := fun Q l =>
    euclidPartial_chartPushedRaw_rotatedTestSection_eqOn (I := I) (M := M)
      g r s α P₀ hχs hχt Q l hy
  set bumpSum :
      (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) → ℝ :=
    fun P =>
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramEuclid (I := I) g α k l y *
              euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M)
                    g r s S α P.1 P.2)) y *
            euclidPartial (E := E) l (chartPushedRaw I α χ) y with hbumpSum_def
  set remSum :
      (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) →
      (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) → ℝ :=
    fun P Q =>
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramEuclid (I := I) g α k l y *
              euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M)
                    g r s S α P.1 P.2)) y *
            (euclidPartial (E := E) l
                (gramInvEntry (I := I) (M := M) g r s α Q P₀) y *
              chartPushedRaw I α χ y) with hremSum_def
  have hLHS :
      (∑ P : CompIdx E r s,
        ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramEuclid (I := I) g α k l y *
                    euclidPartial (E := E) k
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s S α P.1 P.2)) y *
                  euclidPartial (E := E) l
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M) g r s
                        (rotatedTestSection (I := I) (M := M) g r s α P₀
                          χ hχs hχt)
                        α Q.1 Q.2)) y) =
        (∑ P : CompIdx E r s,
          ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              gramInvEntry (I := I) (M := M) g r s α Q P₀ y * bumpSum P) +
        ∑ P : CompIdx E r s,
          ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y * remSum P Q := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    have hinner :
        (∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramEuclid (I := I) g α k l y *
                euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M)
                      g r s S α P.1 P.2)) y *
              euclidPartial (E := E) l
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s
                    (rotatedTestSection (I := I) (M := M) g r s α P₀
                      χ hχs hχt)
                    α Q.1 Q.2)) y) =
          gramInvEntry (I := I) (M := M) g r s α Q P₀ y * bumpSum P +
            remSum P Q := by
      rw [hbumpSum_def, hremSum_def, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [hleibniz Q l]
      ring
    rw [hinner, mul_add]
    ring
  rw [hLHS]
  have hcollapse : ∀ P : CompIdx E r s,
      (∑ Q : CompIdx E r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          gramInvEntry (I := I) (M := M) g r s α Q P₀ y * bumpSum P) =
        (if P = P₀ then (1 : ℝ) else 0) * bumpSum P := by
    intro P
    rw [← Finset.sum_mul]
    congr 1
    have hrw : ∀ Q : CompIdx E r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
            gramInvEntry (I := I) (M := M) g r s α Q P₀ y =
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀ := fun Q => rfl
    rw [Finset.sum_congr rfl (fun Q _ => hrw Q)]
    exact covChartMetricGram_mul_inv_collapse (I := I) (M := M) g r s α hy P P₀
  have hbump_collapse :
      (∑ P : CompIdx E r s,
        ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            gramInvEntry (I := I) (M := M) g r s α Q P₀ y * bumpSum P) =
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramEuclid (I := I) g α k l y *
                euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M)
                      g r s S α P₀.1 P₀.2)) y *
              euclidPartial (E := E) l (chartPushedRaw I α χ) y := by
    rw [Finset.sum_congr rfl (fun P _ => hcollapse P)]
    rw [Finset.sum_eq_single P₀]
    · rw [if_pos rfl, one_mul, hbumpSum_def]
    · intro P _ hP
      rw [if_neg hP, _root_.MulZeroClass.zero_mul]
    · intro hP₀
      exact absurd (Finset.mem_univ P₀) hP₀
  rw [hbump_collapse]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covPrincipalIntegrand_rotated_collapse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covPrincipalIntegrand_rotated_collapse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covPrincipalIntegrand_rotated_collapse ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.covPrincipalIntegrand_rotated_collapse

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma weightedInvGramEuclid_eq_density_mul_invGram
    (g : SmoothRiemannianMetric I M) (α : M)
    (k l : Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    weightedInvGramEuclid (I := I) g α k l y =
      densityOnEuclid (I := I) g α y *
        chartInvGramEuclid (I := I) g α k l y :=
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.weightedInvGramEuclid_eq_density_mul_invGram
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.weightedInvGramEuclid_eq_density_mul_invGram target :: scope.openDecls } }

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
theorem weightedInvGram_principalIntegrand_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
    (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (u φ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))} (hy : y ∈ K) :
    densityOnEuclid (I := I) g α y *
        (∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramEuclid (I := I) g α k l y *
              euclidPartial (E := E) k u y *
              euclidPartial (E := E) l φ y) =
      (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
        u φ y := by
  classical
  rw [SmoothEllipticBilinearForm.principalIntegrand, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [tensorPrincipalForm_a_eq_weightedInvGramEuclid
    (I := I) (M := M) g α hK hK_target hy k l]
  rw [weightedInvGramEuclid_eq_density_mul_invGram (I := I) (M := M) g α k l y,
    euclidPartial_def, euclidPartial_def]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.weightedInvGram_principalIntegrand_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TensorRegularity.weightedInvGram_principalIntegrand_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TensorRegularity.weightedInvGram_principalIntegrand_eq ``Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity.weightedInvGram_principalIntegrand_eq

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
