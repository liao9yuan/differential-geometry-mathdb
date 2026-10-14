import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.ChartL2Convergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix _root_.ENNReal _root_.NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral


open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompactSpace M] in
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartPushedRaw_tensorChartComponentRaw_pouSmul_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α S) α Idx Jdx) =
      tensorChartComponent (I := I) (M := M) g r s S α Idx Jdx := by
  rw [tensorChartComponentRaw_pouSmul_eq_tensorChartComponentPou
    (I := I) (M := M) g r s α S Idx Jdx, tensorChartComponent_def]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_tensorChartComponentRaw_pouSmul_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_tensorChartComponentRaw_pouSmul_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_tensorChartComponentRaw_pouSmul_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPushedRaw_tensorChartComponentRaw_pouSmul_eq

def principalRotationFactor
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (P Q : TensorCompIdx (E := E) r s)
    (k l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    covChartMetricGram (I := I) (M := M) g r s α P Q y *
        chartInvGramEuclid (I := I) g α k l y *
      euclidPartial (E := E) l (gramInvEntry (I := I) (M := M) g r s α Q P₀) y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.principalRotationFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.principalRotationFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.principalRotationFactor ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.principalRotationFactor

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma principalRotationFactor_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ P Q : TensorCompIdx (E := E) r s)
    (k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (principalRotationFactor (I := I) (M := M) g r s α P₀ P Q k l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
      (chartInvGramEuclid_contDiffOn (I := I) g α k l)).mul
    (euclidPartial_contDiffOn_target (I := I) (M := M) α l
      (gramInvEntry_contDiffOn (I := I) (M := M) g r s α Q P₀))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.principalRotationFactor_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.principalRotationFactor_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.principalRotationFactor_contDiffOn ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.principalRotationFactor_contDiffOn

omit [CompactSpace M] in
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma covDerivLowerOrderTerm_pouSmul_eqOn_coeffFactors
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    covDerivLowerOrderTerm (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α m Idx Jdx y =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
          tensorChartComponent (I := I) (M := M) g r s S α p.1 p.2 y := by
  classical
  rw [covDerivLowerOrderTerm_def]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [tensorChartComponentRaw_pouSmul_eq_tensorChartComponentPou
    (I := I) (M := M) g r s α S p.1 p.2,
    tensorChartComponent_def,
    chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (tensorChartComponentPou (I := I) (M := M) g r s S α p.1 p.2) hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivLowerOrderTerm_pouSmul_eqOn_coeffFactors then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivLowerOrderTerm_pouSmul_eqOn_coeffFactors"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivLowerOrderTerm_pouSmul_eqOn_coeffFactors ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covDerivLowerOrderTerm_pouSmul_eqOn_coeffFactors

def weightedGradFactor
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    (P Q : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    (p : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    densityOnEuclid (I := I) g α y *
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          chartInvGramEuclid (I := I) g α k l y *
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α k P.1 p.1 P.2 p.2 y *
      covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradFactor ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradFactor

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M]
    [SigmaCompactSpace M] in
lemma weightedGradFactor_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    (P Q : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    (p : TensorCompIdx (E := E) r s) :
    ContDiffOn ℝ ∞ (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p)
      (chartTargetEuclid (I := I) (M := M) α) :=
  ((((densityOnEuclid_contDiffOn (I := I) g α).mul
        (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q)).mul
      (chartInvGramEuclid_contDiffOn (I := I) g α k l)).mul
    (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
      g r s α k P.1 p.1 P.2 p.2)).mul
    (covChartMetricGramInv_entry_contDiffOn (I := I) (M := M) g r s α Q P₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradFactor_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradFactor_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradFactor_contDiffOn ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradFactor_contDiffOn

omit [CompactSpace M] in
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma weightedGradCoeff_pouSmul_eqOn_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) (S : SmoothCcTensor g r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    weightedGradCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α P₀ l y =
      ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p y *
                tensorChartComponent (I := I) (M := M) g r s
                  S α p.1 p.2 y := by
  classical
  simp only [weightedGradCoeff, covLowerOrderRotationGradCoeff_def]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [covDerivLowerOrderTerm_pouSmul_eqOn_coeffFactors (I := I) (M := M) g r s α
    S k P.1 P.2 hy]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [weightedGradFactor]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeff_pouSmul_eqOn_section
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeff_pouSmul_eqOn_section target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
lemma euclidPartial_weightedGradCoeff_pouSmul_eqOn_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) (S : SmoothCcTensor g r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    euclidPartial (E := E) l
        (weightedGradCoeff (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α S) α P₀ l) y =
      (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                euclidPartial (E := E) l
                    (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
                  tensorChartComponent (I := I) (M := M) g r s
                    S α p.1 p.2 y)
        + ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p y *
                    euclidPartial (E := E) l
                      (tensorChartComponent (I := I) (M := M) g r s
                        S α p.1 p.2) y := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  set wₙ : SmoothCcTensor g r s := S with hwₙ_def
  set Sum4 : EuclN → ℝ := fun z =>
    ∑ P : TensorCompIdx (E := E) r s,
      ∑ Q : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ p : TensorCompIdx (E := E) r s,
            weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p z *
              tensorChartComponent (I := I) (M := M) g r s wₙ α p.1 p.2 z
    with hSum4_def
  have hcoeff_evt :
      weightedGradCoeff (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α wₙ) α P₀ l =ᶠ[𝓝 y] Sum4 := by
    refine Filter.eventually_of_mem (hopen.mem_nhds hy) (fun z hz => ?_)
    rw [hSum4_def]
    exact weightedGradCoeff_pouSmul_eqOn_section (I := I) (M := M)
      g r s α P₀ l wₙ hz
  rw [euclidPartial_def, hcoeff_evt.fderiv_eq, ← euclidPartial_def]
  have hleaf_diff : ∀ P Q : TensorCompIdx (E := E) r s,
      ∀ k : Fin (Module.finrank ℝ E), ∀ p : TensorCompIdx (E := E) r s,
      DifferentiableAt ℝ
        (fun z => weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p z *
          tensorChartComponent (I := I) (M := M) g r s wₙ α p.1 p.2 z) y :=
    fun P Q k p =>
      (differentiableAt_of_contDiffOn_chartTarget (I := I) (M := M) α
        (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p)
        hy).mul
      (differentiableAt_tensorChartComponent (I := I) (M := M) g r s wₙ α
        p.1 p.2 y)
  rw [hSum4_def, euclidPartial_finsetSum (E := E) l Finset.univ
    (fun P _ => DifferentiableAt.fun_sum (fun Q _ =>
      DifferentiableAt.fun_sum (fun k _ =>
        DifferentiableAt.fun_sum (fun p _ => hleaf_diff P Q k p))))]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [euclidPartial_finsetSum (E := E) l Finset.univ
    (fun Q _ => DifferentiableAt.fun_sum (fun k _ =>
      DifferentiableAt.fun_sum (fun p _ => hleaf_diff P Q k p)))]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [euclidPartial_finsetSum (E := E) l Finset.univ
    (fun k _ => DifferentiableAt.fun_sum (fun p _ => hleaf_diff P Q k p))]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [euclidPartial_finsetSum (E := E) l Finset.univ
    (fun p _ => hleaf_diff P Q k p)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  exact euclidPartial_mul (E := E) l
    (differentiableAt_of_contDiffOn_chartTarget (I := I) (M := M) α
      (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p) hy)
    (differentiableAt_tensorChartComponent (I := I) (M := M) g r s wₙ α
      p.1 p.2 y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_weightedGradCoeff_pouSmul_eqOn_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_weightedGradCoeff_pouSmul_eqOn_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_weightedGradCoeff_pouSmul_eqOn_section ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_weightedGradCoeff_pouSmul_eqOn_section

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M]
    [SigmaCompactSpace M] in
lemma euclidPartial_weightedGradFactor_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    (P Q : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    (p : TensorCompIdx (E := E) r s) :
    ContDiffOn ℝ ∞
      (euclidPartial (E := E) l
        (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p))
      (chartTargetEuclid (I := I) (M := M) α) :=
  euclidPartial_contDiffOn_target (I := I) (M := M) α l
    (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_weightedGradFactor_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_weightedGradFactor_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_weightedGradFactor_contDiffOn ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.euclidPartial_weightedGradFactor_contDiffOn

def valuePartialFactor
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (P Q : TensorCompIdx (E := E) r s)
    (k l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    covChartMetricGram (I := I) (M := M) g r s α P Q y *
        chartInvGramEuclid (I := I) g α k l y *
      lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.valuePartialFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.valuePartialFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.valuePartialFactor ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.valuePartialFactor

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma valuePartialFactor_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ P Q : TensorCompIdx (E := E) r s)
    (k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
      (chartInvGramEuclid_contDiffOn (I := I) g α k l)).mul
    (lowerOrderRotationLOCoeff_contDiffOn (I := I) (M := M) g r s α P₀ l Q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.valuePartialFactor_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.valuePartialFactor_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.valuePartialFactor_contDiffOn ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.valuePartialFactor_contDiffOn

def valueComponentFactor
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (P Q : TensorCompIdx (E := E) r s)
    (k l : Fin (Module.finrank ℝ E))
    (p : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    covChartMetricGram (I := I) (M := M) g r s α P Q y *
          chartInvGramEuclid (I := I) g α k l y *
        (euclidPartial (E := E) l
              (gramInvEntry (I := I) (M := M) g r s α Q P₀) y +
            lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y) *
      covDerivLowerOrderCoeff (I := I) (M := M) g r s α k P.1 p.1 P.2 p.2 y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.valueComponentFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.valueComponentFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.valueComponentFactor ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.valueComponentFactor

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma valueComponentFactor_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ P Q : TensorCompIdx (E := E) r s)
    (k l : Fin (Module.finrank ℝ E))
    (p : TensorCompIdx (E := E) r s) :
    ContDiffOn ℝ ∞ (valueComponentFactor (I := I) (M := M) g r s α P₀ P Q k l p)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
        (chartInvGramEuclid_contDiffOn (I := I) g α k l)).mul
      ((euclidPartial_contDiffOn_target (I := I) (M := M) α l
          (gramInvEntry_contDiffOn (I := I) (M := M) g r s α Q P₀)).add
        (lowerOrderRotationLOCoeff_contDiffOn (I := I) (M := M)
          g r s α P₀ l Q))).mul
    (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M) g r s α k P.1 p.1 P.2 p.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.valueComponentFactor_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.valueComponentFactor_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.valueComponentFactor_contDiffOn ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.valueComponentFactor_contDiffOn

omit [CompactSpace M] in
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma covLowerOrderRotationValueCoeff_pouSmul_eqOn_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (S : SmoothCcTensor g r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α P₀ y =
      (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l y *
                  euclidPartial (E := E) k
                    (tensorChartComponent (I := I) (M := M) g r s
                      S α P.1 P.2) y)
        + ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ∑ p : TensorCompIdx (E := E) r s,
                    valueComponentFactor (I := I) (M := M)
                        g r s α P₀ P Q k l p y *
                      tensorChartComponent (I := I) (M := M) g r s
                        S α p.1 p.2 y := by
  classical
  set wₙ : SmoothCcTensor g r s := S with hwₙ_def
  rw [covLowerOrderRotationValueCoeff_def]
  have hbody : ∀ P Q : TensorCompIdx (E := E) r s,
      ∀ k l : Fin (Module.finrank ℝ E),
      chartInvGramEuclid (I := I) g α k l y *
          (euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M)
                    g r s (pouSmul (I := I) (M := M) g r s α wₙ) α P.1 P.2)) y *
              lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y
            + covDerivLowerOrderTerm (I := I) (M := M) g r s
                  (pouSmul (I := I) (M := M) g r s α wₙ) α k P.1 P.2 y *
                euclidPartial (E := E) l
                  (gramInvEntry (I := I) (M := M) g r s α Q P₀) y
            + covDerivLowerOrderTerm (I := I) (M := M) g r s
                  (pouSmul (I := I) (M := M) g r s α wₙ) α k P.1 P.2 y *
                lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y) =
        chartInvGramEuclid (I := I) g α k l y *
            lowerOrderRotationLOCoeff (I := I) (M := M) g r s α P₀ l Q y *
            euclidPartial (E := E) k
              (tensorChartComponent (I := I) (M := M) g r s wₙ α P.1 P.2) y
          + ∑ p : TensorCompIdx (E := E) r s,
              chartInvGramEuclid (I := I) g α k l y *
                  (euclidPartial (E := E) l
                      (gramInvEntry (I := I) (M := M) g r s α Q P₀) y +
                    lowerOrderRotationLOCoeff (I := I) (M := M)
                      g r s α P₀ l Q y) *
                  covDerivLowerOrderCoeff (I := I) (M := M)
                    g r s α k P.1 p.1 P.2 p.2 y *
                tensorChartComponent (I := I) (M := M) g r s wₙ α p.1 p.2 y := by
    intro P Q k l
    rw [show euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s
                (pouSmul (I := I) (M := M) g r s α wₙ) α P.1 P.2)) y =
          euclidPartial (E := E) k
            (tensorChartComponent (I := I) (M := M) g r s wₙ α P.1 P.2) y from
        congrArg (fun u : EuclN → ℝ => euclidPartial (E := E) k u y)
          (chartPushedRaw_tensorChartComponentRaw_pouSmul_eq (I := I) (M := M)
            g r s α wₙ P.1 P.2)]
    rw [covDerivLowerOrderTerm_pouSmul_eqOn_coeffFactors (I := I) (M := M) g r s α wₙ
      k P.1 P.2 hy]
    rw [show (∑ p : TensorCompIdx (E := E) r s,
              chartInvGramEuclid (I := I) g α k l y *
                  (euclidPartial (E := E) l
                      (gramInvEntry (I := I) (M := M) g r s α Q P₀) y +
                    lowerOrderRotationLOCoeff (I := I) (M := M)
                      g r s α P₀ l Q y) *
                  covDerivLowerOrderCoeff (I := I) (M := M)
                    g r s α k P.1 p.1 P.2 p.2 y *
                tensorChartComponent (I := I) (M := M) g r s wₙ α p.1 p.2 y) =
          chartInvGramEuclid (I := I) g α k l y *
              ((∑ p : TensorCompIdx (E := E) r s,
                  covDerivLowerOrderCoeff (I := I) (M := M)
                      g r s α k P.1 p.1 P.2 p.2 y *
                    tensorChartComponent (I := I) (M := M)
                      g r s wₙ α p.1 p.2 y) *
                euclidPartial (E := E) l
                  (gramInvEntry (I := I) (M := M) g r s α Q P₀) y) +
            chartInvGramEuclid (I := I) g α k l y *
              ((∑ p : TensorCompIdx (E := E) r s,
                  covDerivLowerOrderCoeff (I := I) (M := M)
                      g r s α k P.1 p.1 P.2 p.2 y *
                    tensorChartComponent (I := I) (M := M)
                      g r s wₙ α p.1 p.2 y) *
                lowerOrderRotationLOCoeff (I := I) (M := M)
                  g r s α P₀ l Q y) from by
      rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun p _ => ?_); ring]
    ring
  rw [Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => by
    rw [Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl
      (fun l _ => hbody P Q k l))]))]
  have hsplit : ∀ P Q : TensorCompIdx (E := E) r s,
      covChartMetricGram (I := I) (M := M) g r s α P Q y *
          (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            (chartInvGramEuclid (I := I) g α k l y *
                  lowerOrderRotationLOCoeff (I := I) (M := M)
                    g r s α P₀ l Q y *
                  euclidPartial (E := E) k
                    (tensorChartComponent (I := I) (M := M)
                      g r s wₙ α P.1 P.2) y
              + ∑ p : TensorCompIdx (E := E) r s,
                  chartInvGramEuclid (I := I) g α k l y *
                      (euclidPartial (E := E) l
                          (gramInvEntry (I := I) (M := M) g r s α Q P₀) y +
                        lowerOrderRotationLOCoeff (I := I) (M := M)
                          g r s α P₀ l Q y) *
                      covDerivLowerOrderCoeff (I := I) (M := M)
                        g r s α k P.1 p.1 P.2 p.2 y *
                    tensorChartComponent (I := I) (M := M)
                      g r s wₙ α p.1 p.2 y)) =
        (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l y *
              euclidPartial (E := E) k
                (tensorChartComponent (I := I) (M := M) g r s wₙ α P.1 P.2) y)
          + ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                valueComponentFactor (I := I) (M := M) g r s α P₀ P Q k l p y *
                  tensorChartComponent (I := I) (M := M)
                    g r s wₙ α p.1 p.2 y := by
    intro P Q
    rw [Finset.mul_sum]
    rw [show (∑ k : Fin (Module.finrank ℝ E),
              covChartMetricGram (I := I) (M := M) g r s α P Q y *
                ∑ l : Fin (Module.finrank ℝ E),
                  (chartInvGramEuclid (I := I) g α k l y *
                        lowerOrderRotationLOCoeff (I := I) (M := M)
                          g r s α P₀ l Q y *
                        euclidPartial (E := E) k
                          (tensorChartComponent (I := I) (M := M)
                            g r s wₙ α P.1 P.2) y
                    + ∑ p : TensorCompIdx (E := E) r s,
                        chartInvGramEuclid (I := I) g α k l y *
                            (euclidPartial (E := E) l
                                (gramInvEntry (I := I) (M := M)
                                  g r s α Q P₀) y +
                              lowerOrderRotationLOCoeff (I := I) (M := M)
                                g r s α P₀ l Q y) *
                            covDerivLowerOrderCoeff (I := I) (M := M)
                              g r s α k P.1 p.1 P.2 p.2 y *
                          tensorChartComponent (I := I) (M := M)
                            g r s wₙ α p.1 p.2 y)) =
          ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l y *
                euclidPartial (E := E) k
                  (tensorChartComponent (I := I) (M := M)
                    g r s wₙ α P.1 P.2) y
              + ∑ p : TensorCompIdx (E := E) r s,
                  valueComponentFactor (I := I) (M := M)
                      g r s α P₀ P Q k l p y *
                    tensorChartComponent (I := I) (M := M)
                      g r s wₙ α p.1 p.2 y) from by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [mul_add]
      refine congrArg₂ (· + ·) ?_ ?_
      · rw [valuePartialFactor]; ring
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [valueComponentFactor]; ring]
    rw [Finset.sum_congr rfl (fun k _ =>
        Finset.sum_add_distrib
          (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))),
      Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl
    (fun Q _ => hsplit P Q))]
  rw [Finset.sum_congr rfl (fun P _ =>
      Finset.sum_add_distrib (s := (Finset.univ : Finset (TensorCompIdx (E := E) r s)))),
    Finset.sum_add_distrib]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeff_pouSmul_eqOn_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeff_pouSmul_eqOn_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeff_pouSmul_eqOn_section ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeff_pouSmul_eqOn_section

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
