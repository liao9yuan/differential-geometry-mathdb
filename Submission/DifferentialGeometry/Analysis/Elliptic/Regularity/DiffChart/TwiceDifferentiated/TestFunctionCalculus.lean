import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.CanonicalDerivedData
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.VariationalIdentity
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.ThirdMixedPartial
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.TwiceDifferentiated.EffectiveSource
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.FChartResidual.ResidualMemW1p
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.SmoothCoefWeakPartialIBP
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TwiceDifferentiatedVariationalIdentity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DifferentiatedCrossTermIBP
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DifferentiatedVariationalIdentity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChosenThirdMixedPartialChartPushed
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartSecondOrderEffectiveSource
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.FChartResidualMemW1p
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma contDiff_fderiv_apply_single
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (l : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN =>
      (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) := by
  have h_fderiv : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN => fderiv ℝ ψ y) :=
    (contDiff_infty_iff_fderiv.1 hψ).2
  have h_eval : ContDiff ℝ (⊤ : ℕ∞)
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single l 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l (1 : ℝ))).contDiff
  exact h_eval.comp h_fderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.contDiff_fderiv_apply_single then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.contDiff_fderiv_apply_single"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.contDiff_fderiv_apply_single ``Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.contDiff_fderiv_apply_single

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma hasCompactSupport_fderiv_apply_single
    {ψ : EuclN → ℝ} (hψ_cs : HasCompactSupport ψ)
    (l : Fin (Module.finrank ℝ E)) :
    HasCompactSupport (fun y : EuclN =>
      (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) :=
  hψ_cs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single l 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.hasCompactSupport_fderiv_apply_single then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.hasCompactSupport_fderiv_apply_single"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.hasCompactSupport_fderiv_apply_single ``Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.hasCompactSupport_fderiv_apply_single

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma tsupport_fderiv_apply_single_subset
    (ψ : EuclN → ℝ) (l : Fin (Module.finrank ℝ E)) :
    tsupport (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) ⊆
      tsupport ψ :=
  tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single l 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.tsupport_fderiv_apply_single_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.tsupport_fderiv_apply_single_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.tsupport_fderiv_apply_single_subset ``Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.tsupport_fderiv_apply_single_subset

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma fderiv_apply_single_swap
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (y : EuclN)
    (j l : Fin (Module.finrank ℝ E)) :
    (fderiv ℝ
      (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) y)
        (EuclideanSpace.single j 1) =
    (fderiv ℝ
      (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single j 1)) y)
        (EuclideanSpace.single l 1) := by
  classical
  have h_diff_fderiv : Differentiable ℝ (fderiv ℝ ψ) :=
    ((contDiff_infty_iff_fderiv.1 hψ).2).differentiable (by simp)
  have h_flip_eq : ∀ k : Fin (Module.finrank ℝ E),
      fderiv ℝ
        (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single k 1)) y =
        (fderiv ℝ (fderiv ℝ ψ) y).flip (EuclideanSpace.single k 1) := by
    intro k
    have h_const_diff :
        DifferentiableAt ℝ
          (fun _ : EuclN => (EuclideanSpace.single k (1 : ℝ))) y :=
      differentiableAt_const _
    have h_step :=
      fderiv_clm_apply (𝕜 := ℝ)
        (c := fderiv ℝ ψ) (u := fun _ : EuclN => EuclideanSpace.single k (1 : ℝ))
        (x := y) (h_diff_fderiv y) h_const_diff
    have h_const_fderiv :
        fderiv ℝ (fun _ : EuclN => EuclideanSpace.single k (1 : ℝ)) y = 0 :=
      fderiv_const_apply (EuclideanSpace.single k (1 : ℝ))
    rw [h_step, h_const_fderiv]; simp
  rw [h_flip_eq l, h_flip_eq j]
  have h_symm : IsSymmSndFDerivAt ℝ ψ y := by
    have h_ge : minSmoothness ℝ 2 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      rw [minSmoothness_of_isRCLikeNormedField]; decide
    exact hψ.contDiffAt.isSymmSndFDerivAt (𝕜 := ℝ) h_ge
  change ((fderiv ℝ (fderiv ℝ ψ) y).flip (EuclideanSpace.single l 1))
        (EuclideanSpace.single j 1) =
      ((fderiv ℝ (fderiv ℝ ψ) y).flip (EuclideanSpace.single j 1))
        (EuclideanSpace.single l 1)
  rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]
  exact h_symm (EuclideanSpace.single j 1) (EuclideanSpace.single l 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.fderiv_apply_single_swap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.fderiv_apply_single_swap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.fderiv_apply_single_swap ``Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.fderiv_apply_single_swap

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma fderiv_zero_outside_tsupport
    (ψ : EuclN → ℝ) (x : EuclN) (hx : x ∉ tsupport ψ) :
    fderiv ℝ ψ x = 0 := by
  have h_compl_open : IsOpen ((tsupport ψ)ᶜ) := (isClosed_tsupport _).isOpen_compl
  have h_fderiv_eq : fderiv ℝ ψ x = fderiv ℝ (fun _ : EuclN => (0 : ℝ)) x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [h_compl_open.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [h_fderiv_eq]; simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.fderiv_zero_outside_tsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.fderiv_zero_outside_tsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.fderiv_zero_outside_tsupport ``Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.fderiv_zero_outside_tsupport

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma fderiv_partial_zero_outside_tsupport
    {ψ : EuclN → ℝ} (x : EuclN) (hx : x ∉ tsupport ψ)
    (l : Fin (Module.finrank ℝ E)) :
    fderiv ℝ (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) x = 0 := by
  have h_compl_open : IsOpen ((tsupport ψ)ᶜ) := (isClosed_tsupport _).isOpen_compl
  have h_fderiv_eq : fderiv ℝ
      (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) x =
        fderiv ℝ (fun _ : EuclN => (0 : ℝ)) x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [h_compl_open.mem_nhds hx] with y hy
    rw [fderiv_zero_outside_tsupport ψ y hy]; simp
  rw [h_fderiv_eq]; simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.fderiv_partial_zero_outside_tsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.fderiv_partial_zero_outside_tsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.fderiv_partial_zero_outside_tsupport ``Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.fderiv_partial_zero_outside_tsupport

end TwiceDifferentiatedVariationalIdentity
end Laplacian
end Analysis
end DifferentialGeometry

end
