import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletNirenbergOperator
import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.WeakDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
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

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart


theorem dirichletLocalWeakPartialLp_dirichletNirenbergTest_expanded
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k j : Fin (Module.finrank ℝ EuN)) (h : ℝ)
    (hηs : Metric.cthickening |h| (tsupport η) ⊆ Ω) (u : H1ComplDirichlet q) :
    let v := fun z => H1ComplDirichletToLp q u
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    let g := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j u
    (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j
      (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hηs u) : EuStd → ℝ)
      =ᵐ[volume.restrict Ω]
        DifferentialGeometry.Analysis.Sobolev.diffQuot k (-h) (fun x => (η x)^2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g : EuStd → ℝ) x +
          2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h v x) := by
  let v := fun z => H1ComplDirichletToLp q u
    ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
  let g := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j u
  let f := nirenbergTestFunction k h η v
  let G := DifferentialGeometry.Analysis.Sobolev.diffQuot k (-h) (fun x => (η x)^2 *
    DifferentialGeometry.Analysis.Sobolev.diffQuot k h (g : EuStd → ℝ) x +
    2 * η x * fderiv ℝ η x (EuclideanSpace.single j 1) *
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h v x)
  have hv : MemWkp 1 2 v Ω := memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs u
  have hf : MemWkp 1 2 f Ω :=
    (memWkp_nirenbergTestFunction_of_memWkp_local hΩ hv hη hηc k h hηs).mono_set
      (by norm_num) hΩ (_root_.Set.subset_univ _)
  have hGp : _root_.MeasureTheory.MemLp G 2 volume := memLp_nirenbergTestFunction_partial_local hΩ hv.memLp
    (Lp.memLp g) k j h hη hηc hηs
  have hG : DeGiorgi.HasWeakPartialDeriv j G f univ :=
    hasWeakPartialDeriv_nirenbergTestFunction_local hΩ hv.memLp (Lp.memLp g) k j h
      (hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j u) hη hηc hηs
  have hGΩ : DeGiorgi.HasWeakPartialDeriv j G f Ω := by
    exact DeGiorgi.HasWeakPartialDeriv.restrict hΩ (_root_.Set.subset_univ _) hG
  apply (dirichletLocalWeakPartialLp_dirichletNirenbergTest_coeFn q α hΩ hΩc hΩs
    hη hηc k j h hηs u).trans
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ
    (chosenWeakPartialOrZero_isWeakPartial_of_mem hf.memW1p j) hGΩ
    ((chosenWeakPartialOrZero_memLp_of_mem hf.memW1p j).locallyIntegrable (by norm_num))
    ((hGp.restrict Ω).locallyIntegrable (by norm_num))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_dirichletNirenbergTest_expanded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_dirichletNirenbergTest_expanded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_dirichletNirenbergTest_expanded ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletLocalWeakPartialLp_dirichletNirenbergTest_expanded

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
