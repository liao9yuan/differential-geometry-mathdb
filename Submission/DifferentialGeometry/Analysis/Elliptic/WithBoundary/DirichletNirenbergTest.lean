import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakChartPullback
import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.Sobolev

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
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

theorem exists_h1ComplDirichlet_nirenbergTestFunction
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (u : H1ComplDirichlet q) {η : EuStd → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ EuN)) (h : ℝ)
    (hηs : Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    let f := nirenbergTestFunction k h η (fun z => H1ComplDirichletToLp q u
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)))
    ∃ w : H1ComplDirichlet q,
      (H1ComplDirichletToLp q w : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α f ∧
      ∀ i, (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i w : EuStd → ℝ)
        =ᵐ[volume.restrict Ω] chosenWeakPartialOrZero 2 i f Ω := by
  let v : EuStd → ℝ := fun z => H1ComplDirichletToLp q u
    ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
  let f := nirenbergTestFunction k h η v
  have hv : MemWkp 1 2 v Ω := memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs u
  have hf : MemWkp 1 2 f Ω :=
    (memWkp_nirenbergTestFunction_of_memWkp_local hΩ hv hη hηc k h hηs).mono_set
      (by norm_num) hΩ (_root_.Set.subset_univ _)
  have hfs : tsupport f ⊆ Ω :=
    (nirenbergTestFunction_tsupport_subset_cthickening k h η v).trans hηs
  refine ⟨h1ComplDirichletChartPullback q α hΩ hΩc hΩs hf hfs,
    h1ComplDirichletChartPullback_coeFn q α hΩ hΩc hΩs hf hfs, ?_⟩
  intro i
  exact dirichletLocalWeakPartialLp_h1ComplDirichletChartPullback_eq_ae q α hΩ hΩc hΩs hf hfs i
    ((chosenWeakPartialOrZero_memLp_of_mem hf.memW1p i).locallyIntegrable (by norm_num))
    (chosenWeakPartialOrZero_isWeakPartial_of_mem hf.memW1p i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_h1ComplDirichlet_nirenbergTestFunction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_h1ComplDirichlet_nirenbergTestFunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_h1ComplDirichlet_nirenbergTestFunction ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_h1ComplDirichlet_nirenbergTestFunction

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
