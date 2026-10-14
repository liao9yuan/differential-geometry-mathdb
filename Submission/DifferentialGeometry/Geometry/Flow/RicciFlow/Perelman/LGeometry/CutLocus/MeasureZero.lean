import Submission.DifferentialGeometry.Analysis.Integration.Measure.Differentiation.Rademacher
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.ChartLipschitz
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Conjugate.MeasureZero
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.MultipleMinimizers
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.LocalCostBranch

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

theorem lCutMulti_null
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g
      (lCutMulti S T x tau) = 0 := by
  classical
  rcases (lCutMulti S T x tau).eq_empty_or_nonempty with hempty | hmulti
  · rw [hempty, _root_.MeasureTheory.measure_empty]
  · rcases hmulti with ⟨y₀, hy₀⟩
    rcases hy₀ with ⟨Z₀, hZ₀cut, _⟩
    have hZ₀min : (Z₀, tau) ∈ lMinDomain S T x :=
      ((mem_lCutDomain S T x tau Z₀).1 hZ₀cut).1
    have htau : 0 < tau :=
      lMinDomain_pos S T x Z₀ tau hZ₀min
    have hZ₀dom : (Z₀, tau) ∈ lExpPosDom S T x :=
      ((mem_lMinDomain S T x Z₀ tau).1 hZ₀min).1
    have hslab : _root_.Set.Icc (T - tau) T ⊆ D.regular := by
      intro r hr
      have hnonneg : 0 ≤ T - r := by
        linarith [hr.2]
      have hle : T - r ≤ tau := by
        linarith [hr.1]
      have hsqrt :
          Real.sqrt (T - r) ∈ _root_.Set.Icc (0 : Real) (Real.sqrt tau) :=
        ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hle⟩
      have hreg :=
        lExpPosDom_regularity S T x Z₀ hZ₀dom hsqrt
      have heq : T - (Real.sqrt (T - r)) ^ 2 = r := by
        rw [Real.sq_sqrt hnonneg]
        ring
      simpa only [heq] using hreg
    have hdiff₀ :
        riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | ¬ MDifferentiableAt I (modelWithCornersSelf Real Real)
            (fun z : M ↦ lCost S T x z tau) y} = 0 :=
      nondiff_null (I := I) (M := M) g
        (fun z : M ↦ lCost S T x z tau)
        (fun p ↦ lCost_chart_lip (I := I) S hS T x tau htau hslab p)
    refine _root_.MeasureTheory.measure_mono_null ?_
      (_root_.MeasureTheory.measure_union_null (lCutConj_null S hS T x tau g) hdiff₀)
    rintro y ⟨Z, hZcut, W, hWne, hWmin, hend, rfl⟩
    have hZmin : (Z, tau) ∈ lMinDomain S T x :=
      ((mem_lCutDomain S T x tau Z).1 hZcut).1
    have hWcut : (W : E) ∈ lCutDomain S T x tau :=
      mem_lCutDomain_of_distinct_minimizer_same_endpoint S hS T x hZcut hWne hWmin hend
    by_cases hZconj : IsLConjugate S T x Z tau
    · exact Or.inl ⟨Z, hZcut, hZconj, rfl⟩
    by_cases hWconj : IsLConjugate S T x W tau
    · exact Or.inl ⟨W, hWcut, hWconj, hend⟩
    · exact Or.inr <|
        lCost_nondiff_two (I := I) S hS T x
          hZmin hWmin hZconj hWconj hWne.symm hend.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lCutMulti_null then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lCutMulti_null"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lCutMulti_null ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lCutMulti_null

theorem lCut_null
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g
      (lCutImage S T x tau) = 0 := by
  rw [lCut_split S hS T x tau]
  exact _root_.MeasureTheory.measure_union_null
    (lCutConj_null S hS T x tau g)
    (lCutMulti_null S hS T x tau g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lCut_null then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lCut_null"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lCut_null ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lCut_null

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
