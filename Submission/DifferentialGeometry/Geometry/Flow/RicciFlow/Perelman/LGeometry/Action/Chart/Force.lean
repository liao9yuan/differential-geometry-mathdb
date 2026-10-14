import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.Basic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.Defs
import Submission.DifferentialGeometry.Geometry.Operator.Family.Gram.Smoothness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

private noncomputable def lGramDir
    (S : SolutionOn (I := I) (M := M) D) (p : M)
    (i : Fin (Module.finrank Real E)) (q : Real × E) : E →L[Real] E :=
  (1 / 2 : Real) •
    (fderiv Real (chartGramOp (I := I) S.family p) q) (0, DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lGramDir
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.lGramDir target :: scope.openDecls } }

private noncomputable def lScalarDir
    (S : SolutionOn (I := I) (M := M) D) (p : M)
    (i : Fin (Module.finrank Real E)) (q : Real × E) : Real :=
  let x := (extChartAt I p).symm q.2
  mvfderiv (I := I) (S.scalar q.1) x
    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) p i x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lScalarDir
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.lScalarDir target :: scope.openDecls } }

noncomputable def lChartPositionDerivative
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) (r : Real) : E →L[Real] Real :=
  ∑ i : Fin (Module.finrank Real E),
    (_root_.Inner.inner Real
        (lGramDir (I := I) S p i
          (T - (a + r) ^ 2, u.toFun r) (u.deriv r))
        (u.deriv r) +
      2 * (a + r) ^ 2 *
        lScalarDir (I := I) S p i
          (T - (a + r) ^ 2, u.toFun r)) •
      chartCoordCLM E i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartPositionDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lChartPositionDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartPositionDerivative ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lChartPositionDerivative

noncomputable def lChartForce
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) (r : Real) : E :=
  (lChartPositionDerivative (I := I) S T a p u r).adjoint 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartForce then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lChartForce"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartForce ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lChartForce

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
theorem inner_lChartForce
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) (r : Real) (v : E) :
    inner Real (lChartForce (I := I) S T a p u r) v =
      lChartPositionDerivative (I := I) S T a p u r v := by
  rw [lChartForce, ContinuousLinearMap.adjoint_inner_left]
  rw [real_inner_eq_re_inner, RCLike.inner_apply]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.inner_lChartForce then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.inner_lChartForce"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.inner_lChartForce ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.inner_lChartForce

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
theorem integrableOn_lChartForce
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (hL : 0 < L) (u : timeH1 E L)
    (hreg : ∀ r ∈ _root_.Set.Icc (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hchart : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : Real) L)
      (interior (extChartAt I p).target)) :
    IntegrableOn (lChartForce (I := I) S T a p u)
      (_root_.Set.Icc (0 : Real) L) volume := by
  classical
  let tau : Real → Real := fun r ↦ T - (a + r) ^ 2
  let J : Set Real := tau '' _root_.Set.Icc (0 : Real) L
  let K : Set E := u.toFun '' _root_.Set.Icc (0 : Real) L
  let U : Set (Real × E) := D.regular ×ˢ interior (extChartAt I p).target
  have htau : ContinuousOn tau (_root_.Set.Icc (0 : Real) L) :=
    continuousOn_const.sub ((continuousOn_const.add continuousOn_id).pow 2)
  have hJc : IsCompact J := isCompact_Icc.image_of_continuousOn htau
  have hKc : IsCompact K :=
    isCompact_Icc.image_of_continuousOn u.continuousOn_toFun
  have hJreg : J ⊆ D.regular := by
    rintro t ⟨r, hr, rfl⟩
    exact hreg r hr
  have hKchart : K ⊆ interior (extChartAt I p).target := by
    rintro x ⟨r, hr, rfl⟩
    exact hchart hr
  have hUopen : IsOpen U := D.regular_isOpen.prod isOpen_interior
  have hpair : ContinuousOn (fun r ↦ (tau r, u.toFun r))
      (_root_.Set.Icc (0 : Real) L) := htau.prodMk u.continuousOn_toFun
  have hpair_mem : _root_.Set.MapsTo (fun r ↦ (tau r, u.toFun r))
      (_root_.Set.Icc (0 : Real) L) U := by
    intro r hr
    exact ⟨hreg r hr, hchart hr⟩
  have hGram : ContDiffOn Real ∞
      (chartGramOp (I := I) S.family p) U := by
    simpa only [U] using chartGramOp_smooth (I := I) hS.smoothMetric p
      (K := interior (extChartAt I p).target) Subset.rfl
  have hGramFd : ContinuousOn
      (fderiv Real (chartGramOp (I := I) S.family p)) U :=
    hGram.continuousOn_fderiv_of_isOpen hUopen (by simp)
  have hkin (i : Fin (Module.finrank Real E)) : _root_.MeasureTheory.IntegrableOn
      (fun r ↦ _root_.Inner.inner Real
        (lGramDir (I := I) S p i (tau r, u.toFun r) (u.deriv r))
        (u.deriv r)) (_root_.Set.Icc (0 : Real) L) volume := by
    let A : Real → E →L[Real] E := fun r ↦
      lGramDir (I := I) S p i (tau r, u.toFun r)
    have hdir : ContinuousOn
        (fun q ↦ lGramDir (I := I) S p i q) U := by
      exact (hGramFd.clm_apply continuousOn_const).const_smul (1 / 2 : Real)
    have hAcont : ContinuousOn A (_root_.Set.Icc (0 : Real) L) :=
      hdir.comp hpair hpair_mem
    have hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure L) := by
      simpa only [timeMeasure] using
        hAcont.aestronglyMeasurable measurableSet_Icc
    have hdirJK : ContinuousOn
        (fun q ↦ lGramDir (I := I) S p i q) (J ×ˢ K) :=
      hdir.mono (_root_.Set.prod_mono hJreg hKchart)
    obtain ⟨C0, hC0⟩ := (hJc.prod hKc).bddAbove_image hdirJK.norm
    let C : NNReal := ⟨max C0 0, le_max_right C0 0⟩
    have hC : ∀ᵐ r ∂timeMeasure L, ‖A r‖ ≤ (C : Real) := by
      filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with r hr
      have hmem : (tau r, u.toFun r) ∈ J ×ˢ K :=
        ⟨⟨r, hr, rfl⟩, ⟨r, hr, rfl⟩⟩
      exact (hC0 ⟨(tau r, u.toFun r), hmem, rfl⟩).trans
        (le_max_left C0 0)
    have hq := timeQuad_int A hA C hC hL.le u.deriv
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hL.le] at hq
    simpa only [A] using hq
  have hscalar (i : Fin (Module.finrank Real E)) : _root_.MeasureTheory.IntegrableOn
      (fun r ↦ 2 * (a + r) ^ 2 *
        lScalarDir (I := I) S p i (tau r, u.toFun r))
      (_root_.Set.Icc (0 : Real) L) volume := by
    have hsmooth : ContDiffOn Real ∞
        (fun q : Real × E ↦ lScalarDir (I := I) S p i q) U := by
      with_unfolding_all exact chartScalarDeriv (I := I) S hS p i
    have hcomp : ContinuousOn
        (fun r ↦ lScalarDir (I := I) S p i (tau r, u.toFun r))
        (_root_.Set.Icc (0 : Real) L) :=
      hsmooth.continuousOn.comp hpair hpair_mem
    exact (((continuousOn_const.mul
      ((continuousOn_const.add continuousOn_id).pow 2)).mul hcomp)).integrableOn_Icc
  have hcov : _root_.MeasureTheory.IntegrableOn
    (fun r ↦ ∑ i : Fin (Module.finrank Real E),
      (_root_.Inner.inner Real
          (lGramDir (I := I) S p i (tau r, u.toFun r) (u.deriv r))
          (u.deriv r) +
        2 * (a + r) ^ 2 *
          lScalarDir (I := I) S p i (tau r, u.toFun r)) •
        chartCoordCLM E i)
    (_root_.Set.Icc (0 : Real) L) volume := by
    change _root_.MeasureTheory.Integrable (fun r ↦ ∑ i : Fin (Module.finrank Real E),
      (_root_.Inner.inner Real
          (lGramDir (I := I) S p i (tau r, u.toFun r) (u.deriv r))
          (u.deriv r) +
        2 * (a + r) ^ 2 *
          lScalarDir (I := I) S p i (tau r, u.toFun r)) •
        chartCoordCLM E i) (volume.restrict (_root_.Set.Icc (0 : Real) L))
    refine _root_.MeasureTheory.integrable_finsetSum Finset.univ
      (f := fun i r ↦
        (_root_.Inner.inner Real
            (lGramDir (I := I) S p i (tau r, u.toFun r) (u.deriv r))
            (u.deriv r) +
          2 * (a + r) ^ 2 *
            lScalarDir (I := I) S p i (tau r, u.toFun r)) •
          chartCoordCLM E i) ?_
    intro i _
    exact (hkin i).add (hscalar i) |>.smul_const (chartCoordCLM E i)
  have hadj : Continuous
      (fun A : E →L[Real] Real ↦ A.adjoint (1 : Real)) :=
    (ContinuousLinearMap.adjoint (E := E) (F := Real)).continuous.clm_apply
      continuous_const
  have hcov' : _root_.MeasureTheory.IntegrableOn
      (lChartPositionDerivative (I := I) S T a p u) (_root_.Set.Icc (0 : Real) L) volume := by
    with_unfolding_all exact hcov
  change _root_.MeasureTheory.Integrable (lChartForce (I := I) S T a p u)
    (volume.restrict (_root_.Set.Icc (0 : Real) L))
  refine Integrable.mono' hcov'.norm
    (hadj.comp_aestronglyMeasurable hcov'.aestronglyMeasurable) ?_
  filter_upwards [] with r
  change ‖(lChartPositionDerivative (I := I) S T a p u r).adjoint (1 : Real)‖ ≤
    ‖lChartPositionDerivative (I := I) S T a p u r‖
  simpa using
    (lChartPositionDerivative (I := I) S T a p u r).adjoint.le_opNorm (1 : Real)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.integrableOn_lChartForce then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.integrableOn_lChartForce"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.integrableOn_lChartForce ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.integrableOn_lChartForce

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
