import Submission.DifferentialGeometry.Geometry.Operator.Family.Gram.Smoothness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.Force
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.Defs

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
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Geometry.Operator

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
    (fderiv Real (fun y : E => chartGramOp (I := I) S.family p (q.1, y)) q.2)
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lGramDir
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.lGramDir target :: scope.openDecls } }

private noncomputable def lScalarDir
    (S : SolutionOn (I := I) (M := M) D) (p : M)
    (i : Fin (Module.finrank Real E)) (q : Real × E) : Real :=
  fderiv Real (scalarOnE (I := I) p (S.scalar q.1)) q.2
    (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lScalarDir
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.lScalarDir target :: scope.openDecls } }

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
theorem integrableOn_lChartForce_of_spatial_derivatives
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (hL : 0 < L) (u : timeH1 E L)
    {J : Set Real}
    (htime : ∀ r ∈ _root_.Set.Icc (0 : Real) L, T - (a + r) ^ 2 ∈ J)
    (hreg : ∀ r ∈ _root_.Set.Ioo (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hGramFd : ContinuousOn (fun z : Real × E => fderiv Real
      (fun y : E => chartGramOp (I := I) S.family p (z.1, y)) z.2)
      (J ×ˢ interior (extChartAt I p).target))
    (hScalFd : ContinuousOn (fun z : Real × E => fderiv Real
      (scalarOnE (I := I) p (S.scalar z.1)) z.2)
      (J ×ˢ interior (extChartAt I p).target))
    (hchart : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : Real) L)
      (interior (extChartAt I p).target)) :
    IntegrableOn (lChartForce (I := I) S T a p u)
      (_root_.Set.Icc (0 : Real) L) volume := by
  classical
  let tau : Real → Real := fun r ↦ T - (a + r) ^ 2
  let Jt : Set Real := tau '' _root_.Set.Icc (0 : Real) L
  let K : Set E := u.toFun '' _root_.Set.Icc (0 : Real) L
  let U : Set (Real × E) := J ×ˢ interior (extChartAt I p).target
  have htau : ContinuousOn tau (_root_.Set.Icc (0 : Real) L) :=
    continuousOn_const.sub ((continuousOn_const.add continuousOn_id).pow 2)
  have hJc : IsCompact Jt := isCompact_Icc.image_of_continuousOn htau
  have hKc : IsCompact K :=
    isCompact_Icc.image_of_continuousOn u.continuousOn_toFun
  have hJreg : Jt ⊆ J := by
    rintro t ⟨r, hr, rfl⟩
    exact htime r hr
  have hKchart : K ⊆ interior (extChartAt I p).target := by
    rintro x ⟨r, hr, rfl⟩
    exact hchart hr
  have hpair : ContinuousOn (fun r ↦ (tau r, u.toFun r))
      (_root_.Set.Icc (0 : Real) L) := htau.prodMk u.continuousOn_toFun
  have hpair_mem : _root_.Set.MapsTo (fun r ↦ (tau r, u.toFun r))
      (_root_.Set.Icc (0 : Real) L) U := by
    intro r hr
    exact ⟨htime r hr, hchart hr⟩
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
        (fun q ↦ lGramDir (I := I) S p i q) (Jt ×ˢ K) :=
      hdir.mono (_root_.Set.prod_mono hJreg hKchart)
    obtain ⟨C0, hC0⟩ := (hJc.prod hKc).bddAbove_image hdirJK.norm
    let C : NNReal := ⟨max C0 0, le_max_right C0 0⟩
    have hC : ∀ᵐ r ∂timeMeasure L, ‖A r‖ ≤ (C : Real) := by
      filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with r hr
      have hmem : (tau r, u.toFun r) ∈ Jt ×ˢ K :=
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
    have hsmooth : ContinuousOn
        (fun q : Real × E ↦ lScalarDir (I := I) S p i q) U :=
      hScalFd.clm_apply continuousOn_const
    have hcomp : ContinuousOn
        (fun r ↦ lScalarDir (I := I) S p i (tau r, u.toFun r))
        (_root_.Set.Icc (0 : Real) L) :=
      hsmooth.comp hpair hpair_mem
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
  have haeReg : ∀ᵐ r ∂volume.restrict (_root_.Set.Icc (0 : Real) L), r ∈ _root_.Set.Ioo (0 : Real) L := by
    rw [← _root_.MeasureTheory.restrict_Ioo_eq_restrict_Icc]
    exact _root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo
  have hcov' : _root_.MeasureTheory.IntegrableOn
      (lChartPositionDerivative (I := I) S T a p u) (_root_.Set.Icc (0 : Real) L) volume := by
    refine hcov.congr ?_
    filter_upwards [haeReg] with r hr
    have hx := hchart ⟨hr.1.le, hr.2.le⟩
    have hG := chartGramOp_spatial_fderiv_eq S.family hS.smoothMetric p (hreg r hr) hx
    have hscalar (i : Fin (Module.finrank Real E)) :
        lScalarDir (I := I) S p i (tau r, u.toFun r) =
          mvfderiv (I := I) (S.scalar (tau r)) ((extChartAt I p).symm (u.toFun r))
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) p i
              ((extChartAt I p).symm (u.toFun r))) := by
      rw [lScalarDir, DifferentialGeometry.mvfderiv_real_eq_mfderiv]
      have hsrc : (extChartAt I p).symm (u.toFun r) ∈ (chartAt H p).source := by
        simpa only [extChartAt_source] using (extChartAt I p).map_target (interior_subset hx)
      have hright := (extChartAt I p).right_inv (interior_subset hx)
      have hf := scalarSmoothOfSolution (I := I) S (tau r)
      rw [mfderiv_chartBasisVecFiber_of_mdifferentiableAt
        (I := I) p (hf.mdifferentiableAt (by simp)) hsrc
          (by simpa only [hright] using hx) i]
      simp only [DifferentialGeometry.Tensor.Coordinates.partialDeriv, hright]
      rfl
    unfold lChartPositionDerivative
    apply Finset.sum_congr rfl
    intro i _
    rw [hscalar i]
    dsimp only [lGramDir]
    rw [hG]
    rfl
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
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.integrableOn_lChartForce_of_spatial_derivatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.integrableOn_lChartForce_of_spatial_derivatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.integrableOn_lChartForce_of_spatial_derivatives ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.integrableOn_lChartForce_of_spatial_derivatives

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
