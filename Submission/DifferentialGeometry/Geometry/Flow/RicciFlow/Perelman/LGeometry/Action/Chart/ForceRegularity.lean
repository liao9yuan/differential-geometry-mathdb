import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.Force
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
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

noncomputable def lChartPositionDerivativeRepresentative
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) (q : Real → E) (r : Real) :
    E →L[Real] Real :=
  ∑ i : Fin (Module.finrank Real E),
    (_root_.Inner.inner Real
        (((1 / 2 : Real) •
          (fderiv Real (chartGramOp (I := I) S.family p)
            (T - (a + r) ^ 2, u.toFun r))
            (0, DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) (q r))
        (q r) +
      2 * (a + r) ^ 2 *
        chartScalCov (I := I) S p (T - (a + r) ^ 2, u.toFun r)
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) •
      chartCoordCLM E i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartPositionDerivativeRepresentative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lChartPositionDerivativeRepresentative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartPositionDerivativeRepresentative ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lChartPositionDerivativeRepresentative

noncomputable def lChartForceRepresentative
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) (q : Real → E) (r : Real) : E :=
  (lChartPositionDerivativeRepresentative (I := I) S T a p u q r).adjoint 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartForceRepresentative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lChartForceRepresentative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartForceRepresentative ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lChartForceRepresentative

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
private theorem chartScalCov_basis
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (p : M)
    (z : Real × E)
    (hz : z ∈ D.regular ×ˢ interior (extChartAt I p).target)
    (i : Fin (Module.finrank Real E)) :
    chartScalCov (I := I) S p z (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) =
      let x := (extChartAt I p).symm z.2
      mvfderiv (I := I) (S.scalar z.1) x
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) p i x) := by
  let f : M → Real := S.scalar z.1
  let x : M := (extChartAt I p).symm z.2
  have hzt : z.2 ∈ (extChartAt I p).target := interior_subset hz.2
  have hxsrc : x ∈ (chartAt H p).source := by
    have hxext : x ∈ (extChartAt I p).source :=
      (extChartAt I p).map_target hzt
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hxext
  have hright : extChartAt I p x = z.2 :=
    (extChartAt I p).right_inv hzt
  have hf : ContMDiff I 𝓘(Real, Real) ∞ f := by
    simpa only [f] using scalarSmoothOfSolution (I := I) S z.1
  rw [chartScalCov_apply (I := I) S hS p hz.1 hz.2]
  rw [DifferentialGeometry.mvfderiv_real_eq_mfderiv]
  rw [mfderiv_chartBasisVecFiber_of_mdifferentiableAt
    (I := I) p (hf.mdifferentiableAt (by simp)) hxsrc
      (by simpa only [hright] using hz.2) i]
  simp only [DifferentialGeometry.Tensor.Coordinates.partialDeriv, hright, f, x]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.chartScalCov_basis
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.chartScalCov_basis target :: scope.openDecls } }

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
theorem continuousOn_lChartForceRepresentative
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) (q : Real → E)
    (hreg : ∀ r ∈ _root_.Set.Icc (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hchart : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : Real) L)
      (interior (extChartAt I p).target))
    (hq : ContinuousOn q (_root_.Set.Icc (0 : Real) L)) :
    ContinuousOn (lChartForceRepresentative (I := I) S T a p u q)
      (_root_.Set.Icc (0 : Real) L) := by
  classical
  let tau : Real → Real := fun r ↦ T - (a + r) ^ 2
  let U : Set (Real × E) :=
    D.regular ×ˢ interior (extChartAt I p).target
  have htau : ContinuousOn tau (_root_.Set.Icc (0 : Real) L) :=
    continuousOn_const.sub ((continuousOn_const.add continuousOn_id).pow 2)
  have hpair : ContinuousOn (fun r ↦ (tau r, u.toFun r))
      (_root_.Set.Icc (0 : Real) L) := htau.prodMk u.continuousOn_toFun
  have hpair_mem : _root_.Set.MapsTo (fun r ↦ (tau r, u.toFun r))
      (_root_.Set.Icc (0 : Real) L) U := by
    intro r hr
    exact ⟨hreg r hr, hchart hr⟩
  have hUopen : IsOpen U := D.regular_isOpen.prod isOpen_interior
  have hGram : ContDiffOn Real ∞
      (chartGramOp (I := I) S.family p) U := by
    simpa only [U] using chartGramOp_smooth (I := I) hS.smoothMetric p
      (K := interior (extChartAt I p).target) Subset.rfl
  have hGramFd : ContinuousOn
      (fderiv Real (chartGramOp (I := I) S.family p)) U :=
    hGram.continuousOn_fderiv_of_isOpen hUopen (by simp)
  have hScal : ContinuousOn (chartScalCov (I := I) S p) U := by
    simpa only [U] using (chartScalCov_smooth (I := I) S hS p).continuousOn
  have hcoord (i : Fin (Module.finrank Real E)) : ContinuousOn
      (fun r ↦
        _root_.Inner.inner Real
          (((1 / 2 : Real) •
            (fderiv Real (chartGramOp (I := I) S.family p)
              (tau r, u.toFun r)) (0, DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) (q r))
          (q r) +
        2 * (a + r) ^ 2 *
          chartScalCov (I := I) S p (tau r, u.toFun r)
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i))
      (_root_.Set.Icc (0 : Real) L) := by
    have hdir : ContinuousOn
        (fun z ↦ (1 / 2 : Real) •
          (fderiv Real (chartGramOp (I := I) S.family p) z)
            (0, DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) U :=
      by
        have hvec : ContinuousOn
            (fun _ : Real × E ↦ ((0 : Real), DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) U :=
          continuousOn_const
        have h := (hGramFd.clm_apply hvec).const_smul (1 / 2 : Real)
        with_unfolding_all exact h
    have hdir' : ContinuousOn
        (fun r ↦ (1 / 2 : Real) •
          (fderiv Real (chartGramOp (I := I) S.family p)
            (tau r, u.toFun r)) (0, DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i))
        (_root_.Set.Icc (0 : Real) L) := hdir.comp hpair hpair_mem
    have hkin : ContinuousOn
        (fun r ↦ _root_.Inner.inner Real
          (((1 / 2 : Real) •
            (fderiv Real (chartGramOp (I := I) S.family p)
              (tau r, u.toFun r)) (0, DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) (q r))
          (q r)) (_root_.Set.Icc (0 : Real) L) :=
      (hdir'.clm_apply hq).inner (𝕜 := Real) hq
    have hscal : ContinuousOn
        (fun r ↦ chartScalCov (I := I) S p (tau r, u.toFun r)
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) (_root_.Set.Icc (0 : Real) L) :=
      (hScal.comp hpair hpair_mem).clm_apply continuousOn_const
    exact hkin.add
      ((continuousOn_const.mul
        ((continuousOn_const.add continuousOn_id).pow 2)).mul hscal)
  have hpos : ContinuousOn
      (lChartPositionDerivativeRepresentative (I := I) S T a p u q) (_root_.Set.Icc (0 : Real) L) := by
    with_unfolding_all exact
      continuousOn_finsetSum Finset.univ fun i _ ↦
        (hcoord i).smul continuousOn_const
  have hadj : Continuous
      (fun A : E →L[Real] Real ↦ A.adjoint (1 : Real)) :=
    (ContinuousLinearMap.adjoint (E := E) (F := Real)).continuous.clm_apply
      continuous_const
  with_unfolding_all exact hadj.comp_continuousOn hpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.continuousOn_lChartForceRepresentative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.continuousOn_lChartForceRepresentative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.continuousOn_lChartForceRepresentative ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.continuousOn_lChartForceRepresentative

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
theorem lChartForce_ae_eq_lChartForceRepresentative
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) (q : Real → E)
    (hreg : ∀ r ∈ _root_.Set.Icc (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hchart : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : Real) L)
      (interior (extChartAt I p).target))
    (hq : u.deriv =ᵐ[timeMeasure L] q) :
    lChartForce (I := I) S T a p u =ᵐ[timeMeasure L]
      lChartForceRepresentative (I := I) S T a p u q := by
  classical
  filter_upwards [hq, _root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with r hrq hr
  have hz : (T - (a + r) ^ 2, u.toFun r) ∈
      D.regular ×ˢ interior (extChartAt I p).target :=
    ⟨hreg r hr, hchart hr⟩
  have hscal := chartScalCov_basis (I := I) S hS p
    (T - (a + r) ^ 2, u.toFun r) hz
  have hpos : lChartPositionDerivative (I := I) S T a p u r =
      lChartPositionDerivativeRepresentative (I := I) S T a p u q r := by
    rw [lChartPositionDerivative, lChartPositionDerivativeRepresentative]
    apply Finset.sum_congr rfl
    intro i _
    rw [hrq, hscal i]
    rfl
  rw [lChartForce, lChartForceRepresentative, hpos]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartForce_ae_eq_lChartForceRepresentative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lChartForce_ae_eq_lChartForceRepresentative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartForce_ae_eq_lChartForceRepresentative ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lChartForce_ae_eq_lChartForceRepresentative

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {D : RealTimeInterval}

def lChartSpatialForceRepresentative
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) (q : Real → E) (r : Real) : E :=
  (∑ i : Fin (Module.finrank Real E),
    (_root_.Inner.inner Real
        (((1 / 2 : Real) •
          fderiv Real (fun y : E => chartGramOp (I := I) S.family p
            (T - (a + r) ^ 2, y)) (u.toFun r))
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) (q r)) (q r) +
      2 * (a + r) ^ 2 *
        fderiv Real (scalarOnE (I := I) p (S.scalar (T - (a + r) ^ 2)))
          (u.toFun r) (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) •
      chartCoordCLM E i).adjoint 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartSpatialForceRepresentative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lChartSpatialForceRepresentative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartSpatialForceRepresentative ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lChartSpatialForceRepresentative

theorem continuousOn_lChartSpatialForceRepresentative
    (S : SolutionOn (I := I) (M := M) D) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) (q : Real → E) {J : Set Real}
    (htime : ∀ r ∈ _root_.Set.Icc (0 : Real) L, T - (a + r) ^ 2 ∈ J)
    (hGramFd : ContinuousOn (fun z : Real × E => fderiv Real
      (fun y : E => chartGramOp (I := I) S.family p (z.1, y)) z.2)
      (J ×ˢ interior (extChartAt I p).target))
    (hScalFd : ContinuousOn (fun z : Real × E => fderiv Real
      (scalarOnE (I := I) p (S.scalar z.1)) z.2)
      (J ×ˢ interior (extChartAt I p).target))
    (hchart : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : Real) L)
      (interior (extChartAt I p).target))
    (hq : ContinuousOn q (_root_.Set.Icc (0 : Real) L)) :
    ContinuousOn (lChartSpatialForceRepresentative S T a p u q) (_root_.Set.Icc (0 : Real) L) := by
  let tau : Real → Real := fun r => T - (a + r) ^ 2
  have htau : ContinuousOn tau (_root_.Set.Icc (0 : Real) L) :=
    continuousOn_const.sub ((continuousOn_const.add continuousOn_id).pow 2)
  have hpair : ContinuousOn (fun r => (tau r, u.toFun r)) (_root_.Set.Icc (0 : Real) L) :=
    htau.prodMk u.continuousOn_toFun
  have hpair_mem : _root_.Set.MapsTo (fun r => (tau r, u.toFun r)) (_root_.Set.Icc (0 : Real) L)
      (J ×ˢ interior (extChartAt I p).target) :=
    fun r hr => ⟨htime r hr, hchart hr⟩
  have hG := hGramFd.comp hpair hpair_mem
  have hR := hScalFd.comp hpair hpair_mem
  have hcoord (i : Fin (Module.finrank Real E)) : ContinuousOn
      (fun r =>
        _root_.Inner.inner Real
          (((1 / 2 : Real) •
            fderiv Real (fun y : E => chartGramOp (I := I) S.family p
              (tau r, y)) (u.toFun r))
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) (q r)) (q r) +
          2 * (a + r) ^ 2 *
            fderiv Real (scalarOnE (I := I) p (S.scalar (tau r))) (u.toFun r)
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i))
      (_root_.Set.Icc (0 : Real) L) := by
    have hdir := (hG.const_smul (1 / 2 : Real)).clm_apply
      (show ContinuousOn (fun _ : Real =>
        DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) (_root_.Set.Icc (0 : Real) L) from
        continuousOn_const)
    have hkin := (hdir.clm_apply hq).inner (𝕜 := Real) hq
    have hscal := hR.clm_apply
      (show ContinuousOn (fun _ : Real =>
        DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) (_root_.Set.Icc (0 : Real) L) from
        continuousOn_const)
    exact hkin.add (((continuousOn_const.add continuousOn_id).pow 2).const_mul 2 |>.mul hscal)
  have hcov : ContinuousOn
      (fun r => ∑ i : Fin (Module.finrank Real E),
        (_root_.Inner.inner Real
          (((1 / 2 : Real) •
            fderiv Real (fun y : E => chartGramOp (I := I) S.family p
              (tau r, y)) (u.toFun r))
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) (q r)) (q r) +
          2 * (a + r) ^ 2 *
            fderiv Real (scalarOnE (I := I) p (S.scalar (tau r))) (u.toFun r)
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)) •
          chartCoordCLM E i) (_root_.Set.Icc (0 : Real) L) :=
    continuousOn_finsetSum Finset.univ fun i _ => (hcoord i).smul continuousOn_const
  have hadj : Continuous (fun A : E →L[Real] Real => A.adjoint (1 : Real)) :=
    (ContinuousLinearMap.adjoint (E := E) (F := Real)).continuous.clm_apply continuous_const
  exact hadj.comp_continuousOn hcov

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.continuousOn_lChartSpatialForceRepresentative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.continuousOn_lChartSpatialForceRepresentative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.continuousOn_lChartSpatialForceRepresentative ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.continuousOn_lChartSpatialForceRepresentative

variable [T2Space M]

theorem lChartForce_ae_eq_lChartSpatialForceRepresentative
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) (q : Real → E)
    (hreg : ∀ r ∈ _root_.Set.Ioo (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hchart : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : Real) L)
      (interior (extChartAt I p).target))
    (hq : u.deriv =ᵐ[timeMeasure L] q) :
    lChartForce (I := I) S T a p u =ᵐ[timeMeasure L]
      lChartSpatialForceRepresentative S T a p u q := by
  have haeReg : ∀ᵐ r ∂timeMeasure L, r ∈ _root_.Set.Ioo (0 : Real) L := by
    change ∀ᵐ r ∂volume.restrict (_root_.Set.Icc (0 : Real) L), r ∈ _root_.Set.Ioo (0 : Real) L
    rw [← _root_.MeasureTheory.restrict_Ioo_eq_restrict_Icc]
    exact _root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo
  filter_upwards [haeReg, hq] with r hr hqr
  have hx := hchart ⟨hr.1.le, hr.2.le⟩
  have hG := chartGramOp_spatial_fderiv_eq S.family hS.smoothMetric p (hreg r hr) hx
  have hscalar (i : Fin (Module.finrank Real E)) :
      fderiv Real (scalarOnE (I := I) p (S.scalar (T - (a + r)^2))) (u.toFun r)
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i) =
      mvfderiv (I := I) (S.scalar (T - (a + r)^2)) ((extChartAt I p).symm (u.toFun r))
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) p i
          ((extChartAt I p).symm (u.toFun r))) := by
    rw [DifferentialGeometry.mvfderiv_real_eq_mfderiv]
    have hsrc : (extChartAt I p).symm (u.toFun r) ∈ (chartAt H p).source := by
      simpa only [extChartAt_source] using (extChartAt I p).map_target (interior_subset hx)
    have hright := (extChartAt I p).right_inv (interior_subset hx)
    have hf := scalarSmoothOfSolution (I := I) S (T - (a + r)^2)
    rw [mfderiv_chartBasisVecFiber_of_mdifferentiableAt
      (I := I) p (hf.mdifferentiableAt (by simp)) hsrc
        (by simpa only [hright] using hx) i]
    simp only [DifferentialGeometry.Tensor.Coordinates.partialDeriv, hright]
    rfl
  unfold lChartForce lChartSpatialForceRepresentative
  congr 2
  unfold lChartPositionDerivative
  apply Finset.sum_congr rfl
  intro i _
  rw [hG, hscalar i]
  rw [← hqr]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartForce_ae_eq_lChartSpatialForceRepresentative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lChartForce_ae_eq_lChartSpatialForceRepresentative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartForce_ae_eq_lChartSpatialForceRepresentative ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lChartForce_ae_eq_lChartSpatialForceRepresentative

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

theorem lChartSpatialForceRepresentative_eq_lChartForceRepresentative
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (u : timeH1 E L) (q : Real → E) (r : Real)
    (ht : T - (a + r) ^ 2 ∈ D.regular)
    (hx : u.toFun r ∈ interior (extChartAt I p).target) :
    lChartSpatialForceRepresentative S T a p u q r =
      lChartForceRepresentative S T a p u q r := by
  have hG := chartGramOp_spatial_fderiv_eq S.family hS.smoothMetric p ht hx
  have hR := chartScalCov_eq S hS p ht hx
  unfold lChartSpatialForceRepresentative lChartForceRepresentative
  congr 2
  unfold lChartPositionDerivativeRepresentative
  apply Finset.sum_congr rfl
  intro i _
  rw [hG, hR]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartSpatialForceRepresentative_eq_lChartForceRepresentative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lChartSpatialForceRepresentative_eq_lChartForceRepresentative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lChartSpatialForceRepresentative_eq_lChartForceRepresentative ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lChartSpatialForceRepresentative_eq_lChartForceRepresentative

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

end
