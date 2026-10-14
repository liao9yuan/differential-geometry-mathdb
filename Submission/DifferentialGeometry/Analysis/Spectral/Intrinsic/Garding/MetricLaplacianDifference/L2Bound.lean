import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLaplacianDifference.TimeDependence
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.CompactResolvent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete Real E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

private noncomputable def scalarL2ToH0
    (g : SmoothRiemannianMetric I M) :
    TensorL2 0 0 g →ₗᵢ[Real]
      TensorHs (I := I) (M := M) g 0 0 0 :=
  (tensorHsZeroEquivL2 (I := I) (M := M)
    (tensorResolventL2_isCompactOperator
      (I := I) (M := M) g 0 0)).symm.toLinearIsometry

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.scalarL2ToH0
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.scalarL2ToH0 target :: scope.openDecls } }

noncomputable def lapDiffA20
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (T : D.RegularTime) (s : Real) :
    TensorHs (I := I) (M := M) (g_fam (T : Real)) 0 0 2 →L[Real]
      TensorHs (I := I) (M := M) (g_fam (T : Real)) 0 0 0 :=
  (scalarL2ToH0 (I := I) (M := M)
    (g_fam (T : Real))).toContinuousLinearMap.comp
      (lapDiffA2 (I := I) (M := M) g_fam T s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffA20 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffA20"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffA20 ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffA20

@[simp] theorem lapDiffA20_apply
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (T : D.RegularTime) (s : Real)
    (v : TensorHs (I := I) (M := M) (g_fam (T : Real)) 0 0 2) :
    lapDiffA20 (I := I) (M := M) g_fam T s v =
      (tensorHsZeroEquivL2 (I := I) (M := M)
        (tensorResolventL2_isCompactOperator
          (I := I) (M := M) (g_fam (T : Real)) 0 0)).symm
        (lapDiffA2 (I := I) (M := M) g_fam T s v) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffA20_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffA20_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffA20_apply ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffA20_apply

theorem lapDiffA20_norm
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (T : D.RegularTime) (s : Real) :
    ‖lapDiffA20 (I := I) (M := M) g_fam T s‖ =
      ‖lapDiffA2 (I := I) (M := M) g_fam T s‖ := by
  unfold lapDiffA20
  exact (scalarL2ToH0 (I := I) (M := M)
    (g_fam (T : Real))).norm_toContinuousLinearMap_comp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffA20_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffA20_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffA20_norm ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffA20_norm

theorem lapDiffA20_cont_of
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (T : D.RegularTime) {S : Set Real}
    (hcont : ContinuousOn
      (fun s : Real => lapDiffA2 (I := I) (M := M) g_fam T s) S) :
    ContinuousOn
      (fun s : Real => lapDiffA20 (I := I) (M := M) g_fam T s) S := by
  change ContinuousOn
    (fun s : Real =>
      (scalarL2ToH0 (I := I) (M := M)
        (g_fam (T : Real))).toContinuousLinearMap.comp
          (lapDiffA2 (I := I) (M := M) g_fam T s)) S
  let post :
      (TensorHs (I := I) (M := M) (g_fam (T : Real)) 0 0 2 →L[Real]
          TensorL2 0 0 (g_fam (T : Real))) →L[Real]
        (TensorHs (I := I) (M := M) (g_fam (T : Real)) 0 0 2 →L[Real]
          TensorHs (I := I) (M := M) (g_fam (T : Real)) 0 0 0) :=
    (ContinuousLinearMap.compL Real
      (TensorHs (I := I) (M := M) (g_fam (T : Real)) 0 0 2)
      (TensorL2 0 0 (g_fam (T : Real)))
      (TensorHs (I := I) (M := M) (g_fam (T : Real)) 0 0 0))
      (scalarL2ToH0 (I := I) (M := M)
        (g_fam (T : Real))).toContinuousLinearMap
  exact post.continuous.comp_continuousOn hcont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffA20_cont_of then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffA20_cont_of"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffA20_cont_of ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffA20_cont_of

theorem eventually_lapDiffA20_apply_scalarH2Core
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) :
    ∀ᶠ s in nhds (0 : Real),
      ∀ v : ScalarH2Core (I := I) (M := M) (g_fam (T : Real)),
        tensorHsZeroEquivL2 (I := I) (M := M)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) (g_fam (T : Real)) 0 0)
            (lapDiffA20 (I := I) (M := M) g_fam T s v.1) =
          lapDiffCore (I := I) (M := M) (g_fam (T : Real))
            (g_fam ((T : Real) - s)) v := by
  filter_upwards [eventually_lapDiffA2_apply_scalarH2Core (I := I) (M := M) g_fam hG T] with s hs
  intro v
  rw [lapDiffA20_apply, LinearIsometryEquiv.apply_symm_apply, hs v]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.eventually_lapDiffA20_apply_scalarH2Core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.eventually_lapDiffA20_apply_scalarH2Core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.eventually_lapDiffA20_apply_scalarH2Core ``Submission.DifferentialGeometry.Analysis.Spectral.eventually_lapDiffA20_apply_scalarH2Core

theorem lapDiffA20_graph
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) :
    ∀ᶠ s in nhds (0 : Real),
      ∀ u : TensorHs (I := I) (M := M)
          (g_fam (T : Real)) 0 0 2,
        (u,
            tensorHsZeroEquivL2 (I := I) (M := M)
              (tensorResolventL2_isCompactOperator
                (I := I) (M := M) (g_fam (T : Real)) 0 0)
              (lapDiffA20 (I := I) (M := M) g_fam T s u)) ∈
          closure
            (Set.range fun
              v : ScalarH2Core (I := I) (M := M)
                  (g_fam (T : Real)) =>
                ((v.1 : TensorHs (I := I) (M := M)
                    (g_fam (T : Real)) 0 0 2),
                  lapDiffCore (I := I) (M := M)
                    (g_fam (T : Real))
                    (g_fam ((T : Real) - s)) v)) := by
  filter_upwards [eventually_lapDiffA20_apply_scalarH2Core (I := I) (M := M) g_fam hG T] with s hs
  intro u
  let J := tensorHsZeroEquivL2 (I := I) (M := M)
    (tensorResolventL2_isCompactOperator
      (I := I) (M := M) (g_fam (T : Real)) 0 0)
  let graph :
      TensorHs (I := I) (M := M) (g_fam (T : Real)) 0 0 2 →
        TensorHs (I := I) (M := M) (g_fam (T : Real)) 0 0 2 ×
          TensorL2 0 0 (g_fam (T : Real)) :=
    fun w => (w, J (lapDiffA20 (I := I) (M := M) g_fam T s w))
  have hgraph : Continuous graph :=
    continuous_id.prodMk
      (J.continuous.comp
        (lapDiffA20 (I := I) (M := M) g_fam T s).continuous)
  have hu :
      u ∈ closure
        (ScalarH2Core (I := I) (M := M) (g_fam (T : Real)) :
          Set (TensorHs (I := I) (M := M)
            (g_fam (T : Real)) 0 0 2)) :=
    TensorHs.mem_closure_finiteSupportSubmodule (I := I) (M := M) u
  have hmem := mem_closure_image hgraph.continuousAt hu
  rw [Set.image_eq_range] at hmem
  change graph u ∈ closure
    (Set.range fun
      v : ScalarH2Core (I := I) (M := M) (g_fam (T : Real)) =>
        ((v.1 : TensorHs (I := I) (M := M)
            (g_fam (T : Real)) 0 0 2),
          lapDiffCore (I := I) (M := M) (g_fam (T : Real))
            (g_fam ((T : Real) - s)) v))
  refine closure_mono ?_ hmem
  rintro _ ⟨x, rfl⟩
  let v : ScalarH2Core (I := I) (M := M) (g_fam (T : Real)) :=
    ⟨x.1, x.2⟩
  refine ⟨v, Prod.ext rfl ?_⟩
  exact (hs v).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffA20_graph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffA20_graph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffA20_graph ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffA20_graph

theorem lapDiffA20_pairing_mem_closure
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (T : D.RegularTime) (s : Real)
    (u : TensorHs (I := I) (M := M)
      (g_fam (T : Real)) 0 0 2)
    (w : ScalarH2Core (I := I) (M := M) (g_fam (T : Real)))
    (hgraph :
      (u,
          tensorHsZeroEquivL2 (I := I) (M := M)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) (g_fam (T : Real)) 0 0)
            (lapDiffA20 (I := I) (M := M) g_fam T s u)) ∈
        closure
          (Set.range fun
            v : ScalarH2Core (I := I) (M := M)
                (g_fam (T : Real)) =>
              ((v.1 : TensorHs (I := I) (M := M)
                  (g_fam (T : Real)) 0 0 2),
                lapDiffCore (I := I) (M := M)
                  (g_fam (T : Real))
                  (g_fam ((T : Real) - s)) v))) :
    (u,
        _root_.Inner.inner Real
          (tensorHsZeroEquivL2 (I := I) (M := M)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) (g_fam (T : Real)) 0 0)
            (lapDiffA20 (I := I) (M := M) g_fam T s u))
          (SmoothCcTensor.toL2
            (tensorHsSmoothRepr (I := I) (M := M) w.1 w.2))) ∈
      closure
        (Set.range fun
          v : ScalarH2Core (I := I) (M := M)
              (g_fam (T : Real)) =>
            ((v.1 : TensorHs (I := I) (M := M)
                (g_fam (T : Real)) 0 0 2),
              ∫ x, (ΔG (I := I) (g_fam ((T : Real) - s))
                      ⟨reprScalar0 (I := I) (M := M) v.1 v.2,
                        reprScalar0_smooth (I := I) (M := M) v.1 v.2⟩ x -
                    ΔG (I := I) (g_fam (T : Real))
                      ⟨reprScalar0 (I := I) (M := M) v.1 v.2,
                        reprScalar0_smooth (I := I) (M := M) v.1 v.2⟩ x) *
                  reprScalar0 (I := I) (M := M) w.1 w.2 x
                ∂(riemannianVolumeMeasure (I := I) (M := M)
                  (g_fam (T : Real))))) := by
  let J := tensorHsZeroEquivL2 (I := I) (M := M)
    (tensorResolventL2_isCompactOperator
      (I := I) (M := M) (g_fam (T : Real)) 0 0)
  let test : TensorL2 0 0 (g_fam (T : Real)) :=
    SmoothCcTensor.toL2
      (tensorHsSmoothRepr (I := I) (M := M) w.1 w.2)
  let eval :
      (TensorHs (I := I) (M := M) (g_fam (T : Real)) 0 0 2 ×
          TensorL2 0 0 (g_fam (T : Real))) →
        TensorHs (I := I) (M := M) (g_fam (T : Real)) 0 0 2 × Real :=
    fun p => (p.1, _root_.Inner.inner Real p.2 test)
  have heval : Continuous eval :=
    continuous_fst.prodMk
      (((innerSL Real).flip test).continuous.comp continuous_snd)
  have hmem := mem_closure_image heval.continuousAt hgraph
  change eval (u, J (lapDiffA20 (I := I) (M := M) g_fam T s u)) ∈
    closure
      (Set.range fun
        v : ScalarH2Core (I := I) (M := M) (g_fam (T : Real)) =>
          ((v.1 : TensorHs (I := I) (M := M)
              (g_fam (T : Real)) 0 0 2),
            ∫ x, (ΔG (I := I) (g_fam ((T : Real) - s))
                    ⟨reprScalar0 (I := I) (M := M) v.1 v.2,
                      reprScalar0_smooth (I := I) (M := M) v.1 v.2⟩ x -
                  ΔG (I := I) (g_fam (T : Real))
                    ⟨reprScalar0 (I := I) (M := M) v.1 v.2,
                      reprScalar0_smooth (I := I) (M := M) v.1 v.2⟩ x) *
                reprScalar0 (I := I) (M := M) w.1 w.2 x
              ∂(riemannianVolumeMeasure (I := I) (M := M)
                (g_fam (T : Real)))))
  refine closure_mono ?_ hmem
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  refine ⟨v, Prod.ext rfl ?_⟩
  simpa only [eval, test] using
    (lapDiffCore_pair (I := I) (M := M)
      (g_fam (T : Real)) (g_fam ((T : Real) - s)) v w).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffA20_pairing_mem_closure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffA20_pairing_mem_closure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffA20_pairing_mem_closure ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffA20_pairing_mem_closure

theorem lapDiffA20_bound
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) :
    ∃ omega : Real → Real,
      _root_.Filter.Tendsto omega (nhds 0) (nhds 0) ∧
      ∀ᶠ s in nhds (0 : Real),
        ∀ v : TensorHs (I := I) (M := M)
            (g_fam (T : Real)) 0 0 2,
          (Function.support v.coeff).Finite →
            ‖lapDiffA20 (I := I) (M := M) g_fam T s v‖ ≤
              omega s * ‖v‖ := by
  obtain ⟨omega, homega, hbound⟩ :=
    lapDiffA2_bound (I := I) (M := M) g_fam hG T
  refine ⟨omega, homega, ?_⟩
  filter_upwards [hbound] with s hs
  intro v hv
  simpa only [lapDiffA20_apply,
    LinearIsometryEquiv.norm_map] using hs v hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffA20_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffA20_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffA20_bound ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffA20_bound

theorem lapDiffA20_zero
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) :
    Tendsto (fun s : Real => ‖lapDiffA20 (I := I) (M := M) g_fam T s‖)
      (nhds 0) (nhds 0) := by
  have heq :
      (fun s : Real => ‖lapDiffA20 (I := I) (M := M) g_fam T s‖) =
        fun s : Real => ‖lapDiffA2 (I := I) (M := M) g_fam T s‖ := by
    funext s
    exact lapDiffA20_norm (I := I) (M := M) g_fam T s
  rw [heq]
  exact lapDiffA2_zero (I := I) (M := M) g_fam hG T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lapDiffA20_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lapDiffA20_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lapDiffA20_zero ``Submission.DifferentialGeometry.Analysis.Spectral.lapDiffA20_zero

end Spectral
end Analysis
end DifferentialGeometry

end
