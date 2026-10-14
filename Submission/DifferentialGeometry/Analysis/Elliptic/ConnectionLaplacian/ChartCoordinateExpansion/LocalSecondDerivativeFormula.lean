import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.ChartComponentFrameTrace
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.LocalizedFrame.Coordinates
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Iterates
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.SecondCovDerivExpansion.LocalSecondCovariantDerivativeProjection
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.SmoothExtensionExpansion
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Tensor
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private noncomputable def principalSecondDerivSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
      weightedInvGramEuclid (I := I) (M := M) g α k l y *
        euclidPartial (E := E) l
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.principalSecondDerivSum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.principalSecondDerivSum target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma principalSecondDerivSum_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (principalSecondDerivSum (I := I) (M := M) g r s α T₀ Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hk : ∀ k : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)))
        (chartTargetEuclid (I := I) (M := M) α) := fun k =>
    euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M) g r s T₀ α k Idx Jdx
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hkl : ∀ k l : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (euclidPartial (E := E) l
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))))
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro k l
    have hu := hk k
    have hsucc : ContDiffOn ℝ ((∞ : WithTop ℕ∞) + 1)
        (euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)))
        (chartTargetEuclid (I := I) (M := M) α) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl]; exact hu
    have hfw : ContDiffOn ℝ ∞
        (fderivWithin ℝ
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)))
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
      ((contDiffOn_succ_iff_fderivWithin hopen.uniqueDiffOn).mp hsucc).2.2
    have hfderiv : ContDiffOn ℝ ∞
        (fun z => fderiv ℝ
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) z)
        (chartTargetEuclid (I := I) (M := M) α) := by
      refine hfw.congr (fun z hz => ?_)
      exact (fderivWithin_of_isOpen (f :=
        euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)))
        (𝕜 := ℝ) hopen hz).symm
    have hcomp : ContDiffOn ℝ ∞
        ((fun L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] ℝ =>
            L (EuclideanSpace.single l 1)) ∘
          (fun z => fderiv ℝ
            (euclidPartial (E := E) k
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) z))
        (chartTargetEuclid (I := I) (M := M) α) :=
      (ContinuousLinearMap.apply ℝ ℝ
        (EuclideanSpace.single l 1)).contDiff.comp_contDiffOn hfderiv
    refine hcomp.congr (fun z _ => ?_)
    rfl
  have hsum_pair : ∀ k l : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun y =>
          weightedInvGramEuclid (I := I) (M := M) g α k l y *
            euclidPartial (E := E) l
              (euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y)
        (chartTargetEuclid (I := I) (M := M) α) := fun k l =>
    (weightedInvGramEuclid_contDiffOn (I := I) (M := M) g α k l).mul (hkl k l)
  have hsum_inner : ∀ k : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun y =>
          ∑ l : Fin (Module.finrank ℝ E),
            weightedInvGramEuclid (I := I) (M := M) g α k l y *
              euclidPartial (E := E) l
                (euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y)
        (chartTargetEuclid (I := I) (M := M) α) := fun k =>
    ContDiffOn.sum (fun l _ => hsum_pair k l)
  exact ContDiffOn.sum (fun k _ => hsum_inner k)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.principalSecondDerivSum_contDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.principalSecondDerivSum_contDiffOn target :: scope.openDecls } }

private noncomputable def chartPushed_rawConnLapComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  chartPushedRaw I α
    (tensorChartComponentRaw (I := I) (M := M) g r s
      (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.chartPushed_rawConnLapComponent
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.chartPushed_rawConnLapComponent target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma chartPushed_rawConnLapComponent_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (chartPushed_rawConnLapComponent (I := I) (M := M) g r s α T₀ Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
  chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M) g r s
    (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.chartPushed_rawConnLapComponent_contDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.chartPushed_rawConnLapComponent_contDiffOn target :: scope.openDecls } }

private noncomputable def lowerOrderCorrection
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    chartPushed_rawConnLapComponent (I := I) (M := M) g r s α T₀ Idx Jdx y -
      principalSecondDerivSum (I := I) (M := M) g r s α T₀ Idx Jdx y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.lowerOrderCorrection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.lowerOrderCorrection target :: scope.openDecls } }

omit [CompactSpace M] [SigmaCompactSpace M] in
private lemma lowerOrderCorrection_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (lowerOrderCorrection (I := I) (M := M) g r s α T₀ Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (chartPushed_rawConnLapComponent_contDiffOn (I := I) (M := M) g r s α T₀
    Idx Jdx).sub
    (principalSecondDerivSum_contDiffOn (I := I) (M := M) g r s α T₀ Idx Jdx)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.lowerOrderCorrection_contDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.lowerOrderCorrection_contDiffOn target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma chartPushed_rawConnLapComponent_eq_principal_add_LO
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    chartPushed_rawConnLapComponent (I := I) (M := M) g r s α T₀ Idx Jdx y =
      principalSecondDerivSum (I := I) (M := M) g r s α T₀ Idx Jdx y +
        lowerOrderCorrection (I := I) (M := M) g r s α T₀ Idx Jdx y := by
  unfold lowerOrderCorrection
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.chartPushed_rawConnLapComponent_eq_principal_add_LO
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.chartPushed_rawConnLapComponent_eq_principal_add_LO target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma chartPushed_rawConnLapComponent_apply_of_good
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartPushed_rawConnLapComponent (I := I) (M := M) g r s α T₀ Idx Jdx
        ((toEuclidean (E := E)) ((extChartAt I α) b)) =
      tensorChartComponentRaw (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b := by
  classical
  unfold chartPushed_rawConnLapComponent
  have hb_source : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  have hb_target : (extChartAt I α) b ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hb_source
  have hy_chart : (toEuclidean (E := E)) ((extChartAt I α) b) ∈
      chartTargetEuclid (I := I) (M := M) α :=
    ⟨(extChartAt I α) b, hb_target, rfl⟩
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy_chart]
  have hsymm_te :
      (toEuclidean (E := E)).symm
        ((toEuclidean (E := E)) ((extChartAt I α) b)) =
        (extChartAt I α) b :=
    (toEuclidean (E := E)).symm_apply_apply _
  have hleft_inv : (extChartAt I α).symm ((extChartAt I α) b) = b :=
    (extChartAt I α).left_inv hb_source
  rw [hsymm_te, hleft_inv]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.chartPushed_rawConnLapComponent_apply_of_good
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.chartPushed_rawConnLapComponent_apply_of_good target :: scope.openDecls } }

omit [CompactSpace M] in
theorem tensorChartComponentRaw_rawTensorConnLap_eq_chart_α_coord_formula
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b₀ : M}
    (hb₀ : b₀ ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      chartLeviCivitaGoodSet (I := I) α) :
    ∃ U : Set M, IsOpen U ∧ b₀ ∈ U ∧
      U ⊆ chartLeviCivitaGoodSet (I := I) α ∧
    ∃ (Coeff_2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
                  EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ),
    ∃ (Coeff_LO : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ),
      (∀ k l, ContDiffOn ℝ ∞ (Coeff_2 k l)
        (chartTargetEuclid (I := I) (M := M) α)) ∧
      (ContDiffOn ℝ ∞ Coeff_LO (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∀ b ∈ U,
        tensorChartComponentRaw (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b =
          (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            Coeff_2 k l ((toEuclidean (E := E)) ((extChartAt I α) b)) *
              euclidPartial (E := E) l
                (euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)))
                ((toEuclidean (E := E)) ((extChartAt I α) b))) +
          Coeff_LO ((toEuclidean (E := E)) ((extChartAt I α) b)) := by
  classical
  refine ⟨chartLeviCivitaGoodSet (I := I) α,
    chartLeviCivitaGoodSet_isOpen (I := I) α, hb₀.2, Set.Subset.rfl, ?_⟩
  refine ⟨fun k l => weightedInvGramEuclid (I := I) (M := M) g α k l, ?_, ?_, ?_, ?_⟩
  · exact lowerOrderCorrection (I := I) (M := M) g r s α T₀ Idx Jdx
  · intro k l
    exact weightedInvGramEuclid_contDiffOn (I := I) (M := M) g α k l
  · exact lowerOrderCorrection_contDiffOn (I := I) (M := M) g r s α T₀ Idx Jdx
  · intro b hb
    set y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
      (toEuclidean (E := E)) ((extChartAt I α) b) with hy_def
    have hLHS_eq :
        tensorChartComponentRaw (I := I) (M := M) g r s
            (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b =
          chartPushed_rawConnLapComponent (I := I) (M := M) g r s α T₀ Idx Jdx y :=
      (chartPushed_rawConnLapComponent_apply_of_good
        (I := I) (M := M) g r s α T₀ Idx Jdx hb).symm
    rw [hLHS_eq]
    rw [chartPushed_rawConnLapComponent_eq_principal_add_LO
        (I := I) (M := M) g r s α T₀ Idx Jdx y]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorChartComponentRaw_rawTensorConnLap_eq_chart_α_coord_formula then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorChartComponentRaw_rawTensorConnLap_eq_chart_α_coord_formula"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorChartComponentRaw_rawTensorConnLap_eq_chart_α_coord_formula ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorChartComponentRaw_rawTensorConnLap_eq_chart_α_coord_formula

end Elliptic
end Analysis
end DifferentialGeometry

end
