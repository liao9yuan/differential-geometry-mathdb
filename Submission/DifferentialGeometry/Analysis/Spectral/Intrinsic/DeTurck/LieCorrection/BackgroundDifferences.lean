import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LieCorrection.TameBounds
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.ApplicationJets

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroFiberOperators
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
private lemma endoSlotZeroCcTensor_sub (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ s (A - B) =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ s A -
        endoSlotZeroCcTensor (I := I) (M := M) g₀ s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((endoSlotZeroCcTensor (I := I) (M := M) g₀ s A -
        endoSlotZeroCcTensor (I := I) (M := M) g₀ s B).toSection x) =
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ s A).toSection x -
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ s B).toSection x from by
    rw [SmoothCcTensor.toSection_sub]
    rfl]
  rw [sub_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A - B) x) = A x - B x from by
    rw [ContMDiffSection.coe_sub]
    rfl]
  rw [slotInsertEndoFib_sub_left, sub_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.endoSlotZeroCcTensor_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.endoSlotZeroCcTensor_sub target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
private lemma rsDomDomCongrSection_sub (g₀ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 2)) (X Y : SmoothCcTensor g₀ 2 2) :
    rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 σ (X - Y) =
      rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 σ X -
        rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 σ Y := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  change tensorRSDomDomCongr σ ((X - Y).toSection x) =
    tensorRSDomDomCongr σ (X.toSection x) - tensorRSDomDomCongr σ (Y.toSection x)
  rw [SmoothCcTensor.toSection_sub]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.rsDomDomCongrSection_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.rsDomDomCongrSection_sub target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
private lemma reindexCoefficientInputSlots_sub (g₀ : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g₀ 2 2) (ρ : Equiv.Perm (Fin 2)) :
    reindexCoefficientInputSlots (I := I) (M := M) g₀ 2 2 (A - B) ρ =
      reindexCoefficientInputSlots (I := I) (M := M) g₀ 2 2 A ρ -
        reindexCoefficientInputSlots (I := I) (M := M) g₀ 2 2 B ρ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    reindexCoefficientInputSlots_toSection, reindexCoefficientInputSlots_toSection, reindexCoefficientInputSlots_toSection,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  apply ContinuousLinearMap.ext
  intro D
  rw [sub_apply, reindexCoefficientInputSlotsFiber_apply, reindexCoefficientInputSlotsFiber_apply,
    reindexCoefficientInputSlotsFiber_apply, sub_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.reindexCoefficientInputSlots_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.reindexCoefficientInputSlots_sub target :: scope.openDecls } }

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lieCorrectionZeroNEndoSec_sub_insert_eq_lieCorrectionZeroCdVField_sub
    (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ gB -
          lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ g₀) =
      lieCorrectionZeroCdVField (I := I) (M := M) g₀ g₁ g₀ -
        lieCorrectionZeroCdVField (I := I) (M := M) g₀ g₁ gB := by
  rw [endoSlotZeroCcTensor_sub (I := I) (M := M) g₀ 0,
    lieCorrectionZero_NEndoIns_decomp (I := I) (M := M) g₀ g₁ gB,
    lieCorrectionZero_NEndoIns_decomp (I := I) (M := M) g₀ g₁ g₀]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroNEndoSec_sub_insert_eq_lieCorrectionZeroCdVField_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroNEndoSec_sub_insert_eq_lieCorrectionZeroCdVField_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroNEndoSec_sub_insert_eq_lieCorrectionZeroCdVField_sub ``Submission.DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroNEndoSec_sub_insert_eq_lieCorrectionZeroCdVField_sub

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem lieCorrectionZeroInsertionField_sub_eq_nEndoInsert
    (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lieCorrectionZeroInsertionField (I := I) (M := M) g₀ g₁ gB -
        lieCorrectionZeroInsertionField (I := I) (M := M) g₀ g₁ g₀ =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ gB -
            lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ g₀)
        + reindexCoefficientInputSlots (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2
              (Equiv.swap (0 : Fin 2) 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                (lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ gB -
                  lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ g₀)))
            (Equiv.swap (0 : Fin 2) 1) := by
  rw [endoSlotZeroCcTensor_sub (I := I) (M := M) g₀ 1,
    rsDomDomCongrSection_sub (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 2) 1),
    reindexCoefficientInputSlots_sub (I := I) (M := M) g₀]
  change (_ + _) - (_ + _) = _
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroInsertionField_sub_eq_nEndoInsert then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroInsertionField_sub_eq_nEndoInsert"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroInsertionField_sub_eq_nEndoInsert ``Submission.DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroInsertionField_sub_eq_nEndoInsert

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroVFlat_sub_eq_trace_comp_kappa_sub
    (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lieCorrectionZeroVFlat (I := I) (M := M) g₀ g₁ g₀ -
        lieCorrectionZeroVFlat (I := I) (M := M) g₀ g₁ gB =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1
        (lieCorrectionZeroPureDT (I := I) (M := M) g₀ g₁ 1)
        (lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g₀ -
          lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ gB) := by
  rw [ccOperatorFieldComp_sub_right]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroVFlat_sub_eq_trace_comp_kappa_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroVFlat_sub_eq_trace_comp_kappa_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroVFlat_sub_eq_trace_comp_kappa_sub ``Submission.DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroVFlat_sub_eq_trace_comp_kappa_sub

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroIVField_sub_eq_trace_comp_slotExtend_vflat_sub
    (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lieCorrectionZeroIVField (I := I) (M := M) g₀ g₁ g₀ -
        lieCorrectionZeroIVField (I := I) (M := M) g₀ g₁ gB =
      ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 1
        (lieCorrectionZeroTr (I := I) (M := M) g₀ g₁ 1 lieCorrectionZeroIVPerm)
        (slotExtendIter (I := I) (M := M) g₀ 0 1 2
          (lieCorrectionZeroVFlat (I := I) (M := M) g₀ g₁ g₀ -
            lieCorrectionZeroVFlat (I := I) (M := M) g₀ g₁ gB)) := by
  rw [slotExtendIter_sub, ccOperatorFieldComp_sub_right]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroIVField_sub_eq_trace_comp_slotExtend_vflat_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroIVField_sub_eq_trace_comp_slotExtend_vflat_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroIVField_sub_eq_trace_comp_slotExtend_vflat_sub ``Submission.DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroIVField_sub_eq_trace_comp_slotExtend_vflat_sub

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroCdVField_sub_eq_comp_connectionDifference
    (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lieCorrectionZeroCdVField (I := I) (M := M) g₀ g₁ g₀ -
        lieCorrectionZeroCdVField (I := I) (M := M) g₀ g₁ gB =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 2 1
        (lieCorrectionZeroIVField (I := I) (M := M) g₀ g₁ g₀ -
          lieCorrectionZeroIVField (I := I) (M := M) g₀ g₁ gB)
        (connectionDifferenceSection (I := I) g₁ g₀) := by
  rw [operatorFieldComposition_sub_left]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroCdVField_sub_eq_comp_connectionDifference then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroCdVField_sub_eq_comp_connectionDifference"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroCdVField_sub_eq_comp_connectionDifference ``Submission.DifferentialGeometry.Analysis.Spectral.lieCorrectionZeroCdVField_sub_eq_comp_connectionDifference

end DifferentialGeometry.Analysis.Spectral

end
