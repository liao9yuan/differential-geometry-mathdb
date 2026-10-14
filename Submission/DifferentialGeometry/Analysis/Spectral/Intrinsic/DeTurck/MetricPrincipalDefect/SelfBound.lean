import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MetricPrincipalDefect.Defs
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.CometricTraceSelf
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.FiberNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

def phiSelfC (i : ℕ) : ℝ :=
  if i = 0 then 34 * (Module.finrank ℝ E : ℝ) ^ 6 else 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.phiSelfC then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.phiSelfC"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.phiSelfC ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.phiSelfC

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem phiSelfC_nonneg (i : ℕ) : 0 ≤ phiSelfC (E := E) i := by
  by_cases hi : i = 0
  · simp only [phiSelfC, hi, if_pos]
    positivity
  · simp [phiSelfC, hi]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.phiSelfC_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.phiSelfC_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.phiSelfC_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.phiSelfC_nonneg

private def selfTraceC (i : ℕ) : ℝ :=
  if i = 0 then (Module.finrank ℝ E : ℝ) ^ 6 else 0

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.selfTraceC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.selfTraceC target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem phiSelfC_eq (i : ℕ) :
    phiSelfC (E := E) i = 34 * selfTraceC (E := E) i := by
  by_cases hi : i = 0 <;> simp [phiSelfC, selfTraceC, hi]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.phiSelfC_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.phiSelfC_eq target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem selfTraceC_nonneg (i : ℕ) :
    0 ≤ selfTraceC (E := E) i := by
  by_cases hi : i = 0
  · simp only [selfTraceC, hi, if_pos]
    positivity
  · simp [selfTraceC, hi]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.selfTraceC_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.selfTraceC_nonneg target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
private theorem doubleTrace_grid
    (g : SmoothRiemannianMetric I M) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x
        ((iteratedCovGrad (I := I) g 4 2 i
          (cometricDoubleTraceField (I := I) g 2)).toSection x) ≤
      selfTraceC (E := E) i := by
  match i with
  | 0 =>
      rw [iteratedCovGrad_zero]
      simpa only [selfTraceC, if_pos] using
        (cometricTrace_riemannianFiberNormSq (I := I) (M := M) g x)
  | (i' + 1) =>
      rw [iteratedCovGrad_eq_zero_of_covGrad_eq_zero
        (I := I) (M := M) g 4 2
        (cometricDoubleTraceField (I := I) g 2)
        (cometricDoubleTraceField_covGrad_eq_zero (I := I) g 2) i']
      rw [show ((0 : SmoothCcTensor g 4 (2 + (i' + 1))).toSection x) =
          (0 : TensorRSSpace 4 (2 + (i' + 1)) I x) from by
        rw [SmoothCcTensor.toSection_zero]
        rfl]
      rw [riemannianFiberNormSq_zero]
      simp [selfTraceC]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.doubleTrace_grid
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.doubleTrace_grid target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem traceSelf_eq (g : SmoothRiemannianMetric I M) :
    traceHessianCoeff (I := I) (M := M) g g =
      reindexCoefficientInputSlots (I := I) (M := M) g 4 2
        (cometricDoubleTraceField (I := I) g 2) traceHessianSlotPerm := by
  apply DifferentialGeometry.Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [traceHessianCoeff_toSection, reindexCoefficientInputSlots_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [reindexCoefficientInputSlotsFiber_apply, cometricDoubleTraceField_toSection,
    traceHessianFib, ContinuousLinearMap.comp_apply, domDomCongrFib_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.traceSelf_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.traceSelf_eq target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem pureSelf_eq (g : SmoothRiemannianMetric I M) :
    cometricDoubleTraceCoefficient (I := I) (M := M) g g =
      cometricDoubleTraceField (I := I) g 2 := by
  apply DifferentialGeometry.Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [cometricDoubleTraceCoefficient_toSection, cometricDoubleTraceField_toSection]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.pureSelf_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.pureSelf_eq target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
private theorem traceSelf_grid
    (g : SmoothRiemannianMetric I M) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x
        ((iteratedCovGrad (I := I) g 4 2 i
          (traceHessianCoeff (I := I) (M := M) g g)).toSection x) ≤
      selfTraceC (E := E) i := by
  rw [traceSelf_eq (I := I) (M := M) g]
  rw [DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_reindexCoefficientInputSlots_eq
    (I := I) (M := M) g 4 2
    (cometricDoubleTraceField (I := I) g 2) traceHessianSlotPerm i x]
  exact doubleTrace_grid (I := I) (M := M) g i x

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.traceSelf_grid
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.traceSelf_grid target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
private theorem pureSelf_grid
    (g : SmoothRiemannianMetric I M) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x
        ((iteratedCovGrad (I := I) g 4 2 i
          (cometricDoubleTraceCoefficient (I := I) (M := M) g g)).toSection x) ≤
      selfTraceC (E := E) i := by
  rw [pureSelf_eq (I := I) (M := M) g]
  exact doubleTrace_grid (I := I) (M := M) g i x

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.pureSelf_grid
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.pureSelf_grid target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise
      (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise
      (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DifferentialGeometry
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DifferentialGeometry.Analysis
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DifferentialGeometry.Analysis.Elliptic
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
private theorem ricciSelf_riemannianFiberNormSq_le
    (g : SmoothRiemannianMetric I M) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x
        ((iteratedCovGrad (I := I) g 4 2 i
          (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g g)).toSection x) ≤
      (10 / 4 : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x
          ((iteratedCovGrad (I := I) g 4 2 i
            (cometricDoubleTraceField (I := I) g 2)).toSection x) := by
  classical
  set R3 := cometricDoubleTraceField (I := I) g 2 with hR3
  set R1 := reindexCoefficientInputSlots (I := I) (M := M) g 4 2 R3 koszulSlotPerm with hR1
  set R2 := reindexCoefficientInputSlots (I := I) (M := M) g 4 2
    (rsDomDomCongrSection (I := I) (M := M) g 4 2
      (Equiv.swap (0 : Fin 2) 1) R3) koszulSlotPerm with hR2
  set A := ricciDeTurckPrincipalCoefficient (I := I) (M := M) g g with hA
  have hid : A + A = R1 + R2 - R3 := by
    rw [hA, hR1, hR2, hR3, ricciSelf_eq (I := I) (M := M) g]
    module
  have hiter :
      iteratedCovGrad (I := I) g 4 2 i A +
          iteratedCovGrad (I := I) g 4 2 i A =
        iteratedCovGrad (I := I) g 4 2 i R1 +
          iteratedCovGrad (I := I) g 4 2 i R2 -
          iteratedCovGrad (I := I) g 4 2 i R3 := by
    rw [← iteratedCovGrad_add, hid, iteratedCovGrad_sub, iteratedCovGrad_add]
  have hsec :
      (iteratedCovGrad (I := I) g 4 2 i A).toSection x +
          (iteratedCovGrad (I := I) g 4 2 i A).toSection x =
        (iteratedCovGrad (I := I) g 4 2 i R1).toSection x +
          (iteratedCovGrad (I := I) g 4 2 i R2).toSection x -
          (iteratedCovGrad (I := I) g 4 2 i R3).toSection x := by
    have hcg := congrArg (fun T : SmoothCcTensor g 4 (2 + i) =>
      (T.toSection x : TensorRSSpace 4 (2 + i) I x)) hiter
    simpa only [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub,
      ContMDiffSection.coe_add, ContMDiffSection.coe_sub,
      Pi.add_apply, Pi.sub_apply] using hcg
  set PA0 := (iteratedCovGrad (I := I) g 4 2 i A).toSection x with hPA0
  set PA := (iteratedCovGrad (I := I) g 4 2 i R1).toSection x with hPA
  set PB := (iteratedCovGrad (I := I) g 4 2 i R2).toSection x with hPB
  set PC := (iteratedCovGrad (I := I) g 4 2 i R3).toSection x with hPC
  have hbA :
      riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x PA =
        riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x PC := by
    rw [hPA, hPC, hR1]
    exact DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_reindexCoefficientInputSlots_eq
      (I := I) (M := M) g 4 2 R3 koszulSlotPerm i x
  have hbB :
      riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x PB =
        riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x PC := by
    rw [hPB, hPC, hR2]
    rw [DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_reindexCoefficientInputSlots_eq
      (I := I) (M := M) g 4 2
      (rsDomDomCongrSection (I := I) (M := M) g 4 2
        (Equiv.swap (0 : Fin 2) 1) R3) koszulSlotPerm i x]
    exact DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr
      (I := I) (M := M) g 4 2 (Equiv.swap (0 : Fin 2) 1) R3
      (rsDomDomCongrSection (I := I) (M := M) g 4 2
        (Equiv.swap (0 : Fin 2) 1) R3)
      (fun y d => by
        rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) i x
  have hnegC :
      riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x (-PC) =
        riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x PC := by
    rw [← neg_one_smul ℝ PC, DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul (I := I) (M := M)]
    norm_num
  have hsum :
      riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x
          (PA + PB - PC) ≤
        4 * riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x PC +
          4 * riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x PC +
          2 * riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x PC := by
    have h1 := riemannianFiberNormSq_add_le
      (I := I) (M := M) g 4 (2 + i) x (PA + PB) (-PC)
    have h2 := riemannianFiberNormSq_add_le
      (I := I) (M := M) g 4 (2 + i) x PA PB
    rw [hnegC] at h1
    rw [show PA + PB - PC = (PA + PB) + (-PC) from sub_eq_add_neg _ _]
    linarith [h1, h2, hbA, hbB,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 4 (2 + i) x PA,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 4 (2 + i) x PB,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 4 (2 + i) x PC]
  have hlhs4 :
      riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x (PA0 + PA0) =
        4 * riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x PA0 := by
    rw [show PA0 + PA0 = (2 : ℝ) • PA0 from (two_smul ℝ PA0).symm,
      DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul (I := I) (M := M)]
    norm_num
  have hkey :
      4 * riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x PA0 ≤
        10 * riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x PC := by
    rw [← hlhs4, hsec]
    linarith [hsum]
  linarith [hkey,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 4 (2 + i) x PC]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.ricciSelf_riemannianFiberNormSq_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.ricciSelf_riemannianFiberNormSq_le target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
private theorem ricciSelf_grid
    (g : SmoothRiemannianMetric I M) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x
        ((iteratedCovGrad (I := I) g 4 2 i
          (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g g)).toSection x) ≤
      selfTraceC (E := E) i := by
  match i with
  | 0 =>
      let z : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
        fun _ => 0
      have htie : ∀ (y : M) (v w : TangentSpace I y),
          g.inner y v w = g.inner y v w + z y v w := by
        intro y v w
        simp only [z, zero_apply, add_zero]
      have hz : gFibreOpBound (I := I) (M := M) g z 0 := by
        intro y v w
        simp only [z, zero_apply, abs_zero, _root_.MulZeroClass.zero_mul, le_refl]
      have hricci := riemannianFiberNormSq_ricciDeTurckPrincipalCoefficientFiber_le
        (I := I) (M := M) g g z htie
          (show (0 : ℝ) < 1 by norm_num) (show (0 : ℝ) ≤ 0 by norm_num) hz x
      rw [iteratedCovGrad_zero, ricciDeTurckPrincipalCoefficient_toSection]
      refine hricci.trans (le_of_eq ?_)
      simp only [selfTraceC, if_pos, sub_zero, div_one, mul_one]
      ring
  | (i' + 1) =>
      have hmain := ricciSelf_riemannianFiberNormSq_le (I := I) (M := M) g (i' + 1) x
      have htrace := doubleTrace_grid (I := I) (M := M) g (i' + 1) x
      have htrace_nn := riemannianFiberNormSq_nonneg
        (I := I) (M := M) g 4 (2 + (i' + 1)) x
          ((iteratedCovGrad (I := I) g 4 2 (i' + 1)
            (cometricDoubleTraceField (I := I) g 2)).toSection x)
      simp only [selfTraceC, Nat.succ_ne_zero, if_false] at htrace ⊢
      linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.ricciSelf_grid
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.ricciSelf_grid target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
theorem phiSelf_grid
    (g : SmoothRiemannianMetric I M) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x
        ((iteratedCovGrad (I := I) g 4 2 i
          (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g -
            cometricDoubleTraceCoefficient (I := I) (M := M) g g)).toSection x) ≤
      phiSelfC (E := E) i := by
  classical
  let ρA : Equiv.Perm (Fin 4) :=
    traceHessianSlotPerm⁻¹ * deTurckLieSecondOrderDivSlotPermA
  let ρB : Equiv.Perm (Fin 4) :=
    traceHessianSlotPerm⁻¹ * deTurckLieSecondOrderDivSlotPermAT
  set A := (iteratedCovGrad (I := I) g 4 2 i
    (reindexCoefficientInputSlots (I := I) (M := M) g 4 2
      (traceHessianCoeff (I := I) (M := M) g g) ρA)).toSection x with hA
  set B := (iteratedCovGrad (I := I) g 4 2 i
    (reindexCoefficientInputSlots (I := I) (M := M) g 4 2
      (traceHessianCoeff (I := I) (M := M) g g) ρB)).toSection x with hB
  set R := (iteratedCovGrad (I := I) g 4 2 i
    (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g g)).toSection x with hR
  set P := (iteratedCovGrad (I := I) g 4 2 i
    (cometricDoubleTraceCoefficient (I := I) (M := M) g g)).toSection x with hP
  have hsec :
      (iteratedCovGrad (I := I) g 4 2 i
        (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g -
          cometricDoubleTraceCoefficient (I := I) (M := M) g g)).toSection x =
        A + B - (R + R) - P := by
    rw [deTurckMetricPrincipalDefectTotal_eq_reindex (I := I) (M := M) g g,
      iteratedCovGrad_sub, iteratedCovGrad_sub,
      iteratedCovGrad_add, iteratedCovGrad_add,
      SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub,
      SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_add,
      ContMDiffSection.coe_sub, ContMDiffSection.coe_sub,
      ContMDiffSection.coe_add, ContMDiffSection.coe_add,
      Pi.sub_apply, Pi.sub_apply, Pi.add_apply, Pi.add_apply]
  have hAbound :
      riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x A ≤
        selfTraceC (E := E) i := by
    rw [hA, DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_reindexCoefficientInputSlots_eq
      (I := I) (M := M) g 4 2
      (traceHessianCoeff (I := I) (M := M) g g) ρA i x]
    exact traceSelf_grid (I := I) (M := M) g i x
  have hBbound :
      riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x B ≤
        selfTraceC (E := E) i := by
    rw [hB, DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_reindexCoefficientInputSlots_eq
      (I := I) (M := M) g 4 2
      (traceHessianCoeff (I := I) (M := M) g g) ρB i x]
    exact traceSelf_grid (I := I) (M := M) g i x
  have hRbound :
      riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x R ≤
        selfTraceC (E := E) i := by
    rw [hR]
    exact ricciSelf_grid (I := I) (M := M) g i x
  have hPbound :
      riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x P ≤
        selfTraceC (E := E) i := by
    rw [hP]
    exact pureSelf_grid (I := I) (M := M) g i x
  rw [hsec, phiSelfC_eq (E := E) i]
  have hAB := riemannianFiberNormSq_add_le
    (I := I) (M := M) g 4 (2 + i) x A B
  have hRR := riemannianFiberNormSq_add_le
    (I := I) (M := M) g 4 (2 + i) x R R
  have hmid := riemannianFiberNormSq_sub_le
    (I := I) (M := M) g 4 (2 + i) x (A + B) (R + R)
  have hout := riemannianFiberNormSq_sub_le
    (I := I) (M := M) g 4 (2 + i) x (A + B - (R + R)) P
  linarith [hAB, hRR, hmid, hout, hAbound, hBbound, hRbound, hPbound,
    selfTraceC_nonneg (E := E) i]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.phiSelf_grid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.phiSelf_grid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.phiSelf_grid ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.phiSelf_grid

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
