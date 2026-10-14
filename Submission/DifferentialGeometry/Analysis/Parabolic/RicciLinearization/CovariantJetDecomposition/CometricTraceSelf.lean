import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.OperatorField.Application
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.SymmetricCoefficientBounds
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.KoszulSecondCovariantDerivative
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.CovariantOrderCoefficient.PassZero

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry.Analysis.Parabolic.TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem cometricTrace_riemannianFiberNormSq
    (g : SmoothRiemannianMetric I M) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        ((cometricDoubleTraceField (I := I) g 2).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 6 := by
  let z : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
    fun _ => 0
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w = g.inner y v w + z y v w := by
    intro y v w
    simp only [z, zero_apply, add_zero]
  have hz : gFibreOpBound (I := I) (M := M) g z 0 := by
    intro y v w
    simp only [z, zero_apply, abs_zero, _root_.MulZeroClass.zero_mul, le_refl]
  have htrace := riemannianFiberNormSq_traceHessianFib_le
    (I := I) (M := M) g g z htie
      (show (0 : ℝ) < 1 by norm_num) (show (0 : ℝ) ≤ 0 by norm_num) hz x
  have hreindex :
      reindexCoefficientInputSlotsFiber (I := I) 4 2 traceHessianSlotPerm x
          ((cometricDoubleTraceField (I := I) g 2).toSection x) =
        (show TensorRSSpace 4 2 I x from traceHessianFib (I := I) g x) := by
    apply ContinuousLinearMap.ext
    intro D
    rw [reindexCoefficientInputSlotsFiber_apply, cometricDoubleTraceField_toSection,
      traceHessianFib, ContinuousLinearMap.comp_apply, domDomCongrFib_apply]
  calc
    riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        ((cometricDoubleTraceField (I := I) g 2).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        (reindexCoefficientInputSlotsFiber (I := I) 4 2 traceHessianSlotPerm x
          ((cometricDoubleTraceField (I := I) g 2).toSection x)) :=
        (riemannianFiberNormSq_reindexCoefficientInputSlotsFiber
          (I := I) (M := M) g 4 2 x traceHessianSlotPerm
          ((cometricDoubleTraceField (I := I) g 2).toSection x)).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        (show TensorRSSpace 4 2 I x from traceHessianFib (I := I) g x) := by
          rw [hreindex]
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 6 := by
      convert htrace using 1
      norm_num
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricTrace_riemannianFiberNormSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricTrace_riemannianFiberNormSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricTrace_riemannianFiberNormSq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricTrace_riemannianFiberNormSq

private def traceIdx0 (p : ℕ) : Fin (p + 2 + 1) := ⟨0, by omega⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceIdx0
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceIdx0 target :: scope.openDecls } }

private def traceIdx1 (p : ℕ) : Fin (p + 2 + 1) := ⟨1, by omega⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceIdx1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceIdx1 target :: scope.openDecls } }

private def traceIdx2 (p : ℕ) : Fin (p + 2 + 1) := ⟨2, by omega⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceIdx2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceIdx2 target :: scope.openDecls } }

private def traceSuccPerm (p : ℕ) : Equiv.Perm (Fin (p + 2 + 1)) :=
  (Equiv.swap (traceIdx0 p) (traceIdx1 p)).trans
    (Equiv.swap (traceIdx0 p) (traceIdx2 p))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceSuccPerm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceSuccPerm target :: scope.openDecls } }

private theorem traceSucc_zero (p : ℕ) :
    traceSuccPerm p (traceIdx0 p) = traceIdx1 p := by
  have h10 : traceIdx1 p ≠ traceIdx0 p := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [traceIdx0, traceIdx1] at hv
  have h12 : traceIdx1 p ≠ traceIdx2 p := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [traceIdx1, traceIdx2] at hv
  simp only [traceSuccPerm, Equiv.trans_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne h10 h12]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceSucc_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceSucc_zero target :: scope.openDecls } }

private theorem traceSucc_one (p : ℕ) :
    traceSuccPerm p (traceIdx1 p) = traceIdx2 p := by
  simp only [traceSuccPerm, Equiv.trans_apply, Equiv.swap_apply_right,
    Equiv.swap_apply_left]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceSucc_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceSucc_one target :: scope.openDecls } }

private theorem traceSucc_two (p : ℕ) :
    traceSuccPerm p (traceIdx2 p) = traceIdx0 p := by
  have h20 : traceIdx2 p ≠ traceIdx0 p := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [traceIdx0, traceIdx2] at hv
  have h21 : traceIdx2 p ≠ traceIdx1 p := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [traceIdx1, traceIdx2] at hv
  simp only [traceSuccPerm, Equiv.trans_apply,
    Equiv.swap_apply_of_ne_of_ne h20 h21, Equiv.swap_apply_right]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceSucc_two
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceSucc_two target :: scope.openDecls } }

private theorem traceSucc_ge (p : ℕ) (i : Fin (p + 2 + 1))
    (hi : 3 ≤ (i : ℕ)) : traceSuccPerm p i = i := by
  have hi0 : i ≠ traceIdx0 p := by
    intro h
    have hv : (i : ℕ) = 0 := by
      simpa only [traceIdx0] using congrArg Fin.val h
    omega
  have hi1 : i ≠ traceIdx1 p := by
    intro h
    have hv : (i : ℕ) = 1 := by
      simpa only [traceIdx1] using congrArg Fin.val h
    omega
  have hi2 : i ≠ traceIdx2 p := by
    intro h
    have hv : (i : ℕ) = 2 := by
      simpa only [traceIdx2] using congrArg Fin.val h
    omega
  simp only [traceSuccPerm, Equiv.trans_apply,
    Equiv.swap_apply_of_ne_of_ne hi0 hi1,
    Equiv.swap_apply_of_ne_of_ne hi0 hi2]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceSucc_ge
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceSucc_ge target :: scope.openDecls } }

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] in
private theorem traceSucc_tuple
    (p : ℕ) (a b : E) (m : Fin (p + 1) → E) :
    (Fin.cons (m 0) (Fin.cons a (Fin.cons b (Fin.tail m)))) ∘ traceSuccPerm p =
      Fin.cons a (Fin.cons b m) := by
  funext i
  refine Fin.cases ?_ (fun i₁ => ?_) i
  · rw [Function.comp_apply,
      show (0 : Fin (p + 2 + 1)) = traceIdx0 p by rfl]
    rw [traceSucc_zero]
    rfl
  refine Fin.cases ?_ (fun i₂ => ?_) i₁
  · rw [Function.comp_apply,
      show (Fin.succ (0 : Fin (p + 2)) : Fin (p + 2 + 1)) = traceIdx1 p by rfl]
    rw [traceSucc_one]
    rfl
  refine Fin.cases ?_ (fun i₃ => ?_) i₂
  · rw [Function.comp_apply,
      show (Fin.succ (Fin.succ (0 : Fin (p + 1))) : Fin (p + 2 + 1)) =
        traceIdx2 p by rfl]
    rw [traceSucc_two]
    rfl
  · have hge : 3 ≤ ((Fin.succ (Fin.succ (Fin.succ i₃)) : Fin (p + 2 + 1)) : ℕ) := by
      simp
    rw [Function.comp_apply, traceSucc_ge p _ hge]
    rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceSucc_tuple
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceSucc_tuple target :: scope.openDecls } }

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] in
private theorem traceSucc_fib
    (g : SmoothRiemannianMetric I M) (p : ℕ) (x : M) :
    reindexCoefficientInputSlotsFiber (I := I) (p + 2 + 1) (p + 1) (traceSuccPerm p) x
        (slotExtendFib (I := I) (M := M) (p + 2) p x
          (cometricDoubleTraceFib (I := I) g p x)) =
      cometricDoubleTraceFib (I := I) g (p + 1) x := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext fun m => ?_
  rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
  rw [reindexCoefficientInputSlotsFiber_apply,
    DifferentialGeometry.Integral.Connection.slotExtendFib_apply_eval]
  simp only [cometricDoubleTraceFib_toModel, modelDoubleTrace_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [TensorMultilinear.tensor0S_curry_toModel_apply, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg (Tensor0SSpace.toModel D)
    (traceSucc_tuple p
      (cometricLmodel (I := I) g x
        (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)))
      ((Module.finBasis ℝ E) k) (Fin.cons (m 0) (Fin.tail m)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceSucc_fib
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceSucc_fib target :: scope.openDecls } }

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem traceSucc_riemannianFiberNormSq
    (g : SmoothRiemannianMetric I M) (p : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g ((p + 1) + 2) (p + 1) x
        ((cometricDoubleTraceField (I := I) g (p + 1)).toSection x) =
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g (p + 2) p x
          ((cometricDoubleTraceField (I := I) g p).toSection x) := by
  rw [cometricDoubleTraceField_toSection, cometricDoubleTraceField_toSection,
    ← traceSucc_fib (I := I) (M := M) g p x,
    riemannianFiberNormSq_reindexCoefficientInputSlotsFiber]
  exact riemannianFiberNormSq_slotExtendFib_eq (I := I) (M := M) g (p + 2) p x
    (cometricDoubleTraceFib (I := I) g p x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceSucc_riemannianFiberNormSq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.traceSucc_riemannianFiberNormSq target :: scope.openDecls } }

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem cometricTrace_riemannianFiberNormSq_p
    (p : ℕ) (g : SmoothRiemannianMetric I M) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g (p + 2) p x
        ((cometricDoubleTraceField (I := I) g p).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ (p + 6) := by
  let d : ℝ := Module.finrank ℝ E
  have hd : (1 : ℝ) ≤ d := by
    dsimp only [d]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E))
  have hd0 : 0 ≤ d := le_trans (by norm_num) hd
  have hbase :
      riemannianFiberNormSq (I := I) (M := M) g 2 0 x
          ((cometricDoubleTraceField (I := I) g 0).toSection x) ≤ d ^ 6 := by
    have h0 := riemannianFiberNormSq_nonneg (I := I) (M := M) g 2 0 x
      ((cometricDoubleTraceField (I := I) g 0).toSection x)
    have h1 := riemannianFiberNormSq_nonneg (I := I) (M := M) g 3 1 x
      ((cometricDoubleTraceField (I := I) g 1).toSection x)
    have h01 := traceSucc_riemannianFiberNormSq (I := I) (M := M) g 0 x
    have h12 := traceSucc_riemannianFiberNormSq (I := I) (M := M) g 1 x
    have h02 :
        riemannianFiberNormSq (I := I) (M := M) g 2 0 x
            ((cometricDoubleTraceField (I := I) g 0).toSection x) ≤
          riemannianFiberNormSq (I := I) (M := M) g 4 2 x
            ((cometricDoubleTraceField (I := I) g 2).toSection x) := by
      dsimp only [d] at hd h01 h12
      nlinarith
    exact h02.trans (by
      simpa only [d] using cometricTrace_riemannianFiberNormSq (I := I) (M := M) g x)
  induction p with
  | zero =>
      simpa only [Nat.zero_add] using hbase
  | succ p ih =>
      rw [traceSucc_riemannianFiberNormSq (I := I) (M := M) g p x]
      calc
        (Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g (p + 2) p x
              ((cometricDoubleTraceField (I := I) g p).toSection x) ≤
          d * d ^ (p + 6) := by
            dsimp only [d]
            exact mul_le_mul_of_nonneg_left ih hd0
        _ = d ^ (p + 6) * d := mul_comm _ _
        _ = d ^ ((p + 6) + 1) := (pow_succ d (p + 6)).symm
        _ = d ^ ((p + 1) + 6) := by congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricTrace_riemannianFiberNormSq_p then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricTrace_riemannianFiberNormSq_p"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricTrace_riemannianFiberNormSq_p ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricTrace_riemannianFiberNormSq_p

omit [NeZero (Module.finrank ℝ E)] in
private lemma combinedTrace42Model_apply_symbolic
    (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
    (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (m : Fin 2 → E) :
    combinedTrace42Model (E := E) L D m =
      (1 / 2 : ℝ) *
        (modelDoubleTrace (E := E) 2 L
            (ContinuousMultilinearMap.domDomCongr koszulSlotPerm D) m
          + modelDoubleTrace (E := E) 2 L
              (ContinuousMultilinearMap.domDomCongr koszulSlotPerm D)
              (fun j : Fin 2 => m ((Equiv.swap (0 : Fin 2) 1) j))
          - modelDoubleTrace (E := E) 2 L D m) := by
  classical
  have hpermApply :
      koszulSlotPerm 0 = 0 ∧ koszulSlotPerm 1 = 2 ∧
        koszulSlotPerm 2 = 3 ∧ koszulSlotPerm 3 = 1 := by
    unfold koszulSlotPerm
    refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
  obtain ⟨hp0, hp1, hp2, hp3⟩ := hpermApply
  have hT03 : ∀ (mm : Fin 2 → E),
      modelDoubleTrace (E := E) 2 L
          (ContinuousMultilinearMap.domDomCongr koszulSlotPerm D) mm =
        ∑ k : Fin (Module.finrank ℝ E),
          D (Fin.cons (L (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
              ![mm 0, mm 1, (Module.finBasis ℝ E) k]) := by
    intro mm
    rw [modelDoubleTrace_apply (E := E) 2 L _ mm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    congr 1
    funext j
    have hperm : koszulSlotPerm j = ![(0 : Fin 4), 2, 3, 1] j := by
      fin_cases j
      · exact hp0
      · exact hp1
      · exact hp2
      · exact hp3
    rw [hperm]
    fin_cases j <;> rfl
  rw [combinedTrace42Model_apply (E := E) L D m, hT03 m,
    hT03 (fun i => m (Equiv.swap (0 : Fin 2) 1 i)),
    modelDoubleTrace_apply (E := E) 2 L D m]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  congr 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.combinedTrace42Model_apply_symbolic
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.combinedTrace42Model_apply_symbolic target :: scope.openDecls } }

omit [I.Boundaryless] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem ricciSelf_twice_eq
    (g : SmoothRiemannianMetric I M) :
    ricciDeTurckPrincipalCoefficient (I := I) (M := M) g g +
        ricciDeTurckPrincipalCoefficient (I := I) (M := M) g g =
      reindexCoefficientInputSlots (I := I) (M := M) g 4 2
          (cometricDoubleTraceField (I := I) g 2) koszulSlotPerm
        + reindexCoefficientInputSlots (I := I) (M := M) g 4 2
            (rsDomDomCongrSection (I := I) (M := M) g 4 2
              (Equiv.swap (0 : Fin 2) 1)
              (cometricDoubleTraceField (I := I) g 2)) koszulSlotPerm
        - cometricDoubleTraceField (I := I) g 2 := by
  classical
  apply DifferentialGeometry.Integral.L2.SmoothCcTensor.ext
  apply DFunLike.ext _ _
  intro x
  refine tensorRSSpace_ext 4 2 x (fun w => ?_)
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  change
    Tensor0SSpace.toModel
        (ricciDeTurckPrincipalCoefficientFiber (I := I) g x w +
          ricciDeTurckPrincipalCoefficientFiber (I := I) g x w) m =
      Tensor0SSpace.toModel
        (((reindexCoefficientInputSlots (I := I) (M := M) g 4 2
              (cometricDoubleTraceField (I := I) g 2) koszulSlotPerm).toSection x) w +
          ((reindexCoefficientInputSlots (I := I) (M := M) g 4 2
              (rsDomDomCongrSection (I := I) (M := M) g 4 2
                (Equiv.swap (0 : Fin 2) 1)
                (cometricDoubleTraceField (I := I) g 2)) koszulSlotPerm).toSection x) w -
          ((cometricDoubleTraceField (I := I) g 2).toSection x) w) m
  rw [Tensor0SSpace.toModel_add, add_apply,
    ricciDeTurckPrincipalCoefficientFiber_toModel, combinedTrace42Model_apply_symbolic,
    Tensor0SSpace.toModel_sub, Tensor0SSpace.toModel_add,
    sub_apply, add_apply]
  simp_rw [reindexCoefficientInputSlots_toSection, rsDomDomCongrSection_toSection,
    cometricDoubleTraceField_toSection]
  rw [reindexCoefficientInputSlotsFiber_apply (I := I) 4 2 koszulSlotPerm x
    (cometricDoubleTraceFib (I := I) g 2 x) w]
  rw [reindexCoefficientInputSlotsFiber_apply (I := I) 4 2 koszulSlotPerm x
    (rsDomDomCongr (I := I) (Equiv.swap (0 : Fin 2) 1)
      (cometricDoubleTraceFib (I := I) g 2 x)) w]
  rw [toModel_rsDomDomCongr_apply (I := I) (M := M)
    (Equiv.swap (0 : Fin 2) 1) (cometricDoubleTraceFib (I := I) g 2 x)]
  rw [cometricDoubleTraceFib_toModel, cometricDoubleTraceFib_toModel]
  rw [Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciSelf_twice_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciSelf_twice_eq target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricciSelf_eq
    (g : SmoothRiemannianMetric I M) :
    ricciDeTurckPrincipalCoefficient (I := I) (M := M) g g =
      (1 / 2 : ℝ) •
        (reindexCoefficientInputSlots (I := I) (M := M) g 4 2
            (cometricDoubleTraceField (I := I) g 2) koszulSlotPerm
          + reindexCoefficientInputSlots (I := I) (M := M) g 4 2
              (rsDomDomCongrSection (I := I) (M := M) g 4 2
                (Equiv.swap (0 : Fin 2) 1)
                (cometricDoubleTraceField (I := I) g 2)) koszulSlotPerm
          - cometricDoubleTraceField (I := I) g 2) := by
  have htwice := ricciSelf_twice_eq (I := I) (M := M) g
  calc
    ricciDeTurckPrincipalCoefficient (I := I) (M := M) g g =
        (1 : ℝ) • ricciDeTurckPrincipalCoefficient (I := I) (M := M) g g := by simp
    _ = ((1 / 2 : ℝ) + 1 / 2) •
        ricciDeTurckPrincipalCoefficient (I := I) (M := M) g g := by norm_num
    _ = (1 / 2 : ℝ) • ricciDeTurckPrincipalCoefficient (I := I) (M := M) g g +
        (1 / 2 : ℝ) • ricciDeTurckPrincipalCoefficient (I := I) (M := M) g g := by
          rw [add_smul]
    _ = (1 / 2 : ℝ) •
        (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g g +
          ricciDeTurckPrincipalCoefficient (I := I) (M := M) g g) := by
          rw [smul_add]
    _ = (1 / 2 : ℝ) •
        (reindexCoefficientInputSlots (I := I) (M := M) g 4 2
            (cometricDoubleTraceField (I := I) g 2) koszulSlotPerm
          + reindexCoefficientInputSlots (I := I) (M := M) g 4 2
              (rsDomDomCongrSection (I := I) (M := M) g 4 2
                (Equiv.swap (0 : Fin 2) 1)
                (cometricDoubleTraceField (I := I) g 2)) koszulSlotPerm
          - cometricDoubleTraceField (I := I) g 2) := by rw [htwice]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciSelf_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciSelf_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciSelf_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciSelf_eq

end DifferentialGeometry.Analysis.Parabolic.TensorSpectral

end
