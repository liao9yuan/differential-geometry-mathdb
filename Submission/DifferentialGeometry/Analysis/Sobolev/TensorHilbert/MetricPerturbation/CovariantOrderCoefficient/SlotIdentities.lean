import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.CovariantOrderCoefficient.PassZero
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Algebra.CoefficientReindexing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma termSlotFib_toModel_apply (s : ℕ) (x : M)
    (Term : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (D : Tensor0SSpace (s + 1) I x) (v : Fin (s + 1 + 1) → E) :
    Tensor0SSpace.toModel (termSlotFib (I := I) (M := M) s x Term D) v =
      Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
          (Term ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))) D)
        (Matrix.vecTail v) := by
  exact termSlotFib_apply_eval (I := I) (M := M) s x Term D
    (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.termSlotFib_toModel_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.termSlotFib_toModel_apply target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem termSlotEndoCc_succ
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    bilinearSlotInsertionCoefficient (I := I) (M := M) g (s + 1) A =
      reindexCoefficientInputSlots (I := I) (M := M) g (s + 1 + 1) (s + 1 + 1 + 1)
        (rsDomDomCongrSection (I := I) (M := M) g
          (s + 1 + 1) (s + 1 + 1 + 1)
          ((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
            (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2))
          (slotExtend (I := I) (M := M) g (s + 1) (s + 1 + 1)
            (bilinearSlotInsertionCoefficient (I := I) (M := M) g s A)))
        (Equiv.swap (0 : Fin (s + 1 + 1)) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  dsimp only
  rw [termSlotEndoCc_toSection]
  rw [show (TensorRSSpace.ofCLM
      (termSlotFib (I := I) (M := M) (s + 1) x (A x)) :
        Tensor0SSpace (s + 1 + 1) I x →L[ℝ]
          Tensor0SSpace (s + 1 + 1 + 1) I x) D =
    termSlotFib (I := I) (M := M) (s + 1) x (A x) D from rfl]
  rw [termSlotFib_toModel_apply]
  rw [reindexCoefficientInputSlots_toSection, reindexCoefficientInputSlotsFiber_apply,
    rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply, slotExtend_toSection]
  rw [show (fun k : Fin (s + 1 + 1 + 1) =>
      m (((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
        (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2)) k)) =
      Fin.cons (m (((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
          (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2)) 0))
        (fun j : Fin (s + 1 + 1) =>
          m (((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
            (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2)) (Fin.succ j))) from by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp only [Fin.cons_zero]
    · simp only [Fin.cons_succ]]
  rw [DifferentialGeometry.Analysis.Spectral.slotExtendFib_apply_eval]
  rw [termSlotEndoCc_toSection]
  rw [show (TensorRSSpace.ofCLM
      (termSlotFib (I := I) (M := M) s x (A x)) :
        Tensor0SSpace (s + 1) I x →L[ℝ]
          Tensor0SSpace (s + 1 + 1) I x)
      ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr
            (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
            (Tensor0SSpace.toModel D)))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
          (m (((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
            (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2)) 0)))) =
    termSlotFib (I := I) (M := M) s x (A x)
      ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr
            (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
            (Tensor0SSpace.toModel D)))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
          (m (((Equiv.swap (0 : Fin (s + 1 + 1 + 1)) 1).trans
            (Equiv.swap (1 : Fin (s + 1 + 1 + 1)) 2)) 0)))) from rfl]
  rw [termSlotFib_toModel_apply]
  rw [slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval]
  simp only [TensorMultilinear.tensor0S_curry_toModel_apply,
    Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext k
  refine Fin.cases ?_ (fun k₁ => Fin.cases ?_ (fun k₂ => ?_) k₁) k
  · rfl
  · rfl
  · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.termSlotEndoCc_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.termSlotEndoCc_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.termSlotEndoCc_succ ``Submission.DifferentialGeometry.Analysis.Sobolev.termSlotEndoCc_succ

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem termSlotEndoCc_sub
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    bilinearSlotInsertionCoefficient (I := I) (M := M) g s (A - B) =
      bilinearSlotInsertionCoefficient (I := I) (M := M) g s A -
        bilinearSlotInsertionCoefficient (I := I) (M := M) g s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  have hRHS : (show Tensor0SSpace (s + 1) I x →L[ℝ]
        Tensor0SSpace (s + 1 + 1) I x from
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g s A -
          bilinearSlotInsertionCoefficient (I := I) (M := M) g s B).toSection x) D =
      termSlotFib (I := I) (M := M) s x (A x) D -
        termSlotFib (I := I) (M := M) s x (B x) D := by
    rw [show ((bilinearSlotInsertionCoefficient (I := I) (M := M) g s A -
          bilinearSlotInsertionCoefficient (I := I) (M := M) g s B).toSection x) =
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g s A).toSection x -
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g s B).toSection x from rfl]
    rfl
  have hLHS : (show Tensor0SSpace (s + 1) I x →L[ℝ]
        Tensor0SSpace (s + 1 + 1) I x from
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g s (A - B)).toSection x) D =
      termSlotFib (I := I) (M := M) s x ((A - B) x) D := rfl
  have hfib : termSlotFib (I := I) (M := M) s x (A x - B x) D =
      termSlotFib (I := I) (M := M) s x (A x) D -
        termSlotFib (I := I) (M := M) s x (B x) D := by
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    dsimp only
    rw [Tensor0SSpace.toModel_sub, sub_apply,
      termSlotFib_toModel_apply, termSlotFib_toModel_apply, termSlotFib_toModel_apply,
      sub_apply,
      slotInsertEndoFib_sub_left (I := I) (M := M) (s + 1) 0 x
        (A x ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0)))
        (B x ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))),
      sub_apply, Tensor0SSpace.toModel_sub,
      sub_apply]
  rw [hLHS, hRHS, show ((A - B) x) = A x - B x from rfl, hfib]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.termSlotEndoCc_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.termSlotEndoCc_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.termSlotEndoCc_sub ``Submission.DifferentialGeometry.Analysis.Sobolev.termSlotEndoCc_sub

end DifferentialGeometry.Analysis.Sobolev
