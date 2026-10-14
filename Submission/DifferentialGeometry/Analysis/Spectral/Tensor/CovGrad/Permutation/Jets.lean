import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.PairTrace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Integral.Connection.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Connection.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Connection.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

theorem slotIteratedCovGradSq (g : SmoothRiemannianMetric I M) (r s i : ℕ)
    (A : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) i
        (slotExtend (I := I) (M := M) g r s A)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g r s i A‖ ^ 2 := by
  let F : M → ℝ := fun x =>
    (Module.finrank ℝ E : ℝ) *
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i A).toSection x)
  have hF : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g r (s + i)
      (iteratedCovGrad (I := I) g r s i A)).const_mul _
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g
          (r + 1) ((s + 1) + i) x
          ((iteratedCovGrad (I := I) g (r + 1) (s + 1) i
            (slotExtend (I := I) (M := M) g r s A)).toSection x) ≤
        F x := by
    intro x
    simpa only [F, Nat.add_assoc] using
      riemannianFiberNormSq_iteratedCovGrad_slotExtend_le
        (I := I) (M := M) g r s A i x
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (r + 1) ((s + 1) + i)
    (iteratedCovGrad (I := I) g (r + 1) (s + 1) i
      (slotExtend (I := I) (M := M) g r s A))
    F hF hpt
  have hint :
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g
          r (s + i) x
          ((iteratedCovGrad (I := I) g r s i A).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ‖iteratedCovGrad (I := I) g r s i A‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g r (s + i)]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.slotIteratedCovGradSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.slotIteratedCovGradSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.slotIteratedCovGradSq ``Submission.DifferentialGeometry.Integral.Connection.slotIteratedCovGradSq

theorem slotJet (g : SmoothRiemannianMetric I M) (r s m : ℕ)
    (A : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) j
          (slotExtend (I := I) (M := M) g r s A)‖ ^ 2) ≤
      (Module.finrank ℝ E : ℝ) *
        ∑ j ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 := by
  calc
    (∑ j ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) j
          (slotExtend (I := I) (M := M) g r s A)‖ ^ 2) ≤
        ∑ j ∈ Finset.range (m + 1), (Module.finrank ℝ E : ℝ) *
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 :=
      Finset.sum_le_sum fun j _ =>
        slotIteratedCovGradSq (I := I) (M := M) g r s j A
    _ = (Module.finrank ℝ E : ℝ) *
        ∑ j ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 := by
      rw [Finset.mul_sum]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.slotJet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.slotJet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.slotJet ``Submission.DifferentialGeometry.Integral.Connection.slotJet

theorem slotIterJet (g : SmoothRiemannianMetric I M) (r s m w : ℕ)
    (A : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g (r + w) (s + w) j
          (slotExtendIter (I := I) (M := M) g r s w A)‖ ^ 2) ≤
      (Module.finrank ℝ E : ℝ) ^ w *
        ∑ j ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 := by
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  induction w with
  | zero =>
    simpa only [slotExtendIter, Nat.add_zero, pow_zero, one_mul] using
      le_refl (∑ j ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2)
  | succ w ih =>
    calc
      (∑ j ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g (r + (w + 1)) (s + (w + 1)) j
            (slotExtendIter (I := I) (M := M) g r s (w + 1) A)‖ ^ 2) =
          ∑ j ∈ Finset.range (m + 1),
            ‖iteratedCovGrad (I := I) g ((r + w) + 1) ((s + w) + 1) j
              (slotExtend (I := I) (M := M) g (r + w) (s + w)
                (slotExtendIter (I := I) (M := M) g r s w A))‖ ^ 2 := rfl
      _ ≤ (Module.finrank ℝ E : ℝ) *
            ∑ j ∈ Finset.range (m + 1),
              ‖iteratedCovGrad (I := I) g (r + w) (s + w) j
                (slotExtendIter (I := I) (M := M) g r s w A)‖ ^ 2 :=
        slotJet (I := I) (M := M) g (r + w) (s + w) m _
      _ ≤ (Module.finrank ℝ E : ℝ) *
            ((Module.finrank ℝ E : ℝ) ^ w *
              ∑ j ∈ Finset.range (m + 1),
                ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) :=
        mul_le_mul_of_nonneg_left ih hfr
      _ = (Module.finrank ℝ E : ℝ) ^ (w + 1) *
            ∑ j ∈ Finset.range (m + 1),
              ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.slotIterJet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.slotIterJet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.slotIterJet ``Submission.DifferentialGeometry.Integral.Connection.slotIterJet

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem slotExtendIter_sub (g : SmoothRiemannianMetric I M) (r s w : ℕ)
    (A B : SmoothCcTensor g r s) :
    slotExtendIter (I := I) (M := M) g r s w (A - B) =
      slotExtendIter (I := I) (M := M) g r s w A -
        slotExtendIter (I := I) (M := M) g r s w B := by
  induction w with
  | zero => rfl
  | succ w ih =>
    change slotExtend (I := I) (M := M) g (r + w) (s + w)
        (slotExtendIter (I := I) (M := M) g r s w (A - B)) =
      slotExtend (I := I) (M := M) g (r + w) (s + w)
          (slotExtendIter (I := I) (M := M) g r s w A) -
        slotExtend (I := I) (M := M) g (r + w) (s + w)
          (slotExtendIter (I := I) (M := M) g r s w B)
    rw [ih, slotExtend_sub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.slotExtendIter_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.slotExtendIter_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.slotExtendIter_sub ``Submission.DifferentialGeometry.Integral.Connection.slotExtendIter_sub

theorem rspermSq (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A : SmoothCcTensor g r s) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g r s i
        (rsDomDomCongrSection (I := I) (M := M) g r s σ A)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s i A‖ ^ 2 := by
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr
    (I := I) (M := M) g r s σ A
      (rsDomDomCongrSection (I := I) (M := M) g r s σ A)
      (fun y d => by
        rw [rsDomDomCongrSection_toSection,
          toModel_rsDomDomCongr_apply]) i x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.rspermSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.rspermSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.rspermSq ``Submission.DifferentialGeometry.Integral.Connection.rspermSq

theorem rspermJet (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (σ : Equiv.Perm (Fin s)) (A : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g r s j
          (rsDomDomCongrSection (I := I) (M := M) g r s σ A)‖ ^ 2) =
      ∑ j ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 :=
  Finset.sum_congr rfl fun i _ =>
    rspermSq (I := I) (M := M) g σ A i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.rspermJet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.rspermJet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.rspermJet ``Submission.DifferentialGeometry.Integral.Connection.rspermJet

def monoExt (g : SmoothRiemannianMetric I M) (r s w : ℕ)
    (τ : Equiv.Perm (Fin (s + w))) (A : SmoothCcTensor g r s) :
    SmoothCcTensor g (r + w) (s + w) :=
  rsDomDomCongrSection (I := I) (M := M) g (r + w) (s + w) τ
    (slotExtendIter (I := I) (M := M) g r s w A)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.monoExt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.monoExt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.monoExt ``Submission.DifferentialGeometry.Integral.Connection.monoExt

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem monoExtSub (g : SmoothRiemannianMetric I M) (r s w : ℕ)
    (τ : Equiv.Perm (Fin (s + w))) (A B : SmoothCcTensor g r s) :
    monoExt (I := I) (M := M) g r s w τ (A - B) =
      monoExt (I := I) (M := M) g r s w τ A -
        monoExt (I := I) (M := M) g r s w τ B := by
  rw [monoExt, slotExtendIter_sub,
    CurvatureCoefficientDifferenceJetTower.rsDomDomCongrSection_sub_cc]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.monoExtSub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.monoExtSub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.monoExtSub ``Submission.DifferentialGeometry.Integral.Connection.monoExtSub

theorem monoExtJet (g : SmoothRiemannianMetric I M) (r s w m : ℕ)
    (τ : Equiv.Perm (Fin (s + w))) (A : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g (r + w) (s + w) j
          (monoExt (I := I) (M := M) g r s w τ A)‖ ^ 2) ≤
      (Module.finrank ℝ E : ℝ) ^ w *
        ∑ j ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 := by
  rw [monoExt, rspermJet]
  exact slotIterJet (I := I) (M := M) g r s m w A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.monoExtJet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.monoExtJet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.monoExtJet ``Submission.DifferentialGeometry.Integral.Connection.monoExtJet

end Connection
end Integral
end DifferentialGeometry

end
