import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.CovariantTensor.Mixed
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Inner
import Submission.DifferentialGeometry.Tensor.RSTensor.Algebra.Contraction
import Submission.DifferentialGeometry.Geometry.Curvature.SecondOrderDefect.MetricTraceFrame
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Algebra.SlotCurryLeibniz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
    CovariantDerivative
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannian
open _root_.Submission.DifferentialGeometry.Tensor0SNabla _root_.Submission.DifferentialGeometry.TensorRSNabla
    DifferentialGeometry.TensorMetricLowering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
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

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

private local instance tensorCovDivergenceModelNormedAddCommGroup (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModelNormedAddCommGroup r s

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorCovDivergenceModelNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.tensorCovDivergenceModelNormedAddCommGroup target :: scope.openDecls } }

private local instance tensorCovDivergenceModelNormedSpace (r s : ℕ) :
    NormedSpace ℝ (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModelNormedSpace r s

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorCovDivergenceModelNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.tensorCovDivergenceModelNormedSpace target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private lemma tensorRSSpace_toModelL_sum {r s : ℕ} (x : M) {ι : Type*} (fs : Finset ι)
    (f : ι → TensorRSSpace r s I x) :
    TensorRSSpace.toModelL (𝕜 := ℝ) (I := I) r s x (∑ i ∈ fs, f i) =
      ∑ i ∈ fs, TensorRSSpace.toModelL (𝕜 := ℝ) (I := I) r s x (f i) := by
  classical
  induction fs using Finset.cons_induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact ContinuousLinearMap.map_zero _
  | cons a fs ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons, ContinuousLinearMap.map_add, ih]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorRSSpace_toModelL_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.tensorRSSpace_toModelL_sum target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem tensorInnerPointwise_0s_succ_eq_sum_curryLeft_orthoFrame
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) (s + 1) g x S T =
      ∑ a : Fin (Module.finrank ℝ E),
        covariantTensorInnerPointwise (I := I) (M := M) s g x
          (S.curryLeft (tangentSpaceModelContinuousLinearEquiv (I := I) x (frame a)))
          (T.curryLeft (tangentSpaceModelContinuousLinearEquiv (I := I) x (frame a))) := by
  classical
  rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x (s + 1) frame horth S T]
  rw [show (∑ a : Fin (Module.finrank ℝ E),
        covariantTensorInnerPointwise (I := I) (M := M) s g x
          (S.curryLeft (tangentSpaceModelContinuousLinearEquiv (I := I) x (frame a)))
          (T.curryLeft (tangentSpaceModelContinuousLinearEquiv (I := I) x (frame a)))) =
      ∑ a : Fin (Module.finrank ℝ E),
        ∑ φ : Fin s → Fin (Module.finrank ℝ E),
          (S.curryLeft (tangentSpaceModelContinuousLinearEquiv (I := I) x (frame a)))
              (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (frame (φ k))) *
            (T.curryLeft (tangentSpaceModelContinuousLinearEquiv (I := I) x (frame a)))
              (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (frame (φ k))) from by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x s frame horth]]
  rw [← (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (s + 1) => Fin (Module.finrank ℝ E)))
        (fun pr : Fin (Module.finrank ℝ E) × (Fin s → Fin (Module.finrank ℝ E)) =>
          (S.curryLeft (tangentSpaceModelContinuousLinearEquiv (I := I) x (frame pr.1)))
              (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (frame (pr.2 k))) *
            (T.curryLeft (tangentSpaceModelContinuousLinearEquiv (I := I) x (frame pr.1)))
              (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (frame (pr.2 k))))
        (fun ψ : Fin (s + 1) → Fin (Module.finrank ℝ E) =>
          S (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (frame (ψ k))) *
            T (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (frame (ψ k))))
        ?_)]
  · rw [Fintype.sum_prod_type]
  · intro pr
    simp only [Fin.consEquiv_apply, ContinuousMultilinearMap.curryLeft_apply]
    have hcons :
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (frame pr.1))
          (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (frame (pr.2 k))) :
            Fin (s + 1) → E) =
        fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x
          (frame ((Fin.cons pr.1 pr.2 : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)) := by
      funext k
      refine Fin.cases ?_ ?_ k
      · simp
      · intro j; simp
    rw [hcons]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorInnerPointwise_0s_succ_eq_sum_curryLeft_orthoFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorInnerPointwise_0s_succ_eq_sum_curryLeft_orthoFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorInnerPointwise_0s_succ_eq_sum_curryLeft_orthoFrame ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorInnerPointwise_0s_succ_eq_sum_curryLeft_orthoFrame

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma contract_covariant_smul_left (s : ℕ) (x : M) (c : ℝ) (v : TangentSpace I x)
    (A : TensorRSSpace 0 (s + 1) I x) :
    contractCovariant 0 s x (c • v) A =
      c • contractCovariant 0 s x v A := by
  classical
  unfold contractCovariant
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  change (tensorRSSpaceContinuousLinearEquiv (I := I) 0 s x).symm
      (modelContractCovariantBilinear (𝕜 := ℝ) (E := E) 0 s
        (tangentSpaceModelContinuousLinearEquiv (I := I) x (c • v))
        (tensorRSSpaceContinuousLinearEquiv (I := I) 0 (s + 1) x A)) =
    c • (tensorRSSpaceContinuousLinearEquiv (I := I) 0 s x).symm
      (modelContractCovariantBilinear (𝕜 := ℝ) (E := E) 0 s
        (tangentSpaceModelContinuousLinearEquiv (I := I) x v)
        (tensorRSSpaceContinuousLinearEquiv (I := I) 0 (s + 1) x A))
  rw [map_smul, map_smul, smul_apply, map_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.contract_covariant_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.contract_covariant_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.contract_covariant_smul_left ``Submission.DifferentialGeometry.Analysis.Elliptic.contract_covariant_smul_left

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma contract_covariant_add_left (s : ℕ) (x : M) (v w : TangentSpace I x)
    (A : TensorRSSpace 0 (s + 1) I x) :
    contractCovariant 0 s x (v + w) A =
      contractCovariant 0 s x v A + contractCovariant 0 s x w A := by
  classical
  unfold contractCovariant
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  change (tensorRSSpaceContinuousLinearEquiv (I := I) 0 s x).symm
      (modelContractCovariantBilinear (𝕜 := ℝ) (E := E) 0 s
        (tangentSpaceModelContinuousLinearEquiv (I := I) x (v + w))
        (tensorRSSpaceContinuousLinearEquiv (I := I) 0 (s + 1) x A)) =
    (tensorRSSpaceContinuousLinearEquiv (I := I) 0 s x).symm
        (modelContractCovariantBilinear (𝕜 := ℝ) (E := E) 0 s
          (tangentSpaceModelContinuousLinearEquiv (I := I) x v)
          (tensorRSSpaceContinuousLinearEquiv (I := I) 0 (s + 1) x A)) +
      (tensorRSSpaceContinuousLinearEquiv (I := I) 0 s x).symm
        (modelContractCovariantBilinear (𝕜 := ℝ) (E := E) 0 s
          (tangentSpaceModelContinuousLinearEquiv (I := I) x w)
          (tensorRSSpaceContinuousLinearEquiv (I := I) 0 (s + 1) x A))
  rw [map_add, map_add, add_apply, map_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.contract_covariant_add_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.contract_covariant_add_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.contract_covariant_add_left ``Submission.DifferentialGeometry.Analysis.Elliptic.contract_covariant_add_left

noncomputable def covDivergenceBilinear
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (y : M) :
    TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TensorRSSpace 0 s I y :=
  TensorialAt.mkHom₂
    (I := I) (F := E) (F' := E)
    (V := (TangentSpace I : M → Type _))
    (V' := (TangentSpace I : M → Type _))
    (A := TensorRSSpace 0 s I y)
    (Φ := fun (X Y : Π b : M, TangentSpace I b) =>
      contractCovariant 0 s y (Y y)
        ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
            (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y)))
    y
    (fun Y _hY => by
      refine ⟨?_, ?_⟩
      · intro f X _hf _hX
        have hsmul : (f • X : Π b : M, TangentSpace I b) y = f y • X y := rfl
        change contractCovariant 0 s y (Y y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y ((f • X) y)) =
          f y • contractCovariant 0 s y (Y y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y))
        rw [hsmul, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul]
      · intro X X' _hX _hX'
        have hadd : (X + X' : Π b : M, TangentSpace I b) y = X y + X' y := rfl
        change contractCovariant 0 s y (Y y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y ((X + X') y)) =
          contractCovariant 0 s y (Y y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y)) +
          contractCovariant 0 s y (Y y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X' y))
        rw [hadd, ContinuousLinearMap.map_add, ContinuousLinearMap.map_add])
    (fun X _hX => by
      refine ⟨?_, ?_⟩
      · intro f Y _hf _hY
        have hsmul : (f • Y : Π b : M, TangentSpace I b) y = f y • Y y := rfl
        change contractCovariant 0 s y ((f • Y) y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y)) =
          f y • contractCovariant 0 s y (Y y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y))
        rw [hsmul]
        exact contract_covariant_smul_left s y (f y) (Y y) _
      · intro Y Y' _hY _hY'
        have hadd : (Y + Y' : Π b : M, TangentSpace I b) y = Y y + Y' y := rfl
        change contractCovariant 0 s y ((Y + Y') y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y)) =
          contractCovariant 0 s y (Y y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y)) +
          contractCovariant 0 s y (Y' y)
            ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
              (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y))
        rw [hadd]
        exact contract_covariant_add_left s y (Y y) (Y' y) _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDivergenceBilinear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDivergenceBilinear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDivergenceBilinear ``Submission.DifferentialGeometry.Analysis.Elliptic.covDivergenceBilinear

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem codiffPsi_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (y : M)
    {X Y : Π b : M, TangentSpace I b}
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z (X z)) y)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z (Y z)) y) :
    covDivergenceBilinear (I := I) (M := M) g s V y (X y) (Y y) =
      contractCovariant 0 s y (Y y)
        ((TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
            (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) y (X y)) := by
  classical
  unfold covDivergenceBilinear
  exact TensorialAt.mkHom₂_apply _ _ hX hY

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.codiffPsi_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.codiffPsi_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.codiffPsi_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.codiffPsi_apply

def covDivergenceRaw
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (b : M) :
    TensorRSSpace 0 s I b :=
  ∑ i : Fin (Module.finrank ℝ E),
    covDivergenceBilinear (I := I) (M := M) g s V b
      (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b i b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw ``Submission.DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw

def covDivergenceFixedFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1))
    (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    TensorRSSpace 0 s I b :=
  ∑ i : Fin (Module.finrank ℝ E),
    contractCovariant 0 s b (B i b)
      (tensorCovDerivAt (I := I) (M := M) g 0 (s + 1) V b (B i b))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDivergenceFixedFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDivergenceFixedFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDivergenceFixedFrame ``Submission.DifferentialGeometry.Analysis.Elliptic.covDivergenceFixedFrame

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma covDivergenceFixedFrame_eq_sum_section
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1))
    (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    covDivergenceFixedFrame (I := I) (M := M) g s V B b =
      ∑ i : Fin (Module.finrank ℝ E),
        (contractCovariantField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 0 s
          (covDerivAlongVFSectionRS (I := I) (M := M) g 0 (s + 1) V.toSection (B i)) (B i)) b :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDivergenceFixedFrame_eq_sum_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDivergenceFixedFrame_eq_sum_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDivergenceFixedFrame_eq_sum_section ``Submission.DifferentialGeometry.Analysis.Elliptic.covDivergenceFixedFrame_eq_sum_section

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma covDivergenceFixedFrame_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1))
    (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (covDivergenceFixedFrame (I := I) (M := M) g s V B b)) := by
  classical
  have hsummand : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
        (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
          (E := fun z : M => TensorRSSpace 0 s I z) b
          ((contractCovariantField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 0 s
            (covDerivAlongVFSectionRS (I := I) (M := M) g 0 (s + 1) V.toSection (B i))
            (B i)) b)) :=
    fun i =>
      (contractCovariantField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 0 s
        (covDerivAlongVFSectionRS (I := I) (M := M) g 0 (s + 1) V.toSection (B i)) (B i)).contMDiff
  have heq : (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (covDivergenceFixedFrame (I := I) (M := M) g s V B b)) =
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (∑ i : Fin (Module.finrank ℝ E),
          (contractCovariantField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 0 s
            (covDerivAlongVFSectionRS (I := I) (M := M) g 0 (s + 1) V.toSection (B i))
            (B i)) b)) := by
    funext b
    rw [covDivergenceFixedFrame_eq_sum_section (I := I) (M := M) g s V B b]
  rw [heq]
  exact ContMDiff.sum_section (fun i _ => hsummand i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDivergenceFixedFrame_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDivergenceFixedFrame_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDivergenceFixedFrame_contMDiff ``Submission.DifferentialGeometry.Analysis.Elliptic.covDivergenceFixedFrame_contMDiff

def smoothOrthoFrameSection
    (g : SmoothRiemannianMetric I M) (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨fun b : M => smoothOrthoFrame (I := I) g x₀ i b, smoothOrthoFrame_smooth (I := I) g x₀ i⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.smoothOrthoFrameSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.smoothOrthoFrameSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.smoothOrthoFrameSection ``Submission.DifferentialGeometry.Analysis.Elliptic.smoothOrthoFrameSection

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] lemma smoothOrthoFrameSection_apply
    (g : SmoothRiemannianMetric I M) (x₀ : M) (i : Fin (Module.finrank ℝ E)) (b : M) :
    smoothOrthoFrameSection (I := I) (M := M) g x₀ i b =
      smoothOrthoFrame (I := I) g x₀ i b := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.smoothOrthoFrameSection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.smoothOrthoFrameSection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.smoothOrthoFrameSection_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.smoothOrthoFrameSection_apply

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
lemma covDivergenceRaw_eq_codiffPsi_smoothOrthoFrame_trace
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (b : M)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I b)
    (hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    covDivergenceRaw (I := I) (M := M) g s V b =
      ∑ i : Fin (Module.finrank ℝ E),
        covDivergenceBilinear (I := I) (M := M) g s V b (B i) (B i) := by
  classical
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) b).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) b
  have hcentral : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b j b) =
        if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g b i j
  have hcentral_trace := orthonormal_basis_bilin_trace_chartα (I := I)
    (A := TensorRSSpace 0 s I b) g b hb_base (covDivergenceBilinear (I := I) (M := M) g s V b)
    (fun i => smoothOrthoFrame (I := I) g b i b) hcentral
  have hB_trace := orthonormal_basis_bilin_trace_chartα (I := I)
    (A := TensorRSSpace 0 s I b) g b hb_base (covDivergenceBilinear (I := I) (M := M) g s V b) B
      hB_orth
  rw [covDivergenceRaw, hcentral_trace, ← hB_trace]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw_eq_codiffPsi_smoothOrthoFrame_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw_eq_codiffPsi_smoothOrthoFrame_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw_eq_codiffPsi_smoothOrthoFrame_trace ``Submission.DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw_eq_codiffPsi_smoothOrthoFrame_trace

omit [CompactSpace M] [SigmaCompactSpace M] in
lemma covDivergenceRaw_eq_fixedFrame_on_neighborhood
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (x₀ : M)
    {b : M} (hb : b ∈ smoothOrthoFrameNeighborhood (I := I) (M := M) x₀) :
    covDivergenceRaw (I := I) (M := M) g s V b =
      covDivergenceFixedFrame (I := I) (M := M) g s V
        (fun i => smoothOrthoFrameSection (I := I) (M := M) g x₀ i) b := by
  classical
  have hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b (smoothOrthoFrame (I := I) g x₀ i b) (smoothOrthoFrame (I := I) g x₀ j b) =
        if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal (I := I) g x₀ hb i j
  rw [covDivergenceRaw_eq_codiffPsi_smoothOrthoFrame_trace (I := I) (M := M) g s V b
    (fun i => smoothOrthoFrame (I := I) g x₀ i b) hB_orth]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hSmooth_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
        (smoothOrthoFrame (I := I) g x₀ i z)) b :=
    (smoothOrthoFrame_smooth (I := I) g x₀ i).contMDiffAt.mdifferentiableAt (by simp)
  rw [codiffPsi_apply (I := I) (M := M) g s V b hSmooth_at hSmooth_at]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw_eq_fixedFrame_on_neighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw_eq_fixedFrame_on_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw_eq_fixedFrame_on_neighborhood ``Submission.DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw_eq_fixedFrame_on_neighborhood

omit [CompactSpace M] [SigmaCompactSpace M] in
theorem covDivergenceRaw_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (covDivergenceRaw (I := I) (M := M) g s V b)) := by
  classical
  intro x₀
  have h_fixed : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (covDivergenceFixedFrame (I := I) (M := M) g s V
          (fun i => smoothOrthoFrameSection (I := I) (M := M) g x₀ i) b)) :=
    covDivergenceFixedFrame_contMDiff (I := I) (M := M) g s V
      (fun i => smoothOrthoFrameSection (I := I) (M := M) g x₀ i)
  have h_fixed_at := h_fixed x₀
  have h_eventuallyEq :
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (covDivergenceRaw (I := I) (M := M) g s V b)) =ᶠ[𝓝 x₀]
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (covDivergenceFixedFrame (I := I) (M := M) g s V
          (fun i => smoothOrthoFrameSection (I := I) (M := M) g x₀ i) b)) := by
    filter_upwards [smoothOrthoFrameNeighborhood_mem_nhds (I := I) (M := M) x₀] with b hb
    exact congrArg (TotalSpace.mk' (TensorRSModel 0 s ℝ E)
      (E := fun z : M => TensorRSSpace 0 s I z) b)
      (covDivergenceRaw_eq_fixedFrame_on_neighborhood (I := I) (M := M) g s V x₀ hb)
  exact h_fixed_at.congr_of_eventuallyEq h_eventuallyEq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw_contMDiff ``Submission.DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw_contMDiff

omit [CompactSpace M] [SigmaCompactSpace M] in
lemma covDivergenceRaw_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1))
    {b : M} (hb : b ∉ tsupport V.toFun) :
    covDivergenceRaw (I := I) (M := M) g s V b = 0 := by
  classical
  rw [covDivergenceRaw]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hzero : (TensorRSNabla.tensorRSCovariantDerivative I M 0 (s + 1)
      (LeviCivita (I := I) g)).toFun (fun z : M => V.toSection z) b
        (smoothOrthoFrame (I := I) g b i b) = 0 := by
    have := tensorCovDerivAt_eq_zero_off_tsupport (I := I) (M := M) g 0 (s + 1) V hb
      (smoothOrthoFrame (I := I) g b i b)
    exact this
  have hSmooth_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
        (smoothOrthoFrame (I := I) g b i z)) b :=
    (smoothOrthoFrame_smooth (I := I) g b i).contMDiffAt.mdifferentiableAt (by simp)
  rw [codiffPsi_apply (I := I) (M := M) g s V b hSmooth_at hSmooth_at]
  rw [hzero]
  exact ContinuousLinearMap.map_zero _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw_eq_zero_off_tsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw_eq_zero_off_tsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw_eq_zero_off_tsupport ``Submission.DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw_eq_zero_off_tsupport

omit [CompactSpace M] [SigmaCompactSpace M] in
lemma covDivergenceRaw_toModel_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) :
    HasCompactSupport
      (fun b : M => TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b)) := by
  classical
  refine HasCompactSupport.of_support_subset_isCompact V.hasCompactSupport ?_
  intro b hb
  rw [Function.mem_support] at hb
  by_contra hbnot
  apply hb
  rw [covDivergenceRaw_eq_zero_off_tsupport (I := I) (M := M) g s V hbnot,
    TensorRSSpace.toModel_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw_toModel_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw_toModel_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw_toModel_hasCompactSupport ``Submission.DifferentialGeometry.Analysis.Elliptic.covDivergenceRaw_toModel_hasCompactSupport

noncomputable def covDivergence
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) :
    SmoothCcTensor g 0 s where
  toSection :=
    { toFun := fun b : M => covDivergenceRaw (I := I) (M := M) g s V b
      contMDiff_toFun := covDivergenceRaw_contMDiff (I := I) (M := M) g s V }
  hasCompactSupport := covDivergenceRaw_toModel_hasCompactSupport (I := I) (M := M) g s V

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDivergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDivergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDivergence ``Submission.DifferentialGeometry.Analysis.Elliptic.covDivergence

omit [CompactSpace M] [SigmaCompactSpace M] in
@[simp] lemma covDivergence_toSection_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (b : M) :
    (covDivergence (I := I) (M := M) g s V).toSection b =
      covDivergenceRaw (I := I) (M := M) g s V b := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDivergence_toSection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDivergence_toSection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDivergence_toSection_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.covDivergence_toSection_apply

omit [CompactSpace M] [SigmaCompactSpace M] in
@[simp] lemma covDivergence_toFun_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (b : M) :
    (covDivergence (I := I) (M := M) g s V).toFun b =
      TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDivergence_toFun_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDivergence_toFun_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDivergence_toFun_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.covDivergence_toFun_apply

def oneSidedDirichletForm
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) (b : M) :
    TangentSpace I b →ₗ[ℝ] ℝ where
  toFun X := tensorInnerPointwise (I := I) (M := M) g 0 s b
    (TensorRSSpace.toModel (T.toSection b))
    (TensorRSSpace.toModel (contractCovariant 0 s b X (V.toSection b)))
  map_add' X Y := by
    rw [contract_covariant_add_left (I := I) (M := M) s b X Y (V.toSection b),
      TensorRSSpace.toModel_add, tensorInnerPointwise_add_right]
  map_smul' c X := by
    rw [contract_covariant_smul_left (I := I) (M := M) s b c X (V.toSection b),
      TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_right]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletForm ``Submission.DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletForm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma oneSidedDirichletForm_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) (b : M) (X : TangentSpace I b) :
    oneSidedDirichletForm (I := I) (M := M) g s T V b X =
      tensorInnerPointwise (I := I) (M := M) g 0 s b
        (TensorRSSpace.toModel (T.toSection b))
        (TensorRSSpace.toModel (contractCovariant 0 s b X (V.toSection b))) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletForm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletForm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletForm_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletForm_apply

def oneSidedDirichletVF
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) (b : M) :
    TangentSpace I b :=
  metricSharp (I := I) g b (oneSidedDirichletForm (I := I) (M := M) g s T V b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletVF then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletVF"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletVF ``Submission.DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletVF

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma inner_oneSidedDirichletVF
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) (b : M) (X : TangentSpace I b) :
    g.inner b (oneSidedDirichletVF (I := I) (M := M) g s T V b) X =
      oneSidedDirichletForm (I := I) (M := M) g s T V b X := by
  rw [oneSidedDirichletVF]
  exact inner_metricSharp (I := I) g b (oneSidedDirichletForm (I := I) (M := M) g s T V b) X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.inner_oneSidedDirichletVF then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.inner_oneSidedDirichletVF"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.inner_oneSidedDirichletVF ``Submission.DifferentialGeometry.Analysis.Elliptic.inner_oneSidedDirichletVF

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem modelContractCovariantBilinear_contMDiffAt
    (s : ℕ) (x : M) (X : M → E) (A : M → TensorRSModel 0 (s + 1) ℝ E)
    (hX : ContMDiffAt I 𝓘(ℝ, E) ∞ X x)
    (hA : ContMDiffAt I 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E) ∞ A x) :
    ContMDiffAt I 𝓘(ℝ, TensorRSModel 0 s ℝ E) ∞
      (fun y => modelContractCovariantBilinear (𝕜 := ℝ) (E := E) 0 s (X y) (A y)) x :=
  ((contMDiffAt_const
    (c := modelContractCovariantBilinear (𝕜 := ℝ) (E := E) 0 s)).clm_apply hX).clm_apply hA

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.modelContractCovariantBilinear_contMDiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.modelContractCovariantBilinear_contMDiffAt target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma contract_chartBasis_contMDiffOn
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun y : M => TensorRSSpace 0 s I y) b
        (contractCovariant 0 s b (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b) (V.toSection b)))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  let := tensorRSBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 (s + 1)
  let := tensorRSBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 s
  let := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0
  let := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  let := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1)
  have hV_on : ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun y : M => TensorRSSpace 0 (s + 1) I y) b (V.toSection b))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    V.toSection.contMDiff.contMDiffOn
  have hX_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn (I := I) α j
  intro x₀ hx₀
  refine ContMDiffWithinAt.mono ?_ (Set.subset_univ _)
  refine ContMDiffAt.contMDiffWithinAt ?_
  rw [Bundle.contMDiffAt_section (F := TensorRSModel 0 s ℝ E)
    (E := fun z : M => TensorRSSpace 0 s I z)]
  have hV_at := (hV_on x₀ hx₀).contMDiffAt
    ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)
  have hX_at := (hX_on x₀ hx₀).contMDiffAt
    ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)
  have hV' := (Bundle.contMDiffAt_section (F := TensorRSModel 0 (s + 1) ℝ E)
    (E := fun z : M => TensorRSSpace 0 (s + 1) I z) x₀).mp hV_at
  have hX' := (Bundle.contMDiffAt_section (F := E) (E := TangentSpace I) x₀).mp hX_at
  have h_combine :
      ContMDiffAt I 𝓘(ℝ, TensorRSModel 0 s ℝ E) ∞
        (fun b : M => modelContractCovariantBilinear (𝕜 := ℝ) (E := E) 0 s
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀ ⟨b, DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b⟩).2)
          ((_root_.FiberBundle.trivializationAt (TensorRSModel 0 (s + 1) ℝ E)
            (fun z : M => TensorRSSpace 0 (s + 1) I z) x₀ ⟨b, V.toSection b⟩).2)) x₀ :=
    modelContractCovariantBilinear_contMDiffAt (I := I) (M := M) s x₀ _ _ hX' hV'
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase := (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (_root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with b hb
  refine ContinuousLinearMap.ext fun γ => ?_
  refine ContinuousMultilinearMap.ext fun w => ?_
  set sL := (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL ℝ b with hsL
  set Xtilde : E := (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀
    ⟨b, DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b⟩).2
    with hXtilde
  set gtilde : Tensor0SSpace 0 I b :=
    (_root_.FiberBundle.trivializationAt (Tensor0SModel 0 ℝ E) (fun z : M => Tensor0SSpace 0 I z) x₀).symmL ℝ b γ
    with hgtilde
  have h_cLMAt_s : ∀ (Tm : Tensor0SSpace s I b) (v : Fin s → E),
      (_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
        (fun z : M => Tensor0SSpace s I z) x₀).continuousLinearMapAt ℝ b Tm v =
      Tensor0SSpace.eval Tm (fun i => sL (v i)) := by
    intro Tm v
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
        (fun z : M => Tensor0SSpace s I z) x₀).linearMapAt ℝ b) =
        fun y => (_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
          (fun z : M => Tensor0SSpace s I z) x₀ ⟨b, y⟩).2 from
      (_root_.FiberBundle.trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := ℝ) hb]
    rfl
  have h_cLMAt_s1 : ∀ (Tm : Tensor0SSpace (s + 1) I b) (v : Fin (s + 1) → E),
      (_root_.FiberBundle.trivializationAt (Tensor0SModel (s + 1) ℝ E)
        (fun z : M => Tensor0SSpace (s + 1) I z) x₀).continuousLinearMapAt ℝ b Tm v =
      Tensor0SSpace.eval Tm (fun i => sL (v i)) := by
    intro Tm v
    rw [Trivialization.continuousLinearMapAt_apply,
      show ⇑((_root_.FiberBundle.trivializationAt (Tensor0SModel (s + 1) ℝ E)
        (fun z : M => Tensor0SSpace (s + 1) I z) x₀).linearMapAt ℝ b) =
        fun y => (_root_.FiberBundle.trivializationAt (Tensor0SModel (s + 1) ℝ E)
          (fun z : M => Tensor0SSpace (s + 1) I z) x₀ ⟨b, y⟩).2 from
      (_root_.FiberBundle.trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := ℝ) hb]
    rfl
  change (_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
      (fun z : M => Tensor0SSpace s I z) x₀).continuousLinearMapAt ℝ b
      (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s b
        ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (s + 1) I b from V.toSection b) gtilde)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b)) w =
    (_root_.FiberBundle.trivializationAt (Tensor0SModel (s + 1) ℝ E)
      (fun z : M => Tensor0SSpace (s + 1) I z) x₀).continuousLinearMapAt ℝ b
      ((show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace (s + 1) I b from V.toSection b) gtilde)
      (Fin.cons Xtilde w)
  rw [h_cLMAt_s, h_cLMAt_s1]
  rw [TensorMultilinear.tensor0S_curry_apply_eval]
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · change (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b : E) = sL Xtilde
    have h := (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
      (R := ℝ) hb (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b)
    have hcl : (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ b
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b) = Xtilde := by
      change (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).linearMapAt ℝ b
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b) = _
      rw [(_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).coe_linearMapAt_of_mem (R := ℝ) hb]
    rw [hcl] at h
    exact h.symm
  · intro jj
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.contract_chartBasis_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.contract_chartBasis_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.contract_chartBasis_contMDiffOn ``Submission.DifferentialGeometry.Analysis.Elliptic.contract_chartBasis_contMDiffOn

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma oneSidedDirichletForm_chartBasis_component_contMDiffOn
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) (α : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => oneSidedDirichletForm (I := I) (M := M) g s T V b
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b))
      (chartAt H α).source := by
  classical
  have hT_lowered : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (0 + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g 0 s α b
        (TensorRSSpace.toModel (T.toSection b)))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    TensorMetricLowering.contMDiffOn_loweredCompose (I := I) (M := M) g 0 s T.toSection α
  have hcontract_lowered : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (0 + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g 0 s α b
        (TensorRSSpace.toModel
          (contractCovariant 0 s b (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b) (V.toSection b))))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    TensorMetricLowering.contMDiffOn_loweredCompose_of_section_contMDiffOn
      (I := I) (M := M) g 0 s
      (fun b : M => contractCovariant 0 s b (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b) (V.toSection b))
      α (contract_chartBasis_contMDiffOn (I := I) (M := M) g s V α j)
  have hinner : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel
            (contractCovariant 0 s b (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b) (V.toSection b))))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Tensor.TensorRSRiemannian.chartLocal_contMDiff_inner_of_smooth_sections
      (I := I) (M := M) g 0 s
      (fun b : M => T.toSection b)
      (fun b : M => contractCovariant 0 s b (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b) (V.toSection b))
      α hT_lowered hcontract_lowered
  have hbase_eq : (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet =
      (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source
      (I := I) α
  rw [hbase_eq] at hinner
  refine hinner.congr ?_
  intro b _
  rw [oneSidedDirichletForm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletForm_chartBasis_component_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletForm_chartBasis_component_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletForm_chartBasis_component_contMDiffOn ``Submission.DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletForm_chartBasis_component_contMDiffOn

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma oneSidedDirichletVF_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E b (oneSidedDirichletVF (I := I) (M := M) g s T V b)) :=
  metricSharp_contMDiff_total (I := I) g
    (cv := fun b : M => oneSidedDirichletForm (I := I) (M := M) g s T V b)
    (fun α j => oneSidedDirichletForm_chartBasis_component_contMDiffOn
      (I := I) (M := M) g s T V α j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletVF_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletVF_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletVF_contMDiff ``Submission.DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletVF_contMDiff

def oneSidedDirichletVFSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ContMDiffSection.mk
    (fun b : M => oneSidedDirichletVF (I := I) (M := M) g s T V b)
    (oneSidedDirichletVF_contMDiff (I := I) (M := M) g s T V)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletVFSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletVFSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletVFSection ``Submission.DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletVFSection

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma oneSidedDirichletVFSection_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s)
    (V : SmoothCcTensor g 0 (s + 1)) (b : M) :
    oneSidedDirichletVFSection (I := I) (M := M) g s T V b =
      oneSidedDirichletVF (I := I) (M := M) g s T V b := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletVFSection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletVFSection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletVFSection_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.oneSidedDirichletVFSection_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private lemma contract_toModel_apply (s : ℕ) (x : M) (v : TangentSpace I x)
    (A : TensorRSSpace 0 (s + 1) I x) (D : Tensor0SSpace 0 I x) (m : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          contractCovariant 0 s x v A) D) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s+1) I x from A) D)
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x v) m) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.contract_toModel_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.contract_toModel_apply target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private lemma contract_eval (s : ℕ) (x : M) (v : TangentSpace I x)
    (A : TensorRSSpace 0 (s + 1) I x) (D : Tensor0SSpace 0 I x)
    (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.eval
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          contractCovariant 0 s x v A) D) m =
      Tensor0SSpace.eval
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s+1) I x from A) D)
        (Fin.cons v m) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.contract_eval
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.contract_eval target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma D_eq_scalar_smul_unit (x : M) (D : Tensor0SSpace 0 I x) :
    D = (tensor00Scalar (I := I) (M := M) x D) • (unitZeroSec (I := I) (M := M) x) := by
  apply Tensor0SSpace.toModel_injective
  change Tensor0SSpace.toModel D =
    Tensor0SSpace.toModel ((tensor00Scalar (I := I) (M := M) x D) •
      (unitZeroSec (I := I) (M := M) x))
  rw [Tensor0SSpace.toModel_smul]
  apply ContinuousMultilinearMap.ext
  intro m
  rw [smul_apply]
  rw [unitZeroSec_apply, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.constOfIsEmpty_apply]
  rw [tensor00Scalar_apply (I := I) (M := M) x D m, smul_eq_mul, mul_one]
  congr 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.D_eq_scalar_smul_unit
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.D_eq_scalar_smul_unit target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma contract_eq_tensor0SAsRS_curry (s : ℕ) (x : M) (v : TangentSpace I x)
    (A : TensorRSSpace 0 (s + 1) I x) :
    contractCovariant 0 s x v A =
      tensor0SToTensorRS (I := I) (M := M) x
        (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s+1) I x from A)
            (unitZeroSec (I := I) (M := M) x)) v) := by
  apply tensorRSSpace_ext 0 s x
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [contract_toModel_apply (I := I) (M := M) s x v A D m]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor0SToTensorRS (I := I) (M := M) x
          (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s+1) I x from A)
              (unitZeroSec (I := I) (M := M) x)) v)) D =
      tensor00Scalar (I := I) (M := M) x D •
        (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s+1) I x from A)
            (unitZeroSec (I := I) (M := M) x)) v) from
    tensor0SAsRS_apply (I := I) (M := M) x _ D]
  change _ = Tensor0SSpace.toModel
      (tensor00Scalar (I := I) (M := M) x D •
        (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s+1) I x from A)
            (unitZeroSec (I := I) (M := M) x)) v)) m
  rw [Tensor0SSpace.toModel_smul, smul_apply]
  conv_lhs => rw [D_eq_scalar_smul_unit (I := I) (M := M) x D]
  rw [ContinuousLinearMap.map_smul]
  change Tensor0SSpace.toModel
      (tensor00Scalar (I := I) (M := M) x D •
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s+1) I x from A)
          (unitZeroSec (I := I) (M := M) x)))
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x v) m) = _
  rw [Tensor0SSpace.toModel_smul, smul_apply]
  have hcurry := TensorMultilinear.tensor0S_curry_toModel_apply
    (I := I) (M := M)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from A)
      (unitZeroSec (I := I) (M := M) x))
    (tangentSpaceModelContinuousLinearEquiv (I := I) x v) m
  rw [(tangentSpaceModelContinuousLinearEquiv (I := I) x).symm_apply_apply] at hcurry
  rw [hcurry]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.contract_eq_tensor0SAsRS_curry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.contract_eq_tensor0SAsRS_curry target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma rs_zero_recover (s : ℕ) (x : M) (Φ : TensorRSSpace 0 s I x) :
    Φ = tensor0SToTensorRS (I := I) (M := M) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Φ)
        (unitZeroSec (I := I) (M := M) x)) := by
  apply tensorRSSpace_ext 0 s x
  intro D
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor0SToTensorRS (I := I) (M := M) x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Φ)
            (unitZeroSec (I := I) (M := M) x))) D =
      tensor00Scalar (I := I) (M := M) x D •
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Φ)
          (unitZeroSec (I := I) (M := M) x)) from
    tensor0SAsRS_apply (I := I) (M := M) x _ D]
  conv_lhs => rw [D_eq_scalar_smul_unit (I := I) (M := M) x D, ContinuousLinearMap.map_smul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.rs_zero_recover
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.rs_zero_recover target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SAsRS_add (s : ℕ) (x : M) (C D : Tensor0SSpace s I x) :
    tensor0SToTensorRS (I := I) (M := M) x (C + D) =
      tensor0SToTensorRS (I := I) (M := M) x C + tensor0SToTensorRS (I := I) (M := M) x D := by
  apply ContinuousLinearMap.ext
  intro u
  change (tensor00Scalar (I := I) (M := M) x u) • (C + D) =
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from tensor0SToTensorRS (I := I) (M := M) x
      C) u +
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from tensor0SToTensorRS (I := I) (M := M) x
      D) u
  rw [tensor0SAsRS_apply, tensor0SAsRS_apply, smul_add]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.tensor0SAsRS_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.tensor0SAsRS_add target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma contract_covariant_leibniz
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1))
    {W X : Π b:M, TangentSpace I b}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, W b⟩ : _root_.Bundle.TotalSpace E (TangentSpace I))))
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : _root_.Bundle.TotalSpace E (TangentSpace I))))
    (x : M) :
    (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)).toFun
        (fun y : M => contractCovariant 0 s y (X y) (V.toSection y)) x (W x) =
      contractCovariant 0 s x (X x)
          ((tensorRSCovariantDerivative I M 0 (s+1) (LeviCivita (I := I) g)).toFun
            (fun y : M => V.toSection y) x (W x))
        + contractCovariant 0 s x ((LeviCivita (I := I) g).toFun X x (W x)) (V.toSection x) := by
  classical
  have hsec : (fun y : M => contractCovariant 0 s y (X y) (V.toSection y)) =
      (fun y : M => tensor0SToTensorRS (I := I) (M := M) y
        (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s y
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s+1) I y from V.toSection y)
            (unitZeroSec (I := I) (M := M) y)) (X y))) := by
    funext y
    exact contract_eq_tensor0SAsRS_curry (I := I) (M := M) s y (X y) (V.toSection y)
  rw [hsec]
  rw [contract_eq_tensor0SAsRS_curry (I := I) (M := M) s x (X x)
    ((tensorRSCovariantDerivative I M 0 (s+1) (LeviCivita (I := I) g)).toFun
      (fun y : M => V.toSection y) x (W x))]
  rw [contract_eq_tensor0SAsRS_curry (I := I) (M := M) s x
    ((LeviCivita (I := I) g).toFun X x (W x)) (V.toSection x)]
  rw [rs_zero_recover (I := I) (M := M) s x
    ((tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)).toFun
      (fun y : M => tensor0SToTensorRS (I := I) (M := M) y
        (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s y
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (s+1) I y from V.toSection y)
            (unitZeroSec (I := I) (M := M) y)) (X y))) x (W x))]
  rw [← tensor0SAsRS_add]
  congr 1
  have hleib := tensor0S_curry_covApply_slot0_leibniz_fib (I := I) (M := M) g s V hW hX x
  rw [eq_sub_iff_add_eq] at hleib
  exact hleib.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.contract_covariant_leibniz
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.contract_covariant_leibniz target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
private lemma contract_covGrad_eq_covDeriv
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T : SmoothCcTensor g 0 s) (x : M)
    (v : TangentSpace I x) :
    contractCovariant 0 s x v ((covGrad (I := I) (M := M) g 0 s T).toSection x) =
      tensorCovDerivAt (I := I) (M := M) g 0 s T x
        (tangentSpaceModelContinuousLinearEquiv (I := I) x v) := by
  apply tensorRSSpace_ext 0 s x
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [contract_toModel_apply (I := I) (M := M) s x v _ D m]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g 0 s T x D
    (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x v) m)]
  rw [Fin.cons_zero, Matrix.vecTail,
    show (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x v) m ∘ Fin.succ) = m from by
      funext i
      simp]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.contract_covGrad_eq_covDeriv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.contract_covGrad_eq_covDeriv target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private lemma fiberNormSqComponent_contract (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (n : ℕ) (e : Fin n → TangentSpace I x) (i : Fin n)
    (A : TensorRSSpace 0 (s + 1) I x) (J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x 0 s
        (contractCovariant 0 s x (e i) A) n e (fun k => k.elim0) J =
      fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) A n e (fun k => k.elim0)
        (Fin.cons i J) := by
  unfold fiberNormSqComponent
  rw [contract_eval (I := I) (M := M) s x (e i) A _ (fun k => e (J k))]
  congr 1
  funext k
  refine Fin.cases ?_ ?_ k
  · simp
  · intro j; simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.fiberNormSqComponent_contract
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.fiberNormSqComponent_contract target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private lemma tensorInnerPointwise_succ_eq_sum_contract_orthoFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hn : n = Module.finrank ℝ E) (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (A B : TensorRSSpace 0 (s + 1) I x) :
    tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
        (TensorRSSpace.toModel A) (TensorRSSpace.toModel B) =
      ∑ i : Fin n,
        tensorInnerPointwise (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel (contractCovariant 0 s x (e i) A))
          (TensorRSSpace.toModel (contractCovariant 0 s x (e i) B)) := by
  classical
  rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g 0 (s + 1) x
    e bse hn hbse horth A B]
  rw [Finset.sum_eq_single (fun k : Fin 0 => k.elim0)]
  · rw [show (∑ i : Fin n,
          tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel (contractCovariant 0 s x (e i) A))
            (TensorRSSpace.toModel (contractCovariant 0 s x (e i) B))) =
        ∑ i : Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) A n e (fun k => k.elim0)
            (Fin.cons i J) *
          fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) B n e (fun k => k.elim0)
            (Fin.cons i J) from ?_]
    · rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (s + 1) => Fin n))
          (fun p : Fin n × (Fin s → Fin n) =>
            fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) A n e (fun k => k.elim0)
              (Fin.cons p.1 p.2) *
            fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) B n e (fun k => k.elim0)
              (Fin.cons p.1 p.2))
          (fun ψ : Fin (s + 1) → Fin n =>
            fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) A n e (fun k => k.elim0) ψ *
            fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) B n e (fun k => k.elim0) ψ)
          (fun p => rfl)]
      rw [Fintype.sum_prod_type]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g 0 s x
        e bse hn hbse horth (contractCovariant 0 s x (e i) A) (contractCovariant 0 s x (e i) B)]
      rw [Finset.sum_eq_single (fun k : Fin 0 => k.elim0)]
      · refine Finset.sum_congr rfl (fun J _ => ?_)
        rw [fiberNormSqComponent_contract (I := I) (M := M) g s x n e i A J,
          fiberNormSqComponent_contract (I := I) (M := M) g s x n e i B J]
      · intro K _ hK; exact absurd (funext fun k => k.elim0) hK
      · intro h; exact absurd (Finset.mem_univ _) h
  · intro K _ hK; exact absurd (funext fun k => k.elim0) hK
  · intro h; exact absurd (Finset.mem_univ _) h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorInnerPointwise_succ_eq_sum_contract_orthoFrame
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.tensorInnerPointwise_succ_eq_sum_contract_orthoFrame target :: scope.openDecls } }

private def contractFrameSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (b : M)
    (i : Fin (Module.finrank ℝ E)) :
    Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯ :=
  contractCovariantField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) 0 s
    V.toSection (smoothOrthoFrameSection (I := I) (M := M) g b i)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.contractFrameSection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.contractFrameSection target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma contractFrameSection_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (V : SmoothCcTensor g 0 (s + 1)) (b : M)
    (i : Fin (Module.finrank ℝ E)) (y : M) :
    contractFrameSection (I := I) (M := M) g s V b i y =
      contractCovariant 0 s y (smoothOrthoFrame (I := I) g b i y) (V.toSection y) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.contractFrameSection_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.contractFrameSection_apply target :: scope.openDecls } }

omit [CompactSpace M] [SigmaCompactSpace M] in
private lemma divergence_oneSidedVF_summand_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : SmoothCcTensor g 0 s) (V : SmoothCcTensor g 0 (s + 1)) (b : M)
    (i : Fin (Module.finrank ℝ E)) :
    g.inner b
        ((LeviCivita (I := I) g).toFun
          (oneSidedDirichletVFSection (I := I) (M := M) g s T V).toFun b
          (smoothOrthoFrame (I := I) g b i b))
        (smoothOrthoFrame (I := I) g b i b) =
      tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 s T b
              (tangentSpaceModelContinuousLinearEquiv (I := I) b
                (smoothOrthoFrame (I := I) g b i b))))
          (TensorRSSpace.toModel
            (contractCovariant 0 s b (smoothOrthoFrame (I := I) g b i b)
              (V.toSection b)))
        + tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel
            (contractCovariant 0 s b (smoothOrthoFrame (I := I) g b i b)
              ((tensorRSCovariantDerivative I M 0 (s + 1) (LeviCivita (I := I) g)).toFun
                (fun y : M => V.toSection y) b
                (smoothOrthoFrame (I := I) g b i b)))) := by
  classical
  set B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨fun y : M => smoothOrthoFrame (I := I) g b i y,
      smoothOrthoFrame_smooth (I := I) g b i⟩ with hB_def
  set Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    oneSidedDirichletVFSection (I := I) (M := M) g s T V with hZ_def
  set C : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯ :=
    contractFrameSection (I := I) (M := M) g s V b i with hC_def
  have hBb : (B : ∀ y, TangentSpace I y) b = smoothOrthoFrame (I := I) g b i b := rfl
  have hleib := leibniz_inner (I := I) g
    (V := fun y : M => Z y) (W := fun y : M => B y)
    Z.contMDiff B.contMDiff
    (x := b) ((B : ∀ y, TangentSpace I y) b)
  have hfun : (fun y : M => g.inner y (Z y) (B y)) =
      tensorInnerScalar (I := I) (M := M) g 0 s T.toSection C := by
    funext y
    rw [hZ_def, oneSidedDirichletVFSection_apply, inner_oneSidedDirichletVF,
      oneSidedDirichletForm_apply, tensorInnerScalar_apply]
    rfl
  have hprod : tangentSectionAction (I := I) B
        (fun y : M => g.inner y (Z y) (B y)) b =
      tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel
            (covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s T.toSection B b))
          (TensorRSSpace.toModel (C b))
        + tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel
            (covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s C B b)) := by
    have hint := loweringIntertwiner (I := I) (M := M) g s
    rw [show tangentSectionAction (I := I) B
            (fun y : M => g.inner y (Z y) (B y)) =
          tangentSectionAction (I := I) B
            (tensorInnerScalar (I := I) (M := M) g 0 s T.toSection C) from by rw [hfun]]
    rw [tangentSectionAction_tensorInnerScalar (I := I) (M := M) g 0 s
      T.toSection C B b]
    congr 1
    · rw [tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g 0 s
        (covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s T.toSection B) C b]
      rw [toModel_liftedTensorSection_covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s hint
        T.toSection B b]
    · rw [tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g 0 s
        T.toSection (covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s C B) b]
      rw [toModel_liftedTensorSection_covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s hint
        C B b]
  have haccel : g.inner b (Z b)
        ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
          ((B : ∀ y, TangentSpace I y) b)) =
      tensorInnerPointwise (I := I) (M := M) g 0 s b
        (TensorRSSpace.toModel (T.toSection b))
        (TensorRSSpace.toModel
          (contractCovariant 0 s b
            ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
              ((B : ∀ y, TangentSpace I y) b)) (V.toSection b))) := by
    rw [hZ_def, oneSidedDirichletVFSection_apply, inner_oneSidedDirichletVF,
      oneSidedDirichletForm_apply]
  have hCleib : covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s C B b =
      contractCovariant 0 s b ((B : ∀ y, TangentSpace I y) b)
          ((tensorRSCovariantDerivative I M 0 (s + 1) (LeviCivita (I := I) g)).toFun
            (fun y : M => V.toSection y) b ((B : ∀ y, TangentSpace I y) b))
        + contractCovariant 0 s b
          ((LeviCivita (I := I) g).toFun (fun y : M => B y) b ((B : ∀ y, TangentSpace I y) b))
          (V.toSection b) := by
    rw [show covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s C B b =
          (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)).toFun
            (fun y : M => C y) b ((B : ∀ y, TangentSpace I y) b) from rfl]
    rw [hC_def]
    exact contract_covariant_leibniz (I := I) (M := M) g s V
      (W := fun y : M => B y) (X := fun y : M => B y) B.contMDiff B.contMDiff b
  have hsummand : g.inner b
        ((LeviCivita (I := I) g).toFun (fun y : M => Z y) b
          ((B : ∀ y, TangentSpace I y) b))
        ((B : ∀ y, TangentSpace I y) b) =
      tangentSectionAction (I := I) B (fun y : M => g.inner y (Z y) (B y)) b
        - g.inner b (Z b)
          ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
            ((B : ∀ y, TangentSpace I y) b)) := by
    rw [tangentSectionAction_def]
    rw [hleib]; ring
  change g.inner b
      ((LeviCivita (I := I) g).toFun (fun y : M => Z y) b
        ((B : ∀ y, TangentSpace I y) b))
      ((B : ∀ y, TangentSpace I y) b) = _
  rw [hsummand, hprod, haccel]
  rw [hCleib, TensorRSSpace.toModel_add, tensorInnerPointwise_add_right]
  rw [show covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s T.toSection B b =
        tensorCovDerivAt (I := I) (M := M) g 0 s T b
          (tangentSpaceModelContinuousLinearEquiv (I := I) b
            ((B : ∀ y, TangentSpace I y) b)) from by
      rw [tensorCovDerivAt_def, ContinuousLinearEquiv.symm_apply_apply]
      rfl]
  rw [hC_def, contractFrameSection_apply]
  rw [hBb]
  rw [show (fun y : M => (B : ∀ z : M, TangentSpace I z) y) =
        (fun y : M => smoothOrthoFrame (I := I) g b i y) from rfl]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.divergence_oneSidedVF_summand_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.divergence_oneSidedVF_summand_eq target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
private lemma centeredFrame_basis_exists
    (g : SmoothRiemannianMetric I M) (b : M) :
    ∃ (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I b)),
      (∀ i, frame i = smoothOrthoFrame (I := I) g b i b) ∧
      (∀ i j, g.inner b (frame i) (frame j) = if i = j then (1 : ℝ) else 0) := by
  classical
  have hB_orth : ∀ i j, g.inner b
      (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b j b) =
      if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g b i j
  have hB_li : LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) => smoothOrthoFrame (I := I) g b i b) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner b (smoothOrthoFrame (I := I) g b k b)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g b j b) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs,
        g.inner b (smoothOrthoFrame (I := I) g b k b)
          (c j • smoothOrthoFrame (I := I) g b j b) =
        c j * g.inner b (smoothOrthoFrame (I := I) g b k b)
          (smoothOrthoFrame (I := I) g b j b) := by
      intro j _
      rw [(g.inner b (smoothOrthoFrame (I := I) g b k b)).map_smul
        (c j) (smoothOrthoFrame (I := I) g b j b), smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    have h_pull2 : ∀ j ∈ fs,
        c j * g.inner b (smoothOrthoFrame (I := I) g b k b)
          (smoothOrthoFrame (I := I) g b j b) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [hB_orth k j]
    rw [Finset.sum_congr rfl h_pull2] at h_zero
    rw [Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rw [if_pos rfl, mul_one] at h_zero
      exact h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), _root_.MulZeroClass.mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I b) := by
    rw [Fintype.card_fin]
    rfl
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hB_li hcard, ?_, ?_⟩
  · intro i
    change (basisOfLinearIndependentOfCardEqFinrank hB_li hcard :
        Fin (Module.finrank ℝ E) → TangentSpace I b) i = smoothOrthoFrame (I := I) g b i b
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  · intro i j
    rw [show (basisOfLinearIndependentOfCardEqFinrank hB_li hcard : Fin (Module.finrank ℝ E) →
      TangentSpace I b) i =
          smoothOrthoFrame (I := I) g b i b from by rw
                                                      [coe_basisOfLinearIndependentOfCardEqFinrank],
      show (basisOfLinearIndependentOfCardEqFinrank hB_li hcard : Fin (Module.finrank ℝ E) →
        TangentSpace I b) j =
          smoothOrthoFrame (I := I) g b j b from by rw
                                                      [coe_basisOfLinearIndependentOfCardEqFinrank]]
    exact hB_orth i j

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.centeredFrame_basis_exists
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.centeredFrame_basis_exists target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private lemma tip_sum_right
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (S : TensorRSModel 0 s ℝ E) {ι : Type*} (fs : Finset ι)
    (C : ι → TensorRSModel 0 s ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g 0 s b S (∑ i ∈ fs, C i) =
      ∑ i ∈ fs, tensorInnerPointwise (I := I) (M := M) g 0 s b S (C i) := by
  classical
  induction fs using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, tensorInnerPointwise_zero_right]
  | insert a fs ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        tensorInnerPointwise_add_right, ih]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.tip_sum_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.tip_sum_right target :: scope.openDecls } }

omit [CompactSpace M] [SigmaCompactSpace M] in
theorem divergence_oneSidedVF_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : SmoothCcTensor g 0 s) (V : SmoothCcTensor g 0 (s + 1)) (b : M) :
    divergenceG (I := I) g (oneSidedDirichletVFSection (I := I) (M := M) g s T V) b =
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) b
          (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g 0 s T).toSection b))
          (TensorRSSpace.toModel (V.toSection b))
        + tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b)) := by
  classical
  obtain ⟨frame, hframe_eq, hframe_orth⟩ :=
    centeredFrame_basis_exists (I := I) (M := M) g b
  have horth_e : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b j b) =
        if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g b i j
  rw [divergence_g_eq_smoothOrthoFrame_trace (I := I) g
    (oneSidedDirichletVFSection (I := I) (M := M) g s T V) b]
  rw [Finset.sum_congr rfl (fun i _ =>
    divergence_oneSidedVF_summand_eq (I := I) (M := M) g s T V b i)]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [tensorInnerPointwise_succ_eq_sum_contract_orthoFrame (I := I) (M := M) g s b
      (e := fun i => smoothOrthoFrame (I := I) g b i b) frame rfl hframe_eq horth_e
      ((covGrad (I := I) (M := M) g 0 s T).toSection b) (V.toSection b)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [contract_covGrad_eq_covDeriv (I := I) (M := M) g s T b
      (smoothOrthoFrame (I := I) g b i b)]
  · rw [covDivergenceRaw_eq_codiffPsi_smoothOrthoFrame_trace (I := I) (M := M) g s V b
      (fun i => smoothOrthoFrame (I := I) g b i b) horth_e]
    rw [show TensorRSSpace.toModel
          (∑ i : Fin (Module.finrank ℝ E),
            covDivergenceBilinear (I := I) (M := M) g s V b
              (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b i b)) =
        ∑ i : Fin (Module.finrank ℝ E),
          TensorRSSpace.toModel
            (covDivergenceBilinear (I := I) (M := M) g s V b
              (smoothOrthoFrame (I := I) g b i b)
              (smoothOrthoFrame (I := I) g b i b)) from by
      change (TensorRSSpace.toModelL (I := I) 0 s b)
          (∑ i : Fin (Module.finrank ℝ E),
            covDivergenceBilinear (I := I) (M := M) g s V b
              (smoothOrthoFrame (I := I) g b i b)
              (smoothOrthoFrame (I := I) g b i b)) =
        ∑ i : Fin (Module.finrank ℝ E),
          (TensorRSSpace.toModelL (I := I) 0 s b)
            (covDivergenceBilinear (I := I) (M := M) g s V b
              (smoothOrthoFrame (I := I) g b i b)
              (smoothOrthoFrame (I := I) g b i b))
      exact tensorRSSpace_toModelL_sum (I := I) (M := M) b Finset.univ _]
    rw [tip_sum_right (I := I) (M := M) g s b]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hcodiff : covDivergenceBilinear (I := I) (M := M) g s V b
          (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b i b) =
        contractCovariant 0 s b (smoothOrthoFrame (I := I) g b i b)
          ((tensorRSCovariantDerivative I M 0 (s + 1) (LeviCivita (I := I) g)).toFun
            (fun y : M => V.toSection y) b (smoothOrthoFrame (I := I) g b i b)) := by
      have hSmooth_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (fun z : M => TotalSpace.mk' E (E := fun w : M => TangentSpace I w) z
            (smoothOrthoFrame (I := I) g b i z)) b :=
        (smoothOrthoFrame_smooth (I := I) g b i).contMDiffAt.mdifferentiableAt (by simp)
      rw [codiffPsi_apply (I := I) (M := M) g s V b hSmooth_at hSmooth_at]
    rw [hcodiff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.divergence_oneSidedVF_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.divergence_oneSidedVF_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.divergence_oneSidedVF_eq ``Submission.DifferentialGeometry.Analysis.Elliptic.divergence_oneSidedVF_eq

omit [CompactSpace M] in
theorem tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : SmoothCcTensor g 0 s) (V : SmoothCcTensor g 0 (s + 1)) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s T).toFun V.toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s
          T.toFun (covDivergence (I := I) (M := M) g s V).toFun := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  set Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    oneSidedDirichletVFSection (I := I) (M := M) g s T V with hZ_def
  have hZ_cs : HasCompactSupport (Z : ∀ x, TangentSpace I x) := by
    refine HasCompactSupport.mono (f := T.toFun) T.hasCompactSupport ?_
    intro b hb
    change T.toFun b ≠ 0
    intro hTb
    apply hb
    by_contra hZb
    have hpos := g.pos b (Z b) hZb
    have hinner : g.inner b (Z b) (Z b) = 0 := by
      rw [hZ_def, oneSidedDirichletVFSection_apply, inner_oneSidedDirichletVF,
        oneSidedDirichletForm_apply]
      change tensorInnerPointwise (I := I) (M := M) g 0 s b (T.toFun b) _ = 0
      rw [hTb, tensorInnerPointwise_zero_left]
    linarith
  have hdiv_zero : ∫ b, divergenceG (I := I) g Z b ∂μ = 0 :=
    integral_divergence_eq_zero_of_hasCompactSupport (I := I) g Z hZ_cs
  have hpt : ∀ b : M, divergenceG (I := I) g Z b =
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) b
          (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g 0 s T).toSection b))
          (TensorRSSpace.toModel (V.toSection b))
        + tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b)) := by
    intro b; rw [hZ_def]; exact divergence_oneSidedVF_eq (I := I) (M := M) g s T V b
  rw [_root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)] at hdiv_zero
  have hcross_cont : Continuous
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) b
          (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g 0 s T).toSection b))
          (TensorRSSpace.toModel (V.toSection b))) :=
    (tensorInnerScalar_contMDiff (I := I) (M := M) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s T).toSection V.toSection).continuous
  have hsecond_cont : Continuous
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b))) := by
    have heq : (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b))) =
        (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel ((covDivergence (I := I) (M := M) g s V).toSection b))) := by
      funext b
      rw [covDivergence_toSection_apply]
    rw [heq]
    exact (tensorInnerScalar_contMDiff (I := I) (M := M) g 0 s
      T.toSection (covDivergence (I := I) (M := M) g s V).toSection).continuous
  have hcross_int : _root_.MeasureTheory.Integrable
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) b
          (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g 0 s T).toSection b))
          (TensorRSSpace.toModel (V.toSection b))) μ :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hcross_cont
      ((covGrad (I := I) (M := M) g 0 s T).hasCompactSupport_inner_cross V)
  have hsecond_int : _root_.MeasureTheory.Integrable
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel (T.toSection b))
          (TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b))) μ :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hsecond_cont (by
        simpa only [SmoothCcTensor.toFun_apply, covDivergence_toSection_apply] using
          T.hasCompactSupport_inner_cross (covDivergence (I := I) (M := M) g s V))
  rw [_root_.MeasureTheory.integral_add hcross_int hsecond_int] at hdiv_zero
  rw [show tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s T).toFun V.toFun =
      ∫ b, tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) b
          (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g 0 s T).toSection b))
          (TensorRSSpace.toModel (V.toSection b)) ∂μ from ?_]
  · rw [show tensorL2Inner (I := I) (M := M) g 0 s
          T.toFun (covDivergence (I := I) (M := M) g s V).toFun =
        ∫ b, tensorInnerPointwise (I := I) (M := M) g 0 s b
            (TensorRSSpace.toModel (T.toSection b))
            (TensorRSSpace.toModel (covDivergenceRaw (I := I) (M := M) g s V b)) ∂μ from ?_]
    · linarith [hdiv_zero]
    · unfold tensorL2Inner
      rw [← hμ_def]
      refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun b => ?_))
      simp only [SmoothCcTensor.toFun_apply, covDivergence_toSection_apply]
  · unfold tensorL2Inner
    rw [← hμ_def]
    refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun b => ?_))
    simp only [SmoothCcTensor.toFun_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence

end Elliptic
end Analysis
end DifferentialGeometry

end
