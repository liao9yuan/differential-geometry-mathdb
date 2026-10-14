import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovariantDerivativeBounds.SlotCorrection.ChartComponentFormula
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.Smoothness
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartLeviCivitaParallelCLMOpNorm
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.Tensor.SlotBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.Tensor.SlotChartSmoothness
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure

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

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Tensor
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private local instance slotChartKernelNormedAddCommGroup (r s : ℕ) :
    NormedAddCommGroup
      (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.slotChartKernelNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.slotChartKernelNormedAddCommGroup target :: scope.openDecls } }

private local instance slotChartKernelNormedSpace (r s : ℕ) :
    NormedSpace ℝ
      (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.slotChartKernelNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.slotChartKernelNormedSpace target :: scope.openDecls } }

private local instance slotChartKernelEndNormedAddCommGroup (r s : ℕ) :
    NormedAddCommGroup
      ((Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) →L[ℝ]
        (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E)) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.slotChartKernelEndNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.slotChartKernelEndNormedAddCommGroup target :: scope.openDecls } }

private local instance slotChartKernelEndNormedSpace (r s : ℕ) :
    NormedSpace ℝ
      ((Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) →L[ℝ]
        (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E)) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.slotChartKernelEndNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.slotChartKernelEndNormedSpace target :: scope.openDecls } }

def slotInputConjCLM (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M)
    (i : Fin r) : E →L[ℝ] E :=
  if i = k then
    (chartTrivializationLinearMap (I := I) (M := M) α b).comp
      ((tangentLinearMapToModel (I := I)
          (chartLeviCivitaParallelCLM (I := I) g α b B)).comp
        (chartTrivializationLinearMapSymm (I := I) (M := M) α b))
  else
    ContinuousLinearMap.id ℝ E

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.slotInputConjCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.slotInputConjCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.slotInputConjCLM ``Submission.DifferentialGeometry.Analysis.Elliptic.slotInputConjCLM

def slotOutputConjCLM (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M)
    (j : Fin s) : E →L[ℝ] E :=
  if j = l then
    (chartTrivializationLinearMap (I := I) (M := M) α b).comp
      ((tangentLinearMapToModel (I := I)
          (chartLeviCivitaParallelCLM (I := I) g α b B)).comp
        (chartTrivializationLinearMapSymm (I := I) (M := M) α b))
  else
    ContinuousLinearMap.id ℝ E

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.slotOutputConjCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.slotOutputConjCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.slotOutputConjCLM ``Submission.DifferentialGeometry.Analysis.Elliptic.slotOutputConjCLM

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] lemma slotInputConjCLM_self (g : SmoothRiemannianMetric I M) (r : ℕ)
    (α : M) (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M) :
    slotInputConjCLM (I := I) g r α B k b k =
      (chartTrivializationLinearMap (I := I) (M := M) α b).comp
        ((tangentLinearMapToModel (I := I)
            (chartLeviCivitaParallelCLM (I := I) g α b B)).comp
          (chartTrivializationLinearMapSymm (I := I) (M := M) α b)) := by
  unfold slotInputConjCLM
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.slotInputConjCLM_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.slotInputConjCLM_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.slotInputConjCLM_self ``Submission.DifferentialGeometry.Analysis.Elliptic.slotInputConjCLM_self

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] lemma slotInputConjCLM_other (g : SmoothRiemannianMetric I M) (r : ℕ)
    (α : M) (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M)
    {i : Fin r} (h : i ≠ k) :
    slotInputConjCLM (I := I) g r α B k b i = ContinuousLinearMap.id ℝ E := by
  unfold slotInputConjCLM
  simp [h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.slotInputConjCLM_other then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.slotInputConjCLM_other"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.slotInputConjCLM_other ``Submission.DifferentialGeometry.Analysis.Elliptic.slotInputConjCLM_other

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] lemma slotOutputConjCLM_self (g : SmoothRiemannianMetric I M) (s : ℕ)
    (α : M) (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M) :
    slotOutputConjCLM (I := I) g s α B l b l =
      (chartTrivializationLinearMap (I := I) (M := M) α b).comp
        ((tangentLinearMapToModel (I := I)
            (chartLeviCivitaParallelCLM (I := I) g α b B)).comp
          (chartTrivializationLinearMapSymm (I := I) (M := M) α b)) := by
  unfold slotOutputConjCLM
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.slotOutputConjCLM_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.slotOutputConjCLM_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.slotOutputConjCLM_self ``Submission.DifferentialGeometry.Analysis.Elliptic.slotOutputConjCLM_self

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] lemma slotOutputConjCLM_other (g : SmoothRiemannianMetric I M) (s : ℕ)
    (α : M) (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M)
    {j : Fin s} (h : j ≠ l) :
    slotOutputConjCLM (I := I) g s α B l b j = ContinuousLinearMap.id ℝ E := by
  unfold slotOutputConjCLM
  simp [h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.slotOutputConjCLM_other then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.slotOutputConjCLM_other"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.slotOutputConjCLM_other ``Submission.DifferentialGeometry.Analysis.Elliptic.slotOutputConjCLM_other

def inputSlotPrecompCLM (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M) :
    Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel r ℝ E :=
  ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (E := fun _ : Fin r => E) (F := ℝ)
    (slotInputConjCLM (I := I) g r α B k b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.inputSlotPrecompCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.inputSlotPrecompCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.inputSlotPrecompCLM ``Submission.DifferentialGeometry.Analysis.Elliptic.inputSlotPrecompCLM

def outputSlotPostcompCLM (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M) :
    Tensor0SModel s ℝ E →L[ℝ] Tensor0SModel s ℝ E :=
  ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (E := fun _ : Fin s => E) (F := ℝ)
    (slotOutputConjCLM (I := I) g s α B l b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.outputSlotPostcompCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.outputSlotPostcompCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.outputSlotPostcompCLM ``Submission.DifferentialGeometry.Analysis.Elliptic.outputSlotPostcompCLM

def inputSlotChartKernel (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M) :
    (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) →L[ℝ]
      (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) :=
  (ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
      (Tensor0SModel r ℝ E) (Tensor0SModel s ℝ E)).flip
    (inputSlotPrecompCLM (I := I) g r α B k b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel ``Submission.DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel

def outputSlotChartKernel (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M) :
    (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) →L[ℝ]
      (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) :=
  (ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
      (Tensor0SModel s ℝ E) (Tensor0SModel s ℝ E))
    (outputSlotPostcompCLM (I := I) g s α B l b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel ``Submission.DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] lemma inputSlotChartKernel_apply (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M)
    (S : Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) :
    inputSlotChartKernel (I := I) g r s α B k b S =
      S.comp (inputSlotPrecompCLM (I := I) g r α B k b) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] lemma outputSlotChartKernel_apply (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M)
    (S : Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) :
    outputSlotChartKernel (I := I) g r s α B l b S =
      (outputSlotPostcompCLM (I := I) g s α B l b).comp S := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma slotInputConjCLM_compCLM_compCLM_chartJ
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (k : Fin r)
    (α' : Tensor0SModel r ℝ E) :
    (α'.compContinuousLinearMap
        (slotInputConjCLM (I := I) g r α B k b)).compContinuousLinearMap
      (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b) =
    α'.compContinuousLinearMap
      (fun i : Fin r => (chartTrivializationLinearMap (I := I) (M := M) α b).comp
        (tangentLinearMapToModel (I := I)
          (tangentSlotCLM (I := I) r k
            (chartLeviCivitaParallelCLM (I := I) g α b B) i))) := by
  classical
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := hb
  have hfamily :
      (fun i : Fin r => (slotInputConjCLM (I := I) g r α B k b i).comp
          (chartTrivializationLinearMap (I := I) (M := M) α b)) =
      (fun i : Fin r => (chartTrivializationLinearMap (I := I) (M := M) α b).comp
          (tangentLinearMapToModel (I := I)
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b B) i))) := by
    funext i
    by_cases hik : i = k
    · subst hik
      rw [slotInputConjCLM_self, tangentSlotCLM_self]
      refine ContinuousLinearMap.ext ?_
      intro x
      change chartTrivializationLinearMap (I := I) (M := M) α b
          (tangentLinearMapToModel (I := I)
            (chartLeviCivitaParallelCLM (I := I) g α b B)
            (chartTrivializationLinearMapSymm (I := I) (M := M) α b
              (chartTrivializationLinearMap (I := I) (M := M) α b x))) =
        chartTrivializationLinearMap (I := I) (M := M) α b
          (tangentLinearMapToModel (I := I)
            (chartLeviCivitaParallelCLM (I := I) g α b B) x)
      rw [chartJinv_chartJ_self (I := I) (M := M) α hb_base]
    · rw [slotInputConjCLM_other (I := I) g r α B k b hik,
        tangentSlotCLM_other (I := I) r k _ hik]
      refine ContinuousLinearMap.ext ?_
      intro x
      change chartTrivializationLinearMap (I := I) (M := M) α b x =
        chartTrivializationLinearMap (I := I) (M := M) α b
          (tangentLinearMapToModel (I := I)
            (ContinuousLinearMap.id ℝ (TangentSpace I b)) x)
      rfl
  refine ContinuousMultilinearMap.ext ?_
  intro v
  have h_lhs_eq :
      (((α'.compContinuousLinearMap
            (slotInputConjCLM (I := I) g r α B k b)).compContinuousLinearMap
          (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)) v : ℝ) =
      α' (fun i : Fin r =>
        (slotInputConjCLM (I := I) g r α B k b i)
          (chartTrivializationLinearMap (I := I) (M := M) α b (v i))) := by
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [h_lhs_eq]
  have hfam_at_v : (fun i : Fin r =>
      (slotInputConjCLM (I := I) g r α B k b i)
        (chartTrivializationLinearMap (I := I) (M := M) α b (v i))) =
      (fun i : Fin r => (chartTrivializationLinearMap (I := I) (M := M) α b)
        (tangentLinearMapToModel (I := I)
          (tangentSlotCLM (I := I) r k
            (chartLeviCivitaParallelCLM (I := I) g α b B) i) (v i))) := by
    funext i
    have hi := congrFun hfamily i
    have h_at_v := congrArg (fun (T : E →L[ℝ] E) => T (v i)) hi
    simp only [ContinuousLinearMap.comp_apply] at h_at_v
    exact h_at_v
  rw [hfam_at_v]
  exact (ContinuousMultilinearMap.compContinuousLinearMap_apply _ _ _).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.slotInputConjCLM_compCLM_compCLM_chartJ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.slotInputConjCLM_compCLM_compCLM_chartJ target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma slotOutputConjCLM_compose_chartJinv
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (l : Fin s)
    (m : Fin s → E) (j : Fin s) :
    chartTrivializationLinearMapSymm (I := I) (M := M) α b
        (slotOutputConjCLM (I := I) g s α B l b j (m j)) =
      tangentSpaceModelContinuousLinearEquiv (I := I) b
        (tangentSlotCLM (I := I) s l
          (chartLeviCivitaParallelCLM (I := I) g α b B) j
          ((tangentSpaceModelContinuousLinearEquiv (I := I) b).symm
            (chartTrivializationLinearMapSymm (I := I) (M := M) α b (m j)))) := by
  classical
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := hb
  by_cases hjl : j = l
  · subst hjl
    rw [slotOutputConjCLM_self, tangentSlotCLM_self]
    change chartTrivializationLinearMapSymm (I := I) (M := M) α b
        (chartTrivializationLinearMap (I := I) (M := M) α b
          (tangentLinearMapToModel (I := I)
            (chartLeviCivitaParallelCLM (I := I) g α b B)
            (chartTrivializationLinearMapSymm (I := I) (M := M) α b (m j)))) = _
    rw [chartJinv_chartJ_self (I := I) (M := M) α hb_base]
    rfl
  · rw [slotOutputConjCLM_other (I := I) g s α B l b hjl,
      tangentSlotCLM_other (I := I) s l _ hjl]
    simp only [ContinuousLinearMap.id_apply, ContinuousLinearEquiv.apply_symm_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.slotOutputConjCLM_compose_chartJinv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.slotOutputConjCLM_compose_chartJinv target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem chartTensorRSInputSlotCorrection_chart_kernel_factorization
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (k : Fin r) :
    (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
      (chartTensorRSInputSlotCorrection (I := I) r s g α T B b k) =
    (inputSlotChartKernel (I := I) g r s α B k b)
      ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (T b)) := by
  classical
  refine ContinuousLinearMap.ext ?_
  intro α'
  refine ContinuousMultilinearMap.ext ?_
  intro w
  have hLHS_bridge :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
      r s α hb (chartTensorRSInputSlotCorrection (I := I) r s g α T B b k)
  have hRHS_bridge :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
      r s α hb (T b)
  have hLHS_eval :
      ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (chartTensorRSInputSlotCorrection (I := I) r s g α T B b k)
        α' w : ℝ) =
      Tensor0SSpace.eval
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (Tensor0SSpace.ofModel
            (α'.compContinuousLinearMap
              (fun i : Fin r =>
                (chartTrivializationLinearMap (I := I) (M := M) α b).comp
                  (tangentLinearMapToModel (I := I)
                    (tangentSlotCLM (I := I) r k
                      (chartLeviCivitaParallelCLM (I := I) g α b B) i))))))
        (fun j : Fin s =>
          (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm
            (chartTrivializationLinearMapSymm (I := I) (M := M) α b (w j))) := by
    rw [hLHS_bridge, chartRSTwistInv_apply]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have h_apply := chartTensorRSInputSlotCorrection_apply (I := I) r s g α T B b k
      (Tensor0SSpace.ofModel
        (α'.compContinuousLinearMap
          (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)))
      (fun j : Fin s =>
        (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm
          (chartTrivializationLinearMapSymm (I := I) (M := M) α b (w j)))
    have hsubst :
        (tensorSlotSubstCLM (I := I) r b
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b B))
            (Tensor0SSpace.ofModel
              (α'.compContinuousLinearMap
                (fun _ : Fin r =>
                  chartTrivializationLinearMap (I := I) (M := M) α b)))) =
        Tensor0SSpace.ofModel
          (α'.compContinuousLinearMap
            (fun i : Fin r =>
              (chartTrivializationLinearMap (I := I) (M := M) α b).comp
                (tangentLinearMapToModel (I := I)
                  (tangentSlotCLM (I := I) r k
                    (chartLeviCivitaParallelCLM (I := I) g α b B) i)))) := by
      apply Tensor0SSpace.toModel_injective
      refine ContinuousMultilinearMap.ext ?_
      intro v
      change Tensor0SSpace.toModel
          (tensorSlotSubstCLM (I := I) r b
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b B))
            (Tensor0SSpace.ofModel
              (α'.compContinuousLinearMap
                (fun _ : Fin r =>
                  chartTrivializationLinearMap (I := I) (M := M) α b)))) v =
        Tensor0SSpace.toModel
          (Tensor0SSpace.ofModel
            (α'.compContinuousLinearMap
              (fun i : Fin r =>
                (chartTrivializationLinearMap (I := I) (M := M) α b).comp
                  (tangentLinearMapToModel (I := I)
                    (tangentSlotCLM (I := I) r k
                      (chartLeviCivitaParallelCLM (I := I) g α b B) i))))) v
      rw [Tensor0SSpace.toModel_ofModel,
        Tensor0SSpace.toModel_apply_model_vector]
      change Tensor0SSpace.eval
          (tensorSlotSubstCLM (I := I) r b
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b B))
            (Tensor0SSpace.ofModel
              (α'.compContinuousLinearMap
                (fun _ : Fin r =>
                  chartTrivializationLinearMap (I := I) (M := M) α b))))
          (fun i : Fin r =>
            (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm (v i)) = _
      rw [tensorSlotSubstCLM_apply (I := I) r b
          (tangentSlotCLM (I := I) r k
            (chartLeviCivitaParallelCLM (I := I) g α b B))
          (Tensor0SSpace.ofModel
            (α'.compContinuousLinearMap
              (fun _ : Fin r =>
                chartTrivializationLinearMap (I := I) (M := M) α b)))
          (fun i : Fin r =>
            (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm (v i))]
      change α' (fun i : Fin r =>
          chartTrivializationLinearMap (I := I) (M := M) α b
            (tangentSpaceModelContinuousLinearEquiv (I := I) b
              (tangentSlotCLM (I := I) r k
                (chartLeviCivitaParallelCLM (I := I) g α b B) i
                ((tangentSpaceModelContinuousLinearEquiv (I := I) b).symm (v i))))) =
        α' (fun i : Fin r =>
          chartTrivializationLinearMap (I := I) (M := M) α b
            (tangentLinearMapToModel (I := I)
              (tangentSlotCLM (I := I) r k
                (chartLeviCivitaParallelCLM (I := I) g α b B) i) (v i)))
      rfl
    rw [hsubst] at h_apply
    exact h_apply
  have hRHS_eval :
      ((inputSlotChartKernel (I := I) g r s α B k b)
        ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (T b)) α' w : ℝ) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (α'.compContinuousLinearMap
            (fun i : Fin r => (chartTrivializationLinearMap (I := I) (M := M) α b).comp
              (tangentSlotCLM (I := I) r k
                (chartLeviCivitaParallelCLM (I := I) g α b B) i))))
        (fun j : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b (w j)) := by
    rw [inputSlotChartKernel_apply, ContinuousLinearMap.comp_apply,
      hRHS_bridge, chartRSTwistInv_apply]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have hkey :=
      slotInputConjCLM_compCLM_compCLM_chartJ (I := I) (M := M) g r α B hb k α'
    have h_unfold_precomp :
        ((inputSlotPrecompCLM (I := I) g r α B k b) α').compContinuousLinearMap
          (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b) =
        α'.compContinuousLinearMap
          (fun i : Fin r => (chartTrivializationLinearMap (I := I) (M := M) α b).comp
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b B) i)) := by
      unfold inputSlotPrecompCLM
      rw [ContinuousMultilinearMap.compContinuousLinearMapL_apply]
      exact hkey
    rw [h_unfold_precomp]
    rfl
  exact hLHS_eval.trans hRHS_eval.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.chartTensorRSInputSlotCorrection_chart_kernel_factorization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.chartTensorRSInputSlotCorrection_chart_kernel_factorization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.chartTensorRSInputSlotCorrection_chart_kernel_factorization ``Submission.DifferentialGeometry.Analysis.Elliptic.chartTensorRSInputSlotCorrection_chart_kernel_factorization

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem chartTensorRSOutputSlotCorrection_chart_kernel_factorization
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (l : Fin s) :
    (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
      (chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l) =
    (outputSlotChartKernel (I := I) g r s α B l b)
      ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (T b)) := by
  classical
  refine ContinuousLinearMap.ext ?_
  intro α'
  refine ContinuousMultilinearMap.ext ?_
  intro m
  have hLHS_bridge :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
      r s α hb (chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l)
  have hRHS_bridge :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
      r s α hb (T b)
  have hLHS_eval :
      ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l)
        α' m : ℝ) =
      Tensor0SSpace.eval
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (Tensor0SSpace.ofModel
            (α'.compContinuousLinearMap
              (fun _ : Fin r =>
                chartTrivializationLinearMap (I := I) (M := M) α b))))
        (fun j : Fin s =>
          tangentSlotCLM (I := I) s l
            (chartLeviCivitaParallelCLM (I := I) g α b B) j
            ((tangentSpaceModelContinuousLinearEquiv (I := I) b).symm
              (chartTrivializationLinearMapSymm (I := I) (M := M) α b (m j)))) := by
    rw [hLHS_bridge, chartRSTwistInv_apply]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    exact chartTensorRSOutputSlotCorrection_apply (I := I) r s g α T B b l
      (Tensor0SSpace.ofModel
        (α'.compContinuousLinearMap
          (fun _ : Fin r =>
            chartTrivializationLinearMap (I := I) (M := M) α b)))
      (fun j : Fin s =>
        (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm
          (chartTrivializationLinearMapSymm (I := I) (M := M) α b (m j)))
  have hRHS_eval :
      ((outputSlotChartKernel (I := I) g r s α B l b)
        ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (T b)) α' m : ℝ) =
      Tensor0SSpace.eval
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (Tensor0SSpace.ofModel
            (α'.compContinuousLinearMap
              (fun _ : Fin r =>
                chartTrivializationLinearMap (I := I) (M := M) α b))))
        (fun j : Fin s =>
          tangentSlotCLM (I := I) s l
            (chartLeviCivitaParallelCLM (I := I) g α b B) j
            ((tangentSpaceModelContinuousLinearEquiv (I := I) b).symm
              (chartTrivializationLinearMapSymm (I := I) (M := M) α b (m j)))) := by
    rw [outputSlotChartKernel_apply]
    rw [ContinuousLinearMap.comp_apply]
    rw [hRHS_bridge]
    unfold outputSlotPostcompCLM
    rw [ContinuousMultilinearMap.compContinuousLinearMapL_apply]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rw [chartRSTwistInv_apply]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext j
    exact slotOutputConjCLM_compose_chartJinv (I := I) (M := M) g s α B hb l m j
  exact hLHS_eval.trans hRHS_eval.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.chartTensorRSOutputSlotCorrection_chart_kernel_factorization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.chartTensorRSOutputSlotCorrection_chart_kernel_factorization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.chartTensorRSOutputSlotCorrection_chart_kernel_factorization ``Submission.DifferentialGeometry.Analysis.Elliptic.chartTensorRSOutputSlotCorrection_chart_kernel_factorization

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma chartLCConj_eq_christoffelCorrectionCLM
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) :
    (chartTrivializationLinearMap (I := I) (M := M) α b).comp
        ((tangentLinearMapToModel (I := I)
            (chartLeviCivitaParallelCLM (I := I) g α b X)).comp
          (chartTrivializationLinearMapSymm (I := I) (M := M) α b)) =
      christoffelCorrectionCLM (I := I) g α X b := by
  classical
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := hb
  refine ContinuousLinearMap.ext ?_
  intro w
  rw [ContinuousLinearMap.comp_apply]
  change chartTrivializationLinearMap (I := I) (M := M) α b
      (tangentLinearMapToModel (I := I)
        (chartLeviCivitaParallelCLM (I := I) g α b X)
        (chartTrivializationLinearMapSymm (I := I) (M := M) α b w)) = _
  rw [tangentLinearMapToModel_apply]
  rw [chartLeviCivitaParallelCLM_apply (I := I) g α b X
    ((tangentSpaceModelContinuousLinearEquiv (I := I) b).symm
      (chartTrivializationLinearMapSymm (I := I) (M := M) α b w))]
  change trivToE (I := I) α b
      (trivFromE (I := I) α b
        (christoffelCorrection (I := I) g α b
          (trivToE (I := I) α b (X b))
          (chartTrivializationLinearMapSymm (I := I) (M := M) α b w))) = _
  rw [trivToE_trivFromE (I := I) α hb_base]
  exact christoffelCorrection_eq_christoffelCorrectionCLM (I := I) g α X hb_base w

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.chartLCConj_eq_christoffelCorrectionCLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.chartLCConj_eq_christoffelCorrectionCLM target :: scope.openDecls } }

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartLCConj_contMDiffOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun b : M =>
        (chartTrivializationLinearMap (I := I) (M := M) α b).comp
          ((tangentLinearMapToModel (I := I)
              (chartLeviCivitaParallelCLM (I := I) g α b B.toFun)).comp
            (chartTrivializationLinearMapSymm (I := I) (M := M) α b)))
      ((chartAt H α).source) := by
  classical
  have hB_total : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := fun y : M => TangentSpace I y) x (B.toFun x)) := B.contMDiff
  have hB_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B.toFun : Π x : M, TangentSpace I x))
      (chartLeviCivitaGoodSet (I := I) α) := hB_total.contMDiffOn
  have hχ_good : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (christoffelCorrectionCLM (I := I) g α B.toFun)
      (chartLeviCivitaGoodSet (I := I) α) :=
    christoffelCorrectionCLM_contMDiffOn (I := I) g α hB_on
  have h_good_eq_source :
      chartLeviCivitaGoodSet (I := I) α = (chartAt H α).source := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α,
      extChartAt_source_eq_chartAt_source (I := I)]
  have hχ : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (christoffelCorrectionCLM (I := I) g α B.toFun)
      ((chartAt H α).source) := by
    rw [← h_good_eq_source]; exact hχ_good
  refine hχ.congr ?_
  intro b hb
  exact chartLCConj_eq_christoffelCorrectionCLM (I := I) (M := M) g α B.toFun hb

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.chartLCConj_contMDiffOn_chartSource
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.chartLCConj_contMDiffOn_chartSource target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma goodSet_image_isOpen (α : M) :
    IsOpen ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
  chartLeviCivitaGoodSet_image_isOpen (I := I) α

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.goodSet_image_isOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.goodSet_image_isOpen target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M]
    [SigmaCompactSpace M] in
private lemma goodSet_subset_chartSource (α : M) :
    chartLeviCivitaGoodSet (I := I) α ⊆ (chartAt H α).source := by
  intro b hb
  have h_eq :=
    chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α
  rw [h_eq, extChartAt_source_eq_chartAt_source (I := I)] at hb
  exact hb

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.goodSet_subset_chartSource
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.goodSet_subset_chartSource target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
private lemma extChartAt_mem_goodSet_image (α : M) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    extChartAt I α b ∈ (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
  ⟨b, hb, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.extChartAt_mem_goodSet_image
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.extChartAt_mem_goodSet_image target :: scope.openDecls } }

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartLCConj_chart_pulled_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContDiffOn ℝ ∞
      (fun y : E =>
        (chartTrivializationLinearMap (I := I) (M := M) α ((extChartAt I α).symm y)).comp
          ((tangentLinearMapToModel (I := I)
              (chartLeviCivitaParallelCLM (I := I) g α
                ((extChartAt I α).symm y) B.toFun)).comp
            (chartTrivializationLinearMapSymm (I := I) (M := M) α ((extChartAt I α).symm y))))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have hcm := chartLCConj_contMDiffOn_chartSource (I := I) (M := M) g α B
  set hgood_open : IsOpen (chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_isOpen (I := I) α
  intro y hy
  rcases hy with ⟨x, hxS, rfl⟩
  have hx_source : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hxS
  set F : M → E →L[ℝ] E := fun b : M =>
    (chartTrivializationLinearMap (I := I) (M := M) α b).comp
      ((tangentLinearMapToModel (I := I)
          (chartLeviCivitaParallelCLM (I := I) g α b B.toFun)).comp
        (chartTrivializationLinearMapSymm (I := I) (M := M) α b)) with hF_def
  have hF_at : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ F x := by
    have hopen_source : IsOpen (chartAt H α).source :=
      (chartAt H α).open_source
    exact hcm.contMDiffAt (hopen_source.mem_nhds hx_source)
  set φ := extChartAt I α
  have hxφ_source : x ∈ φ.source := by rw [extChartAt_source]; exact hx_source
  have hxφ_target : φ x ∈ φ.target := φ.map_source hxφ_source
  have hxφ_inv : φ.symm (φ x) = x := φ.left_inv hxφ_source
  have hsymm_on : ContMDiffOn 𝓘(ℝ, E) I (∞ : WithTop ℕ∞) φ.symm φ.target :=
    contMDiffOn_extChartAt_symm (I := I) (n := ∞) (x := α)
  have hsymm_at : ContMDiffWithinAt 𝓘(ℝ, E) I (∞ : WithTop ℕ∞)
      φ.symm φ.target (φ x) := hsymm_on (φ x) hxφ_target
  have hF_at' : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ F (φ.symm (φ x)) := by
    rw [hxφ_inv]; exact hF_at
  have hcomp_at : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞
      (F ∘ φ.symm) φ.target (φ x) :=
    hF_at'.comp_contMDiffWithinAt (φ x) hsymm_at
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at hcomp_at
  refine hcomp_at.mono ?_
  intro z hz
  rcases hz with ⟨x', hx'_good, rfl⟩
  exact interior_subset
    (chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx'_good)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.chartLCConj_chart_pulled_contDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.chartLCConj_chart_pulled_contDiffOn target :: scope.openDecls } }

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartLCConj_chart_pulled_contDiffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ ∞
      (fun y : E =>
        (chartTrivializationLinearMap (I := I) (M := M) α ((extChartAt I α).symm y)).comp
          ((tangentLinearMapToModel (I := I)
              (chartLeviCivitaParallelCLM (I := I) g α
                ((extChartAt I α).symm y) B.toFun)).comp
            (chartTrivializationLinearMapSymm (I := I) (M := M) α ((extChartAt I α).symm y))))
      (extChartAt I α b) := by
  classical
  have hOpen := goodSet_image_isOpen (I := I) (M := M) α
  have hmem : extChartAt I α b ∈
      (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
    extChartAt_mem_goodSet_image (I := I) (M := M) α hb
  exact (chartLCConj_chart_pulled_contDiffOn (I := I) (M := M) g α B).contDiffAt
    (hOpen.mem_nhds hmem)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.chartLCConj_chart_pulled_contDiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.chartLCConj_chart_pulled_contDiffAt target :: scope.openDecls } }

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma slotInputConjCLM_chart_pulled_contDiffAt
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) (i : Fin r) :
    ContDiffAt ℝ ∞
      (fun y : E =>
        slotInputConjCLM (I := I) g r α B.toFun k
          ((extChartAt I α).symm y) i)
      (extChartAt I α b) := by
  classical
  by_cases hik : i = k
  · subst hik
    have heq : (fun y : E =>
        slotInputConjCLM (I := I) g r α B.toFun i ((extChartAt I α).symm y) i) =
      (fun y : E =>
        (chartTrivializationLinearMap (I := I) (M := M) α ((extChartAt I α).symm y)).comp
          ((tangentLinearMapToModel (I := I)
              (chartLeviCivitaParallelCLM (I := I) g α
                ((extChartAt I α).symm y) B.toFun)).comp
            (chartTrivializationLinearMapSymm (I := I) (M := M) α ((extChartAt I α).symm y)))) := by
      funext y
      exact slotInputConjCLM_self (I := I) g r α B.toFun i ((extChartAt I α).symm y)
    rw [heq]
    exact chartLCConj_chart_pulled_contDiffAt (I := I) (M := M) g α B hb
  · have heq : (fun y : E =>
        slotInputConjCLM (I := I) g r α B.toFun k ((extChartAt I α).symm y) i) =
      (fun _ : E => ContinuousLinearMap.id ℝ E) := by
      funext y
      exact slotInputConjCLM_other (I := I) g r α B.toFun k _ hik
    rw [heq]
    exact contDiffAt_const

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.slotInputConjCLM_chart_pulled_contDiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.slotInputConjCLM_chart_pulled_contDiffAt target :: scope.openDecls } }

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma slotOutputConjCLM_chart_pulled_contDiffAt
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) (j : Fin s) :
    ContDiffAt ℝ ∞
      (fun y : E =>
        slotOutputConjCLM (I := I) g s α B.toFun l
          ((extChartAt I α).symm y) j)
      (extChartAt I α b) := by
  classical
  by_cases hjl : j = l
  · subst hjl
    have heq : (fun y : E =>
        slotOutputConjCLM (I := I) g s α B.toFun j ((extChartAt I α).symm y) j) =
      (fun y : E =>
        (chartTrivializationLinearMap (I := I) (M := M) α ((extChartAt I α).symm y)).comp
          ((tangentLinearMapToModel (I := I)
              (chartLeviCivitaParallelCLM (I := I) g α
                ((extChartAt I α).symm y) B.toFun)).comp
            (chartTrivializationLinearMapSymm (I := I) (M := M) α ((extChartAt I α).symm y)))) := by
      funext y
      exact slotOutputConjCLM_self (I := I) g s α B.toFun j ((extChartAt I α).symm y)
    rw [heq]
    exact chartLCConj_chart_pulled_contDiffAt (I := I) (M := M) g α B hb
  · have heq : (fun y : E =>
        slotOutputConjCLM (I := I) g s α B.toFun l ((extChartAt I α).symm y) j) =
      (fun _ : E => ContinuousLinearMap.id ℝ E) := by
      funext y
      exact slotOutputConjCLM_other (I := I) g s α B.toFun l _ hjl
    rw [heq]
    exact contDiffAt_const

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.slotOutputConjCLM_chart_pulled_contDiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.slotOutputConjCLM_chart_pulled_contDiffAt target :: scope.openDecls } }

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma inputSlotPrecompCLM_chart_pulled_contDiffAt
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ ∞
      (fun y : E =>
        inputSlotPrecompCLM (I := I) g r α B.toFun k
          ((extChartAt I α).symm y))
      (extChartAt I α b) := by
  classical
  set hmulti : ContinuousMultilinearMap ℝ (fun _ : Fin r => E →L[ℝ] E)
      ((ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ) :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
      ℝ (fun _ : Fin r => E) (fun _ : Fin r => E) ℝ with hmulti_def
  have hpi : ContDiffAt ℝ ∞
      (fun y : E =>
        fun i : Fin r => slotInputConjCLM (I := I) g r α B.toFun k
          ((extChartAt I α).symm y) i)
      (extChartAt I α b) := by
    refine contDiffAt_pi.mpr ?_
    intro i
    exact slotInputConjCLM_chart_pulled_contDiffAt (I := I) (M := M)
      g r α B k hb i
  have hcomposed :=
    (hmulti.contDiff (𝕜 := ℝ)).contDiffAt.comp (x := extChartAt I α b) hpi
  have h_eval :
      ∀ y : E,
        (hmulti
            (fun i : Fin r => slotInputConjCLM (I := I) g r α B.toFun k
              ((extChartAt I α).symm y) i)
          : ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ →L[ℝ]
              ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ) =
        inputSlotPrecompCLM (I := I) g r α B.toFun k
          ((extChartAt I α).symm y) := by
    intro y
    refine ContinuousLinearMap.ext ?_
    intro w
    rfl
  refine hcomposed.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  exact h_eval y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.inputSlotPrecompCLM_chart_pulled_contDiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.inputSlotPrecompCLM_chart_pulled_contDiffAt target :: scope.openDecls } }

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma outputSlotPostcompCLM_chart_pulled_contDiffAt
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ ∞
      (fun y : E =>
        outputSlotPostcompCLM (I := I) g s α B.toFun l
          ((extChartAt I α).symm y))
      (extChartAt I α b) := by
  classical
  set hmulti : ContinuousMultilinearMap ℝ (fun _ : Fin s => E →L[ℝ] E)
      ((ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
      ℝ (fun _ : Fin s => E) (fun _ : Fin s => E) ℝ with hmulti_def
  have hpi : ContDiffAt ℝ ∞
      (fun y : E =>
        fun j : Fin s => slotOutputConjCLM (I := I) g s α B.toFun l
          ((extChartAt I α).symm y) j)
      (extChartAt I α b) := by
    refine contDiffAt_pi.mpr ?_
    intro j
    exact slotOutputConjCLM_chart_pulled_contDiffAt (I := I) (M := M)
      g s α B l hb j
  have hcomposed :=
    (hmulti.contDiff (𝕜 := ℝ)).contDiffAt.comp (x := extChartAt I α b) hpi
  have h_eval :
      ∀ y : E,
        (hmulti
            (fun j : Fin s => slotOutputConjCLM (I := I) g s α B.toFun l
              ((extChartAt I α).symm y) j)
          : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ →L[ℝ]
              ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) =
        outputSlotPostcompCLM (I := I) g s α B.toFun l
          ((extChartAt I α).symm y) := by
    intro y
    refine ContinuousLinearMap.ext ?_
    intro w
    rfl
  refine hcomposed.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  exact h_eval y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.outputSlotPostcompCLM_chart_pulled_contDiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.outputSlotPostcompCLM_chart_pulled_contDiffAt target :: scope.openDecls } }

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem inputSlotChartKernel_contDiffAt_chart_pulled
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (k : Fin r) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ ∞
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                      ((extChartAt I α).symm y))
      (extChartAt I α b) := by
  classical
  have h_precomp := inputSlotPrecompCLM_chart_pulled_contDiffAt
    (I := I) (M := M) g r α B k hb
  have hL_smooth := ContinuousLinearMap.contDiff (n := ∞)
    (ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
      (Tensor0SModel r ℝ E) (Tensor0SModel s ℝ E)).flip
  have hcomposed := hL_smooth.contDiffAt.comp (x := extChartAt I α b) h_precomp
  refine hcomposed.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel_contDiffAt_chart_pulled then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel_contDiffAt_chart_pulled"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel_contDiffAt_chart_pulled ``Submission.DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel_contDiffAt_chart_pulled

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem outputSlotChartKernel_contDiffAt_chart_pulled
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (l : Fin s) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ ∞
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                      ((extChartAt I α).symm y))
      (extChartAt I α b) := by
  classical
  have h_postcomp := outputSlotPostcompCLM_chart_pulled_contDiffAt
    (I := I) (M := M) g s α B l hb
  have hL_smooth := ContinuousLinearMap.contDiff (n := ∞)
    (ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
      (Tensor0SModel s ℝ E) (Tensor0SModel s ℝ E))
  have hcomposed := hL_smooth.contDiffAt.comp (x := extChartAt I α b) h_postcomp
  refine hcomposed.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel_contDiffAt_chart_pulled then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel_contDiffAt_chart_pulled"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel_contDiffAt_chart_pulled ``Submission.DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel_contDiffAt_chart_pulled

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma chartLCConj_opNorm_le (g : SmoothRiemannianMetric I M) (α b : M)
    (X : Π b' : M, TangentSpace I b') :
    ‖(chartTrivializationLinearMap (I := I) (M := M) α b).comp
        ((tangentLinearMapToModel (I := I)
            (chartLeviCivitaParallelCLM (I := I) g α b X)).comp
          (chartTrivializationLinearMapSymm (I := I) (M := M) α b))‖ ≤
      ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ *
        (‖chartLeviCivitaParallelCLM (I := I) g α b X‖ *
          ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖) := by
  have hmodel_norm :
      ‖tangentLinearMapToModel (I := I)
        (chartLeviCivitaParallelCLM (I := I) g α b X)‖ =
      ‖chartLeviCivitaParallelCLM (I := I) g α b X‖ := by
    rfl
  refine ContinuousLinearMap.opNorm_comp_le _ _ |>.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine ContinuousLinearMap.opNorm_comp_le _ _ |>.trans ?_
  rw [hmodel_norm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.chartLCConj_opNorm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.chartLCConj_opNorm_le target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma slotInputConjCLM_opNorm_le (g : SmoothRiemannianMetric I M)
    (r : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M)
    (i : Fin r) :
    ‖slotInputConjCLM (I := I) g r α B k b i‖ ≤
      _root_.Max.max 1
        (‖chartTrivializationLinearMap (I := I) (M := M) α b‖ *
          (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
            ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖)) := by
  classical
  by_cases hik : i = k
  · subst hik
    rw [slotInputConjCLM_self]
    refine le_trans (chartLCConj_opNorm_le (I := I) (M := M) g α b B) ?_
    exact le_max_right _ _
  · rw [slotInputConjCLM_other (I := I) g r α B k b hik]
    refine ContinuousLinearMap.norm_id_le.trans ?_
    exact le_max_left _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.slotInputConjCLM_opNorm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.slotInputConjCLM_opNorm_le target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma slotOutputConjCLM_opNorm_le (g : SmoothRiemannianMetric I M)
    (s : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M)
    (j : Fin s) :
    ‖slotOutputConjCLM (I := I) g s α B l b j‖ ≤
      _root_.Max.max 1
        (‖chartTrivializationLinearMap (I := I) (M := M) α b‖ *
          (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
            ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖)) := by
  classical
  by_cases hjl : j = l
  · subst hjl
    rw [slotOutputConjCLM_self]
    refine le_trans (chartLCConj_opNorm_le (I := I) (M := M) g α b B) ?_
    exact le_max_right _ _
  · rw [slotOutputConjCLM_other (I := I) g s α B l b hjl]
    refine ContinuousLinearMap.norm_id_le.trans ?_
    exact le_max_left _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.slotOutputConjCLM_opNorm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.slotOutputConjCLM_opNorm_le target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma slotInputConjCLM_prod_opNorm_le (g : SmoothRiemannianMetric I M)
    (r : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M) :
    (∏ i : Fin r, ‖slotInputConjCLM (I := I) g r α B k b i‖) ≤
      (_root_.Max.max 1
        (‖chartTrivializationLinearMap (I := I) (M := M) α b‖ *
          (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
            ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖))) ^ r := by
  classical
  set M_b : ℝ := _root_.Max.max 1
    (‖chartTrivializationLinearMap (I := I) (M := M) α b‖ *
      (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
        ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖)) with hM_def
  have h_pow : M_b ^ r = ∏ _i : Fin r, M_b := by
    rw [Finset.prod_const]; simp
  rw [h_pow]
  refine Finset.prod_le_prod ?_ ?_
  · intro i _; exact norm_nonneg _
  · intro i _; exact slotInputConjCLM_opNorm_le (I := I) (M := M) g r α B k b i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.slotInputConjCLM_prod_opNorm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.slotInputConjCLM_prod_opNorm_le target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma slotOutputConjCLM_prod_opNorm_le (g : SmoothRiemannianMetric I M)
    (s : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M) :
    (∏ j : Fin s, ‖slotOutputConjCLM (I := I) g s α B l b j‖) ≤
      (_root_.Max.max 1
        (‖chartTrivializationLinearMap (I := I) (M := M) α b‖ *
          (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
            ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖))) ^ s := by
  classical
  set M_b : ℝ := _root_.Max.max 1
    (‖chartTrivializationLinearMap (I := I) (M := M) α b‖ *
      (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
        ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖)) with hM_def
  have h_pow : M_b ^ s = ∏ _j : Fin s, M_b := by
    rw [Finset.prod_const]; simp
  rw [h_pow]
  refine Finset.prod_le_prod ?_ ?_
  · intro j _; exact norm_nonneg _
  · intro j _; exact slotOutputConjCLM_opNorm_le (I := I) (M := M) g s α B l b j

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.slotOutputConjCLM_prod_opNorm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.slotOutputConjCLM_prod_opNorm_le target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma inputSlotPrecompCLM_opNorm_le (g : SmoothRiemannianMetric I M)
    (r : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M) :
    ‖inputSlotPrecompCLM (I := I) g r α B k b‖ ≤
      (_root_.Max.max 1
        (‖chartTrivializationLinearMap (I := I) (M := M) α b‖ *
          (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
            ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖))) ^ r := by
  classical
  unfold inputSlotPrecompCLM
  refine le_trans
    (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le
      (𝕜 := ℝ) (E := fun _ : Fin r => E) ℝ _) ?_
  exact slotInputConjCLM_prod_opNorm_le (I := I) (M := M) g r α B k b

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.inputSlotPrecompCLM_opNorm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.inputSlotPrecompCLM_opNorm_le target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma outputSlotPostcompCLM_opNorm_le (g : SmoothRiemannianMetric I M)
    (s : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M) :
    ‖outputSlotPostcompCLM (I := I) g s α B l b‖ ≤
      (_root_.Max.max 1
        (‖chartTrivializationLinearMap (I := I) (M := M) α b‖ *
          (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
            ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖))) ^ s := by
  classical
  unfold outputSlotPostcompCLM
  refine le_trans
    (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le
      (𝕜 := ℝ) (E := fun _ : Fin s => E) ℝ _) ?_
  exact slotOutputConjCLM_prod_opNorm_le (I := I) (M := M) g s α B l b

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.outputSlotPostcompCLM_opNorm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.outputSlotPostcompCLM_opNorm_le target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma inputSlotChartKernel_opNorm_le (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M) :
    ‖inputSlotChartKernel (I := I) g r s α B k b‖ ≤
      ‖inputSlotPrecompCLM (I := I) g r α B k b‖ := by
  classical
  unfold inputSlotChartKernel
  refine le_trans ((ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
    (Tensor0SModel r ℝ E) (Tensor0SModel s ℝ E)).flip.le_opNorm _) ?_
  rw [ContinuousLinearMap.opNorm_flip]
  have h_le := ContinuousLinearMap.norm_compL_le (𝕜 := ℝ)
    (E := Tensor0SModel r ℝ E) (Fₗ := Tensor0SModel r ℝ E)
    (Gₗ := Tensor0SModel s ℝ E)
  have h_nn : 0 ≤ ‖inputSlotPrecompCLM (I := I) g r α B k b‖ := norm_nonneg _
  refine le_trans (mul_le_mul_of_nonneg_right h_le h_nn) ?_
  rw [one_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel_opNorm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel_opNorm_le target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma outputSlotChartKernel_opNorm_le (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M) :
    ‖outputSlotChartKernel (I := I) g r s α B l b‖ ≤
      ‖outputSlotPostcompCLM (I := I) g s α B l b‖ := by
  classical
  unfold outputSlotChartKernel
  refine le_trans ((ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
    (Tensor0SModel s ℝ E) (Tensor0SModel s ℝ E)).le_opNorm _) ?_
  have h_le := ContinuousLinearMap.norm_compL_le (𝕜 := ℝ)
    (E := Tensor0SModel r ℝ E) (Fₗ := Tensor0SModel s ℝ E)
    (Gₗ := Tensor0SModel s ℝ E)
  have h_nn : 0 ≤ ‖outputSlotPostcompCLM (I := I) g s α B l b‖ := norm_nonneg _
  refine le_trans (mul_le_mul_of_nonneg_right h_le h_nn) ?_
  rw [one_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel_opNorm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel_opNorm_le target :: scope.openDecls } }

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem inputSlotChartKernel_chart_pulled_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r) :
    ContDiffOn ℝ ∞
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                      ((extChartAt I α).symm y))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have hL_smooth := ContinuousLinearMap.contDiff (n := ∞)
    (ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
      (Tensor0SModel r ℝ E) (Tensor0SModel s ℝ E)).flip
  intro y hy
  obtain ⟨b, hb_good, hyb⟩ := hy
  subst hyb
  have h_precomp_at := inputSlotPrecompCLM_chart_pulled_contDiffAt
    (I := I) (M := M) g r α B k hb_good
  have hcomposed := hL_smooth.contDiffAt.comp (x := extChartAt I α b) h_precomp_at
  have h_at : ContDiffAt ℝ ∞
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                      ((extChartAt I α).symm y))
      (extChartAt I α b) := by
    refine hcomposed.congr_of_eventuallyEq ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    rfl
  exact h_at.contDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel_chart_pulled_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel_chart_pulled_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel_chart_pulled_contDiffOn ``Submission.DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel_chart_pulled_contDiffOn

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem outputSlotChartKernel_chart_pulled_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s) :
    ContDiffOn ℝ ∞
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                      ((extChartAt I α).symm y))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have hL_smooth := ContinuousLinearMap.contDiff (n := ∞)
    (ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
      (Tensor0SModel s ℝ E) (Tensor0SModel s ℝ E))
  intro y hy
  obtain ⟨b, hb_good, hyb⟩ := hy
  subst hyb
  have h_postcomp_at := outputSlotPostcompCLM_chart_pulled_contDiffAt
    (I := I) (M := M) g s α B l hb_good
  have hcomposed := hL_smooth.contDiffAt.comp (x := extChartAt I α b) h_postcomp_at
  have h_at : ContDiffAt ℝ ∞
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                      ((extChartAt I α).symm y))
      (extChartAt I α b) := by
    refine hcomposed.congr_of_eventuallyEq ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    rfl
  exact h_at.contDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel_chart_pulled_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel_chart_pulled_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel_chart_pulled_contDiffOn ``Submission.DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel_chart_pulled_contDiffOn

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma inputSlotChartKernel_fderiv_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r) :
    ContinuousOn
      (fun y : E => ‖fderiv ℝ
        (fun y' : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                        ((extChartAt I α).symm y')) y‖)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have hcd := inputSlotChartKernel_chart_pulled_contDiffOn (I := I) (M := M)
    g r s α B k
  have hOpen := goodSet_image_isOpen (I := I) (M := M) α
  have hfd_cd : ContDiffOn ℝ ∞
      (fderiv ℝ (fun y' : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                        ((extChartAt I α).symm y')))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
    have h_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by rw [ENat.coe_top_add_one]
    exact hcd.fderiv_of_isOpen hOpen h_le
  exact continuous_norm.comp_continuousOn hfd_cd.continuousOn

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel_fderiv_continuousOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel_fderiv_continuousOn target :: scope.openDecls } }

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma outputSlotChartKernel_fderiv_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s) :
    ContinuousOn
      (fun y : E => ‖fderiv ℝ
        (fun y' : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                        ((extChartAt I α).symm y')) y‖)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have hcd := outputSlotChartKernel_chart_pulled_contDiffOn (I := I) (M := M)
    g r s α B l
  have hOpen := goodSet_image_isOpen (I := I) (M := M) α
  have hfd_cd : ContDiffOn ℝ ∞
      (fderiv ℝ (fun y' : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                        ((extChartAt I α).symm y')))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
    have h_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by rw [ENat.coe_top_add_one]
    exact hcd.fderiv_of_isOpen hOpen h_le
  exact continuous_norm.comp_continuousOn hfd_cd.continuousOn

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel_fderiv_continuousOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel_fderiv_continuousOn target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem inputSlotChartKernel_fderiv_opNorm_uniform_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖fderiv ℝ
            (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                            ((extChartAt I α).symm y))
            (extChartAt I α b)‖ ≤ K := by
  classical
  set K_set : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hcont := inputSlotChartKernel_fderiv_continuousOn (I := I) (M := M)
    g r s α B k
  have hK_sub : K_set ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  have hK_sub_good : K_set ⊆ chartLeviCivitaGoodSet (I := I) α := by
    intro b hb
    have h_eq :=
      chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α
    rw [h_eq, extChartAt_source_eq_chartAt_source (I := I)]
    exact hK_sub hb
  have hmaps : Set.MapsTo (extChartAt I α) K_set
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    fun b hb => ⟨b, hK_sub_good hb, rfl⟩
  have hφ_cm : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
    contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
  have hφ_cont : ContinuousOn (extChartAt I α) K_set :=
    (hφ_cm.continuousOn).mono hK_sub
  have hcont_M : ContinuousOn (fun b : M =>
      ‖fderiv ℝ
        (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                        ((extChartAt I α).symm y)) (extChartAt I α b)‖) K_set :=
    hcont.comp hφ_cont hmaps
  obtain ⟨C, hC_mem⟩ := hK_compact.bddAbove_image hcont_M
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro b hb
  have hb_K : b ∈ K_set := hb.1
  have h := hC_mem ⟨b, hb_K, rfl⟩
  exact le_trans h (le_max_left _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel_fderiv_opNorm_uniform_on_pouTsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel_fderiv_opNorm_uniform_on_pouTsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel_fderiv_opNorm_uniform_on_pouTsupport ``Submission.DifferentialGeometry.Analysis.Elliptic.inputSlotChartKernel_fderiv_opNorm_uniform_on_pouTsupport

omit [NeZero (Module.finrank ℝ E)] in
theorem outputSlotChartKernel_fderiv_opNorm_uniform_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖fderiv ℝ
            (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                            ((extChartAt I α).symm y))
            (extChartAt I α b)‖ ≤ K := by
  classical
  set K_set : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hcont := outputSlotChartKernel_fderiv_continuousOn (I := I) (M := M)
    g r s α B l
  have hK_sub : K_set ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  have hK_sub_good : K_set ⊆ chartLeviCivitaGoodSet (I := I) α := by
    intro b hb
    have h_eq :=
      chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α
    rw [h_eq, extChartAt_source_eq_chartAt_source (I := I)]
    exact hK_sub hb
  have hmaps : Set.MapsTo (extChartAt I α) K_set
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    fun b hb => ⟨b, hK_sub_good hb, rfl⟩
  have hφ_cm : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
    contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
  have hφ_cont : ContinuousOn (extChartAt I α) K_set :=
    (hφ_cm.continuousOn).mono hK_sub
  have hcont_M : ContinuousOn (fun b : M =>
      ‖fderiv ℝ
        (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                        ((extChartAt I α).symm y)) (extChartAt I α b)‖) K_set :=
    hcont.comp hφ_cont hmaps
  obtain ⟨C, hC_mem⟩ := hK_compact.bddAbove_image hcont_M
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro b hb
  have hb_K : b ∈ K_set := hb.1
  have h := hC_mem ⟨b, hb_K, rfl⟩
  exact le_trans h (le_max_left _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel_fderiv_opNorm_uniform_on_pouTsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel_fderiv_opNorm_uniform_on_pouTsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel_fderiv_opNorm_uniform_on_pouTsupport ``Submission.DifferentialGeometry.Analysis.Elliptic.outputSlotChartKernel_fderiv_opNorm_uniform_on_pouTsupport

end Elliptic
end Analysis
end DifferentialGeometry

end
