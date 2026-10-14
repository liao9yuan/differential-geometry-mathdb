import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.CoefficientFields
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.PalatiniDecomposition.PathLinearization
import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.ConnectionDifference.CovariantDerivative
import Submission.DifferentialGeometry.Geometry.Metric.DeTurck.ConnectionDifference.Identities
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.ModelProduct

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.MeasureTheory _root_.intervalIntegral
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix _root_.Submission.Matrix _root_.Interval

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

def permOfImages {n : ℕ} (f g : Fin n → Fin n)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : Equiv.Perm (Fin n) :=
  ⟨f, g, h₁, h₂⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.permOfImages then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.permOfImages"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.permOfImages ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.permOfImages

def perm210 : Equiv.Perm (Fin 2) :=
  permOfImages ![1, 0] ![1, 0] (by decide) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm210 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm210"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm210 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm210

def perm3102 : Equiv.Perm (Fin 3) :=
  permOfImages ![1, 0, 2] ![1, 0, 2] (by decide) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm3102 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm3102"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm3102 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm3102

def perm3120 : Equiv.Perm (Fin 3) :=
  permOfImages ![1, 2, 0] ![2, 0, 1] (by decide) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm3120 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm3120"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm3120 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm3120

def perm40312 : Equiv.Perm (Fin 4) :=
  permOfImages ![0, 3, 1, 2] ![0, 2, 3, 1] (by decide) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm40312 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm40312"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm40312 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm40312

def perm40213 : Equiv.Perm (Fin 4) :=
  permOfImages ![0, 2, 1, 3] ![0, 2, 1, 3] (by decide) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm40213 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm40213"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm40213 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm40213

def perm42301 : Equiv.Perm (Fin 4) :=
  permOfImages ![2, 3, 0, 1] ![2, 3, 0, 1] (by decide) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm42301 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm42301"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm42301 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm42301

def perm41302 : Equiv.Perm (Fin 4) :=
  permOfImages ![1, 3, 0, 2] ![2, 0, 3, 1] (by decide) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm41302 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm41302"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm41302 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm41302

def perm41203 : Equiv.Perm (Fin 4) :=
  permOfImages ![1, 2, 0, 3] ![2, 0, 1, 3] (by decide) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm41203 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm41203"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm41203 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm41203

def perm43012 : Equiv.Perm (Fin 4) :=
  permOfImages ![3, 0, 1, 2] ![1, 2, 3, 0] (by decide) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm43012 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm43012"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm43012 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm43012

def perm42013 : Equiv.Perm (Fin 4) :=
  permOfImages ![2, 0, 1, 3] ![1, 2, 0, 3] (by decide) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm42013 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm42013"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm42013 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm42013

def perm43201 : Equiv.Perm (Fin 4) :=
  permOfImages ![3, 2, 0, 1] ![2, 3, 1, 0] (by decide) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm43201 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm43201"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm43201 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm43201

def perm43102 : Equiv.Perm (Fin 4) :=
  permOfImages ![3, 1, 0, 2] ![2, 1, 3, 0] (by decide) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm43102 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm43102"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm43102 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm43102

def perm42103 : Equiv.Perm (Fin 4) :=
  permOfImages ![2, 1, 0, 3] ![2, 1, 0, 3] (by decide) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm42103 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm42103"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm42103 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm42103

def perm40231 : Equiv.Perm (Fin 4) :=
  permOfImages ![0, 2, 3, 1] ![0, 3, 1, 2] (by decide) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm40231 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm40231"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm40231 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm40231

def perm40321 : Equiv.Perm (Fin 4) :=
  permOfImages ![0, 3, 2, 1] ![0, 3, 2, 1] (by decide) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm40321 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm40321"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm40321 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.perm40321

noncomputable def slotPermCLM {d : ℕ} (ρ : Equiv.Perm (Fin d)) (x : M) :
    Tensor0SBundle.Tensor0SSpace d I x →L[ℝ] Tensor0SBundle.Tensor0SSpace d I x :=
  (Tensor0SBundle.tensor0SSpaceContinuousLinearEquiv (I := I) d x).symm.toContinuousLinearMap.comp
    (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
          ρ).toContinuousLinearEquiv.toContinuousLinearMap).comp
      (Tensor0SBundle.tensor0SSpaceContinuousLinearEquiv (I := I) d x).toContinuousLinearMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem slotPermCLM_apply {d : ℕ} (ρ : Equiv.Perm (Fin d)) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace d I x) :
    slotPermCLM (I := I) ρ x D =
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr ρ
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
  rw [slotPermCLM]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM_apply

noncomputable def tensorProdWithCLM (m k : ℕ) (x : M)
    (P : Tensor0SBundle.Tensor0SSpace m I x) :
    Tensor0SBundle.Tensor0SSpace k I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (m + k) I x :=
  (Tensor0SBundle.tensor0SSpaceContinuousLinearEquiv (I := I)
      (m + k) x).symm.toContinuousLinearMap.comp
    ((Bundle.continuousMultilinearMap.modelProductL (𝕜 := ℝ) (F := E) m k
        (Tensor0SBundle.Tensor0SSpace.toModel P)).comp
      (Tensor0SBundle.tensor0SSpaceContinuousLinearEquiv (I := I) k x).toContinuousLinearMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorProdWithCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorProdWithCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorProdWithCLM ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorProdWithCLM

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem tensorProdWithCLM_apply (m k : ℕ) (x : M)
    (P : Tensor0SBundle.Tensor0SSpace m I x) (Q : Tensor0SBundle.Tensor0SSpace k I x) :
    tensorProdWithCLM (I := I) m k x P Q =
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m k
          (Tensor0SBundle.Tensor0SSpace.toModel P)
          (Tensor0SBundle.Tensor0SSpace.toModel Q)) := by
  rw [tensorProdWithCLM]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, Bundle.continuousMultilinearMap.modelProductL_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorProdWithCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorProdWithCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorProdWithCLM_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorProdWithCLM_apply

noncomputable def tensorProdPairCLM (m k : ℕ) (x : M) :
    Tensor0SBundle.Tensor0SSpace m I x →L[ℝ]
      Tensor0SBundle.Tensor0SSpace k I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (m + k) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SBundle.Tensor0SSpace m I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun P => tensorProdWithCLM (I := I) m k x P
      map_add' := fun P₁ P₂ => by
        apply ContinuousLinearMap.ext
        intro Q
        have hsplit : Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m k
            (Tensor0SBundle.Tensor0SSpace.toModel P₁ + Tensor0SBundle.Tensor0SSpace.toModel P₂)
            (Tensor0SBundle.Tensor0SSpace.toModel Q) =
          Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m k
              (Tensor0SBundle.Tensor0SSpace.toModel P₁) (Tensor0SBundle.Tensor0SSpace.toModel Q)
            + Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m k
              (Tensor0SBundle.Tensor0SSpace.toModel P₂)
              (Tensor0SBundle.Tensor0SSpace.toModel Q) := by
          apply ContinuousMultilinearMap.ext
          intro v
          simp only [Bundle.continuousMultilinearMap.modelProduct_apply, add_apply, add_mul]
        rw [add_apply, tensorProdWithCLM_apply, tensorProdWithCLM_apply,
          tensorProdWithCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_add, hsplit]
        exact map_add
          ((Tensor0SBundle.tensor0SSpaceContinuousLinearEquiv (I := I) (m + k) x).symm) _ _
      map_smul' := fun c P => by
        apply ContinuousLinearMap.ext
        intro Q
        have hsplit : Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m k
            (c • Tensor0SBundle.Tensor0SSpace.toModel P)
            (Tensor0SBundle.Tensor0SSpace.toModel Q) =
          c • Bundle.continuousMultilinearMap.modelProduct (𝕜 := ℝ) (F := E) m k
              (Tensor0SBundle.Tensor0SSpace.toModel P)
              (Tensor0SBundle.Tensor0SSpace.toModel Q) := by
          apply ContinuousMultilinearMap.ext
          intro v
          simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
            smul_apply, smul_eq_mul]
          ring
        rw [RingHom.id_apply, smul_apply, tensorProdWithCLM_apply,
          tensorProdWithCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_smul, hsplit]
        exact map_smul
          ((Tensor0SBundle.tensor0SSpaceContinuousLinearEquiv (I := I) (m + k) x).symm) c _ }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorProdPairCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorProdPairCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorProdPairCLM ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorProdPairCLM

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem tensorProdPairCLM_apply (m k : ℕ) (x : M)
    (P : Tensor0SBundle.Tensor0SSpace m I x) :
    tensorProdPairCLM (I := I) m k x P = tensorProdWithCLM (I := I) m k x P := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorProdPairCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorProdPairCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorProdPairCLM_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorProdPairCLM_apply

noncomputable def contractUnitCLM (n : ℕ) (x : M) :
    Tensor0SBundle.TensorRSSpace 1 (n + 1) I x →L[ℝ] Tensor0SBundle.Tensor0SSpace n I x :=
  (Tensor0SBundle.tensor0SSpaceContinuousLinearEquiv (I := I) n x).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.apply ℝ (Tensor0SBundle.Tensor0SModel n ℝ E)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))).comp
      ((Tensor0SBundle.tensorRSSpaceContinuousLinearEquiv (I := I) 0 n
        x).toContinuousLinearMap.comp
        (show Tensor0SBundle.TensorRSSpace 1 (n + 1) I x →L[ℝ]
            Tensor0SBundle.TensorRSSpace 0 n I x from
          Tensor0SBundle.contractTrace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 n x)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contractUnitCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contractUnitCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contractUnitCLM ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contractUnitCLM

noncomputable def connContrCLM (m k : ℕ) (x : M)
    (B : Tensor0SBundle.TensorRSSpace 1 (k + 1) I x) :
    Tensor0SBundle.Tensor0SSpace (m + 1) I x →L[ℝ]
      Tensor0SBundle.Tensor0SSpace (m + 1 + k) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SBundle.Tensor0SSpace (m + 1) I x) := inferInstance
  (contractUnitCLM (I := I) (m + 1 + k) x).comp
    (LinearMap.toContinuousLinearMap
      { toFun := fun D =>
          (tensorProdWithCLM (I := I) (m + 1) (k + 1) x D).comp
            (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace (k + 1) I x from B)
        map_add' := fun D₁ D₂ => by
          simp only [← tensorProdPairCLM_apply]
          rw [ContinuousLinearMap.map_add, ContinuousLinearMap.add_comp]
        map_smul' := fun c D => by
          simp only [← tensorProdPairCLM_apply, RingHom.id_apply]
          rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_comp] })

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connContrCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connContrCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connContrCLM ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.connContrCLM

noncomputable def linearizedRicciConnectionDifferenceOrder1CLM (x : M)
    (A : Tensor0SBundle.TensorRSSpace 1 2 I x) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x :=
  -((slotPermCLM (I := I) perm40312 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp (slotPermCLM (I := I) perm3102 x))
      + (slotPermCLM (I := I) perm40213 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp (slotPermCLM (I := I) perm3120 x))
      + (slotPermCLM (I := I) perm42301 x).comp (connContrCLM (I := I) 2 1 x A)
      + (slotPermCLM (I := I) perm41302 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp (slotPermCLM (I := I) perm3102 x))
      + (slotPermCLM (I := I) perm41203 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp (slotPermCLM (I := I) perm3120 x)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnectionDifferenceOrder1CLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnectionDifferenceOrder1CLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnectionDifferenceOrder1CLM ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnectionDifferenceOrder1CLM

noncomputable def linearizedRicciConnectionDifferenceOrder0CLM (x : M)
    (A : Tensor0SBundle.TensorRSSpace 1 2 I x)
    (DA : Tensor0SBundle.TensorRSSpace 1 3 I x) :
    Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x :=
  ((slotPermCLM (I := I) perm43201 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp
          ((slotPermCLM (I := I) perm3102 x).comp (connContrCLM (I := I) 1 1 x A)))
      + (slotPermCLM (I := I) perm42301 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp
          ((slotPermCLM (I := I) perm3102 x).comp
            ((connContrCLM (I := I) 1 1 x A).comp (slotPermCLM (I := I) perm210 x))))
      + (slotPermCLM (I := I) perm43102 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp
          ((slotPermCLM (I := I) perm3120 x).comp (connContrCLM (I := I) 1 1 x A)))
      + (slotPermCLM (I := I) perm41302 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp
          ((connContrCLM (I := I) 1 1 x A).comp (slotPermCLM (I := I) perm210 x)))
      + (slotPermCLM (I := I) perm41203 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp (connContrCLM (I := I) 1 1 x A))
      + (slotPermCLM (I := I) perm42103 x).comp
        ((connContrCLM (I := I) 2 1 x A).comp
          ((slotPermCLM (I := I) perm3120 x).comp
            ((connContrCLM (I := I) 1 1 x A).comp (slotPermCLM (I := I) perm210 x)))))
    - (slotPermCLM (I := I) perm43012 x).comp (connContrCLM (I := I) 1 2 x DA)
    - (slotPermCLM (I := I) perm42013 x).comp
      ((connContrCLM (I := I) 1 2 x DA).comp (slotPermCLM (I := I) perm210 x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnectionDifferenceOrder0CLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnectionDifferenceOrder0CLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnectionDifferenceOrder0CLM ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnectionDifferenceOrder0CLM

noncomputable def ricciCometricFourTraceCLM (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  ((1 : ℝ) / 2) •
    ((cometricDoubleTraceFib (I := I) g₁ 2 x).comp (slotPermCLM (I := I) perm40231 x)
      + (cometricDoubleTraceFib (I := I) g₁ 2 x).comp (slotPermCLM (I := I) perm40321 x)
      - cometricDoubleTraceFib (I := I) g₁ 2 x
      - (cometricDoubleTraceFib (I := I) g₁ 2 x).comp (slotPermCLM (I := I) perm42301 x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
