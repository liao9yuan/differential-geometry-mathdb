import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.PrincipalSymbol.Formula

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section

open _root_.Set _root_.Function
open scoped _root_.Topology _root_.ContDiff _root_.Matrix _root_.Manifold

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace DeTurckLinearization

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [hSigma : SigmaCompactSpace M] [hT2 : T2Space M]
  [hBoundaryless : BoundarylessManifold I M]

section Output

omit [NeZero (Module.finrank ℝ E)] hSigma hT2 hBoundaryless in
private lemma centeredChartTangentBasis_repr_apply_add (x : M)
    (v₁ v₂ : TangentSpace I x)
    (i : Fin (Module.finrank ℝ E)) :
    (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr (v₁ + v₂) i =
      (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v₁ i +
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v₂ i := by
  exact congrArg
    (fun p : Fin (Module.finrank ℝ E) →₀ ℝ => p i)
    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr.map_add v₁ v₂)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.centeredChartTangentBasis_repr_apply_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.centeredChartTangentBasis_repr_apply_add target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] hSigma hT2 hBoundaryless in
private lemma centeredChartTangentBasis_repr_apply_smul (x : M)
    (a : ℝ) (v : TangentSpace I x)
    (i : Fin (Module.finrank ℝ E)) :
    (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr (a • v) i =
      a * (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v i := by
  have h := congrArg
    (fun p : Fin (Module.finrank ℝ E) →₀ ℝ => p i)
    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr.map_smul a v)
  simpa only [Finsupp.smul_apply, smul_eq_mul] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.centeredChartTangentBasis_repr_apply_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.centeredChartTangentBasis_repr_apply_smul target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
def deTurckCorrectionSymbolOutput (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ
    (fun v w : TangentSpace I x =>
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v i *
            (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w j *
            deTurckCorrectionSymbolComp (I := I) g x ξ t i j)
    (fun v₁ v₂ w => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [centeredChartTangentBasis_repr_apply_add]
      ring)
    (fun a v w => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [centeredChartTangentBasis_repr_apply_smul]
      ring)
    (fun v w₁ w₂ => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [centeredChartTangentBasis_repr_apply_add]
      ring)
    (fun a v w => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [centeredChartTangentBasis_repr_apply_smul]
      ring) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolOutput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolOutput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolOutput ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolOutput

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma deTurckCorrectionSymbolOutput_apply_apply (g : SmoothRiemannianMetric I M)
    (x : M) (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (v w : TangentSpace I x) :
    deTurckCorrectionSymbolOutput (I := I) g x ξ t v w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr v i *
            (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr w j *
            deTurckCorrectionSymbolComp (I := I) g x ξ t i j := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolOutput_apply_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolOutput_apply_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolOutput_apply_apply ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolOutput_apply_apply

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma deTurckCorrectionSymbolOutput_add (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t t' : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    deTurckCorrectionSymbolOutput (I := I) g x ξ (t + t') =
      deTurckCorrectionSymbolOutput (I := I) g x ξ t +
        deTurckCorrectionSymbolOutput (I := I) g x ξ t' := by
  ext v w
  rw [LinearMap.add_apply, LinearMap.add_apply, deTurckCorrectionSymbolOutput_apply_apply,
    deTurckCorrectionSymbolOutput_apply_apply, deTurckCorrectionSymbolOutput_apply_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [deTurckCorrectionSymbolComp_add]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolOutput_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolOutput_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolOutput_add ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolOutput_add

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma deTurckCorrectionSymbolOutput_smul (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (a : ℝ) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    deTurckCorrectionSymbolOutput (I := I) g x ξ (a • t) =
      a • deTurckCorrectionSymbolOutput (I := I) g x ξ t := by
  ext v w
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
    deTurckCorrectionSymbolOutput_apply_apply, deTurckCorrectionSymbolOutput_apply_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [deTurckCorrectionSymbolComp_smul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolOutput_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolOutput_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolOutput_smul ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbolOutput_smul

end Output

section Bundle

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
def deTurckCorrectionSymbol (g : SmoothRiemannianMetric I M) :
    TensorSymbol (E := E) I M :=
  fun x ξ =>
    { toFun := fun t => deTurckCorrectionSymbolOutput (I := I) g x ξ t
      map_add' := fun t t' => deTurckCorrectionSymbolOutput_add (I := I) g x ξ t t'
      map_smul' := fun a t => by
        simpa using deTurckCorrectionSymbolOutput_smul (I := I) g x ξ a t }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbol then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbol"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbol ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbol

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma deTurckCorrectionSymbol_apply (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    deTurckCorrectionSymbol (I := I) g x ξ t =
      deTurckCorrectionSymbolOutput (I := I) g x ξ t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbol_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbol_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbol_apply ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbol_apply

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckCorrectionSymbol_apply_apply (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    (deTurckCorrectionSymbol (I := I) g x ξ t)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x i)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x j) =
      deTurckCorrectionSymbolComp (I := I) g x ξ t i j := by
  classical
  rw [deTurckCorrectionSymbol_apply, deTurckCorrectionSymbolOutput_apply_apply]
  rw [(DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr_self,
    (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr_self]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
      ring
    · intro j' _ hj'
      rw [Finsupp.single_eq_of_ne hj']
      ring
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · intro i' _ hi'
    rw [Finsupp.single_eq_of_ne hi']
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbol_apply_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbol_apply_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbol_apply_apply ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbol_apply_apply

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckCorrectionSymbol_apply_eq_closedForm (g : SmoothRiemannianMetric I M)
    (x : M) (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (i j : Fin (Module.finrank ℝ E)) :
    (deTurckCorrectionSymbol (I := I) g x ξ t)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x i)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x j) =
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i *
          raisedFormContractionSnd (I := I) g x ξ t j +
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j *
          raisedFormContractionSnd (I := I) g x ξ t i -
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ i * (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr ξ j *
          formMetricTrace (I := I) g x t := by
  rw [deTurckCorrectionSymbol_apply_apply, deTurckCorrectionSymbolComp_eq_closedForm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbol_apply_eq_closedForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbol_apply_eq_closedForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbol_apply_eq_closedForm ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbol_apply_eq_closedForm

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckCorrectionSymbol_apply_symm (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (v w : TangentSpace I x) :
    (deTurckCorrectionSymbol (I := I) g x ξ t) v w =
      (deTurckCorrectionSymbol (I := I) g x ξ t) w v := by
  rw [deTurckCorrectionSymbol_apply, deTurckCorrectionSymbolOutput_apply_apply,
    deTurckCorrectionSymbolOutput_apply_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [deTurckCorrectionSymbolComp_symm (I := I) g x ξ t j i]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbol_apply_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbol_apply_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbol_apply_symm ``Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.deTurckCorrectionSymbol_apply_symm

end Bundle

end DeTurckLinearization
end DeTurck
end PDE
end DifferentialGeometry
