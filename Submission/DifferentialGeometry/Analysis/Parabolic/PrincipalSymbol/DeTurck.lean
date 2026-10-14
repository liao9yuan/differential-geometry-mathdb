import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.Symbol.Basic
import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.PrincipalSymbol.Basic
import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.Operator

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Function
open scoped _root_.Topology _root_.ContDiff _root_.Matrix _root_.Manifold

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def deTurckSymbol (g : SmoothRiemannianMetric I M) : TensorSymbol (E := E) I M :=
  fun x ξ => (-2 : ℝ) • ricciSymbol (I := I) g x ξ +
    deTurckCorrectionSymbol (I := I) g x ξ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.deTurckSymbol then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.deTurckSymbol"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.deTurckSymbol ``Submission.DifferentialGeometry.PDE.DeTurck.deTurckSymbol

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma deTurckSymbol_def (g : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    deTurckSymbol (I := I) g x ξ =
      (-2 : ℝ) • ricciSymbol (I := I) g x ξ +
        deTurckCorrectionSymbol (I := I) g x ξ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.deTurckSymbol_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.deTurckSymbol_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.deTurckSymbol_def ``Submission.DifferentialGeometry.PDE.DeTurck.deTurckSymbol_def

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma deTurckSymbol_apply (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    deTurckSymbol (I := I) g x ξ t =
      (-2 : ℝ) • ricciSymbol (I := I) g x ξ t +
        deTurckCorrectionSymbol (I := I) g x ξ t := by
  rw [deTurckSymbol_def, LinearMap.add_apply, LinearMap.smul_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.deTurckSymbol_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.deTurckSymbol_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.deTurckSymbol_apply ``Submission.DifferentialGeometry.PDE.DeTurck.deTurckSymbol_apply

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma deTurckSymbol_apply_apply (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (v w : TangentSpace I x) :
    (deTurckSymbol (I := I) g x ξ t) v w =
      -2 * (ricciSymbol (I := I) g x ξ t) v w +
        (deTurckCorrectionSymbol (I := I) g x ξ t) v w := by
  rw [deTurckSymbol_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.deTurckSymbol_apply_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.deTurckSymbol_apply_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.deTurckSymbol_apply_apply ``Submission.DifferentialGeometry.PDE.DeTurck.deTurckSymbol_apply_apply

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma raisedFormContraction_eq_snd_of_symm (g : SmoothRiemannianMetric I M) (x : M)
    (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) (k : Fin (Module.finrank ℝ E)) :
    raisedFormContraction (I := I) g x ξ t k =
      raisedFormContractionSnd (I := I) g x ξ t k :=
  (raisedFormContractionSnd_eq_of_symm (I := I) g x ξ t ht k).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.raisedFormContraction_eq_snd_of_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.raisedFormContraction_eq_snd_of_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.raisedFormContraction_eq_snd_of_symm ``Submission.DifferentialGeometry.PDE.DeTurck.raisedFormContraction_eq_snd_of_symm

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckSymbol_apply_apply_eq_isotropic_of_symm (g : SmoothRiemannianMetric I M)
    (x : M) (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) (i k : Fin (Module.finrank ℝ E)) :
    (deTurckSymbol (I := I) g x ξ t)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x i)
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x k) =
      metricCovectorNormSq (I := I) g x ξ * formComp (I := I) x t i k := by
  rw [deTurckSymbol_apply_apply]
  rw [ricciSymbol_apply_eq_closedForm (I := I) g x ξ t i k,
    deTurckCorrectionSymbol_apply_eq_closedForm (I := I) g x ξ t i k]
  rw [raisedFormContraction_eq_snd_of_symm (I := I) g x ξ t ht k]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.deTurckSymbol_apply_apply_eq_isotropic_of_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.deTurckSymbol_apply_apply_eq_isotropic_of_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.deTurckSymbol_apply_apply_eq_isotropic_of_symm ``Submission.DifferentialGeometry.PDE.DeTurck.deTurckSymbol_apply_apply_eq_isotropic_of_symm

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckSymbol_apply_eq_smul_of_symm (g : SmoothRiemannianMetric I M)
    (x : M) (ξ : E) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) :
    deTurckSymbol (I := I) g x ξ t =
      metricCovectorNormSq (I := I) g x ξ • t := by
  refine LinearMap.ext_basis (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x)
    (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x) (fun i k => ?_)
  calc (deTurckSymbol (I := I) g x ξ t)
          (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x i)
          (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x k)
      = metricCovectorNormSq (I := I) g x ξ * formComp (I := I) x t i k :=
        deTurckSymbol_apply_apply_eq_isotropic_of_symm (I := I) g x ξ t ht i k
    _ = (metricCovectorNormSq (I := I) g x ξ • t)
          (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x i)
          (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x k) := by
        rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, formComp_def]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.deTurckSymbol_apply_eq_smul_of_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.deTurckSymbol_apply_eq_smul_of_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.deTurckSymbol_apply_eq_smul_of_symm ``Submission.DifferentialGeometry.PDE.DeTurck.deTurckSymbol_apply_eq_smul_of_symm

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckSymbol_isStrictlyParabolic_of_symm (g : SmoothRiemannianMetric I M) (x : M)
    {ξ : E} (hξ : ξ ≠ 0) (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) :
    deTurckSymbol (I := I) g x ξ t =
        metricCovectorNormSq (I := I) g x ξ • t ∧
      0 < metricCovectorNormSq (I := I) g x ξ :=
  ⟨deTurckSymbol_apply_eq_smul_of_symm (I := I) g x ξ t ht,
    metricCovectorNormSq_pos (I := I) g x hξ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.deTurckSymbol_isStrictlyParabolic_of_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.deTurckSymbol_isStrictlyParabolic_of_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.deTurckSymbol_isStrictlyParabolic_of_symm ``Submission.DifferentialGeometry.PDE.DeTurck.deTurckSymbol_isStrictlyParabolic_of_symm

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem deTurckSymbol_eq_neg_laplacianSymbolCoeff_smul_of_symm
    (g : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) :
    deTurckSymbol (I := I) g x ξ t =
      (-(deTurckSymbolCoeff (I := I) g x ξ)) • t := by
  rw [deTurckSymbol_apply_eq_smul_of_symm (I := I) g x ξ t ht, deTurckSymbolCoeff_apply,
    neg_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.DeTurck.deTurckSymbol_eq_neg_laplacianSymbolCoeff_smul_of_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.DeTurck.deTurckSymbol_eq_neg_laplacianSymbolCoeff_smul_of_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.DeTurck.deTurckSymbol_eq_neg_laplacianSymbolCoeff_smul_of_symm ``Submission.DifferentialGeometry.PDE.DeTurck.deTurckSymbol_eq_neg_laplacianSymbolCoeff_smul_of_symm

end DeTurck
end PDE
end DifferentialGeometry
