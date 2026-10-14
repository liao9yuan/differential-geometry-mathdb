import Submission.DifferentialGeometry.Analysis.Convex.Tensor04SectionalNonnegativeCone
import Submission.DifferentialGeometry.Geometry.Curvature.Algebraic.Tensor

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Analysis.Convex
open _root_.Submission.DifferentialGeometry.Analysis.InnerProductSpace
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

noncomputable def algebraicSectionalEvalCLM {x : M}
    (v w : TangentSpace I x) :
    StrongDual Real
      (algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :=
  (tensor04SectionalEvalCLM (I := I) (M := M) v w).comp
    (algebraicCurvatureTensorSubmodule (I := I) (M := M) x).subtypeL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.algebraicSectionalEvalCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.algebraicSectionalEvalCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.algebraicSectionalEvalCLM ``Submission.DifferentialGeometry.Geometry.Curvature.algebraicSectionalEvalCLM

omit [FiniteDimensional Real E] in
@[simp]
theorem algebraicSectionalEvalCLM_apply {x : M}
    (v w : TangentSpace I x)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    algebraicSectionalEvalCLM (I := I) (M := M) v w A =
      tensor04SectionalEval (I := I) (M := M)
        (A : Tensor04At (I := I) (M := M) x) v w :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.algebraicSectionalEvalCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.algebraicSectionalEvalCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.algebraicSectionalEvalCLM_apply ``Submission.DifferentialGeometry.Geometry.Curvature.algebraicSectionalEvalCLM_apply

noncomputable def algebraicSectionalNonnegativeCone {x : M} :
    ProperCone Real
      (algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :=
  (tensor04SectionalNonnegativeCone (I := I) (M := M)).comap
    (algebraicCurvatureTensorSubmodule (I := I) (M := M) x).subtypeL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.algebraicSectionalNonnegativeCone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.algebraicSectionalNonnegativeCone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.algebraicSectionalNonnegativeCone ``Submission.DifferentialGeometry.Geometry.Curvature.algebraicSectionalNonnegativeCone

omit [FiniteDimensional Real E] in
@[simp]
theorem mem_algebraicSectionalNonnegativeCone {x : M}
    {A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x} :
    A ∈ algebraicSectionalNonnegativeCone (I := I) (M := M) ↔
      ∀ v w : TangentSpace I x,
        0 ≤ tensor04SectionalEval (I := I) (M := M)
          (A : Tensor04At (I := I) (M := M) x) v w := by
  simp [algebraicSectionalNonnegativeCone]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.mem_algebraicSectionalNonnegativeCone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.mem_algebraicSectionalNonnegativeCone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.mem_algebraicSectionalNonnegativeCone ``Submission.DifferentialGeometry.Geometry.Curvature.mem_algebraicSectionalNonnegativeCone

omit [FiniteDimensional Real E] in
theorem algebraicSectionalEvalCLM_isDualElement {x : M}
    (v w : TangentSpace I x) :
    ProperCone.IsDualElement
      (C := algebraicSectionalNonnegativeCone (I := I) (M := M))
      (algebraicSectionalEvalCLM (I := I) (M := M) v w) := by
  intro A hA
  exact (mem_algebraicSectionalNonnegativeCone.mp hA) v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.algebraicSectionalEvalCLM_isDualElement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.algebraicSectionalEvalCLM_isDualElement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.algebraicSectionalEvalCLM_isDualElement ``Submission.DifferentialGeometry.Geometry.Curvature.algebraicSectionalEvalCLM_isDualElement

omit [FiniteDimensional Real E] in
theorem mem_algebraicSectionalNonnegative_dualZeroFace {x : M}
    {A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x}
    {v w : TangentSpace I x} :
    A ∈ (algebraicSectionalNonnegativeCone (I := I) (M := M)).dualZeroFace
        (algebraicSectionalEvalCLM (I := I) (M := M) v w) ↔
      A ∈ algebraicSectionalNonnegativeCone (I := I) (M := M) ∧
        tensor04SectionalEval (I := I) (M := M)
          (A : Tensor04At (I := I) (M := M) x) v w = 0 := by
  simp [ProperCone.mem_dualZeroFace]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.mem_algebraicSectionalNonnegative_dualZeroFace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.mem_algebraicSectionalNonnegative_dualZeroFace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.mem_algebraicSectionalNonnegative_dualZeroFace ``Submission.DifferentialGeometry.Geometry.Curvature.mem_algebraicSectionalNonnegative_dualZeroFace

theorem algebraicSectionalEval_pullback {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) y)
    (v w : TangentSpace I x) :
    tensor04SectionalEval (I := I) (M := M)
        ((algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e A :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
          Tensor04At (I := I) (M := M) x) v w =
      tensor04SectionalEval (I := I) (M := M)
        (A : Tensor04At (I := I) (M := M) y) (e v) (e w) := by
  change tensor04SectionalEval (I := I) (M := M)
      (tensor0SPullbackCLE (I := I) (M := M) 4 e A) v w = _
  exact tensor04SectionalEval_pullback (I := I) (M := M) e A v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.algebraicSectionalEval_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.algebraicSectionalEval_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.algebraicSectionalEval_pullback ``Submission.DifferentialGeometry.Geometry.Curvature.algebraicSectionalEval_pullback

theorem algebraicCurvatureTensorPullbackCLE_mem_sectionalNonnegativeCone_iff
    {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) y) :
    algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e A ∈
        algebraicSectionalNonnegativeCone (I := I) (M := M) ↔
      A ∈ algebraicSectionalNonnegativeCone (I := I) (M := M) := by
  constructor
  · intro hA
    apply mem_algebraicSectionalNonnegativeCone.mpr
    intro v w
    have h := mem_algebraicSectionalNonnegativeCone.mp hA
      (e.symm v) (e.symm w)
    rw [algebraicSectionalEval_pullback] at h
    simpa using h
  · intro hA
    apply mem_algebraicSectionalNonnegativeCone.mpr
    intro v w
    rw [algebraicSectionalEval_pullback]
    exact mem_algebraicSectionalNonnegativeCone.mp hA (e v) (e w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorPullbackCLE_mem_sectionalNonnegativeCone_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorPullbackCLE_mem_sectionalNonnegativeCone_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorPullbackCLE_mem_sectionalNonnegativeCone_iff ``Submission.DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorPullbackCLE_mem_sectionalNonnegativeCone_iff

theorem algebraicSectionalNonnegativeCone_map_pullback {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    (algebraicSectionalNonnegativeCone (I := I) (M := M) :
      ProperCone Real
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) y)).map
          (algebraicCurvatureTensorPullbackCLE
            (I := I) (M := M) e).toContinuousLinearMap =
      (algebraicSectionalNonnegativeCone (I := I) (M := M) :
        ProperCone Real
          (algebraicCurvatureTensorSubmodule (I := I) (M := M) x)) := by
  apply ProperCone.ext
  intro A
  rw [ProperCone.mem_map_continuousLinearEquiv_iff]
  simpa using
    algebraicCurvatureTensorPullbackCLE_mem_sectionalNonnegativeCone_iff
      (I := I) (M := M) e.symm A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.algebraicSectionalNonnegativeCone_map_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.algebraicSectionalNonnegativeCone_map_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.algebraicSectionalNonnegativeCone_map_pullback ``Submission.DifferentialGeometry.Geometry.Curvature.algebraicSectionalNonnegativeCone_map_pullback

theorem algebraicSectionalNonnegative_dualZeroFace_map_pullback {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (v w : TangentSpace I x) :
    ((algebraicSectionalNonnegativeCone (I := I) (M := M) :
      ProperCone Real
        (algebraicCurvatureTensorSubmodule (I := I) (M := M) y)).dualZeroFace
          (algebraicSectionalEvalCLM (I := I) (M := M) (e v) (e w))).map
            (algebraicCurvatureTensorPullbackCLE
              (I := I) (M := M) e).toContinuousLinearMap =
      ((algebraicSectionalNonnegativeCone (I := I) (M := M) :
        ProperCone Real
          (algebraicCurvatureTensorSubmodule (I := I) (M := M) x)).dualZeroFace
            (algebraicSectionalEvalCLM (I := I) (M := M) v w)) := by
  rw [ProperCone.dualZeroFace_map_continuousLinearEquiv]
  rw [algebraicSectionalNonnegativeCone_map_pullback]
  congr 1
  apply ContinuousLinearMap.ext
  intro A
  change tensor04SectionalEval (I := I) (M := M)
      (((algebraicCurvatureTensorPullbackCLE
        (I := I) (M := M) e).symm A :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) y) :
          Tensor04At (I := I) (M := M) y) (e v) (e w) =
    tensor04SectionalEval (I := I) (M := M)
      (A : Tensor04At (I := I) (M := M) x) v w
  change tensor04SectionalEval (I := I) (M := M)
      ((algebraicCurvatureTensorPullbackCLE
        (I := I) (M := M) e.symm A :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) y) :
          Tensor04At (I := I) (M := M) y) (e v) (e w) = _
  rw [algebraicSectionalEval_pullback]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.algebraicSectionalNonnegative_dualZeroFace_map_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.algebraicSectionalNonnegative_dualZeroFace_map_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.algebraicSectionalNonnegative_dualZeroFace_map_pullback ``Submission.DifferentialGeometry.Geometry.Curvature.algebraicSectionalNonnegative_dualZeroFace_map_pullback

end DifferentialGeometry.Geometry.Curvature
