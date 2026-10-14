import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Topology.ContinuousMap.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.Morse

open _root_.Manifold

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def sublevel (f : M → ℝ) (a : ℝ) : Set M :=
  f ⁻¹' Set.Iic a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.sublevel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.sublevel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.sublevel ``Submission.DifferentialGeometry.Topology.Morse.sublevel

def superlevel (f : M → ℝ) (a : ℝ) : Set M :=
  f ⁻¹' Set.Ici a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.superlevel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.superlevel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.superlevel ``Submission.DifferentialGeometry.Topology.Morse.superlevel

def sublevelStrip (f : M → ℝ) (a b : ℝ) : Set M :=
  f ⁻¹' Set.Icc a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.sublevelStrip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.sublevelStrip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.sublevelStrip ``Submission.DifferentialGeometry.Topology.Morse.sublevelStrip

abbrev SublevelSpace (f : M → ℝ) (a : ℝ) : Type _ :=
  {x : M // x ∈ sublevel f a}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.SublevelSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.SublevelSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.SublevelSpace ``Submission.DifferentialGeometry.Topology.Morse.SublevelSpace

noncomputable def sublevelInclusion {M : Type*} [TopologicalSpace M] (f : M → ℝ) {a b : ℝ}
    (hab : a ≤ b) : C(SublevelSpace f a, SublevelSpace f b) :=
  ContinuousMap.mk (fun x => ⟨x.1, by
    change f x.1 ≤ b
    exact le_trans (by change f x.1 ≤ a; exact x.2) hab⟩) (by
    exact Continuous.subtype_mk continuous_subtype_val (by
      intro x
      change f x.1 ≤ b
      exact le_trans (by change f x.1 ≤ a; exact x.2) hab))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.sublevelInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.sublevelInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.sublevelInclusion ``Submission.DifferentialGeometry.Topology.Morse.sublevelInclusion

def IsCriticalPointAt (I : ModelWithCorners ℝ E H) (f : M → ℝ) (x : M) : Prop :=
  mfderiv I 𝓘(ℝ, ℝ) f x = 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.IsCriticalPointAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.IsCriticalPointAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.IsCriticalPointAt ``Submission.DifferentialGeometry.Topology.Morse.IsCriticalPointAt

def criticalPoints (I : ModelWithCorners ℝ E H) (f : M → ℝ) : Set M :=
  {x | IsCriticalPointAt I f x}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.criticalPoints then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.criticalPoints"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.criticalPoints ``Submission.DifferentialGeometry.Topology.Morse.criticalPoints

def chartHessianBilinAt (g : E → ℝ) (y : E) : LinearMap.BilinForm ℝ E :=
  { toFun := fun x => (fderiv ℝ (fderiv ℝ g) y x).toLinearMap
    map_add' := by
      intro x y
      ext z
      simp
    map_smul' := by
      intro a x
      ext z
      simp }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.chartHessianBilinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.chartHessianBilinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.chartHessianBilinAt ``Submission.DifferentialGeometry.Topology.Morse.chartHessianBilinAt

def chartHessianAt (g : E → ℝ) (y : E) : QuadraticForm ℝ E :=
  (chartHessianBilinAt g y).toQuadraticMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.chartHessianAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.chartHessianAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.chartHessianAt ``Submission.DifferentialGeometry.Topology.Morse.chartHessianAt

def chartHessian (g : E → ℝ) : QuadraticForm ℝ E :=
  chartHessianAt g 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.chartHessian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.chartHessian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.chartHessian ``Submission.DifferentialGeometry.Topology.Morse.chartHessian

def IsNondegenerateCriticalPointAt (I : ModelWithCorners ℝ E H) (f : M → ℝ) (x : M) : Prop :=
  IsCriticalPointAt I f x ∧
    (QuadraticMap.associated (R := ℝ)
      (chartHessianAt (g := fun y => f ((extChartAt I x).symm y))
        (extChartAt I x x))).SeparatingLeft

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt ``Submission.DifferentialGeometry.Topology.Morse.IsNondegenerateCriticalPointAt

end
end DifferentialGeometry.Topology.Morse
