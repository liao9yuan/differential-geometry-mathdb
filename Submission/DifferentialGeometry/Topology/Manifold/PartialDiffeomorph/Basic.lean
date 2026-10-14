import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff

namespace DifferentialGeometry.PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
variable {m n : WithTop ℕ∞}

def ofLE (Φ : PartialDiffeomorph I J M N n) (h : m ≤ n) :
    PartialDiffeomorph I J M N m where
  toPartialEquiv := Φ.toPartialEquiv
  open_source := Φ.open_source
  open_target := Φ.open_target
  contMDiffOn_toFun := Φ.contMDiffOn_toFun.of_le h
  contMDiffOn_invFun := Φ.contMDiffOn_invFun.of_le h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PartialDiffeomorph.ofLE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PartialDiffeomorph.ofLE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PartialDiffeomorph.ofLE ``Submission.DifferentialGeometry.PartialDiffeomorph.ofLE

@[simp]
theorem ofLE_toPartialEquiv (Φ : PartialDiffeomorph I J M N n) (h : m ≤ n) :
    (ofLE Φ h).toPartialEquiv = Φ.toPartialEquiv := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PartialDiffeomorph.ofLE_toPartialEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PartialDiffeomorph.ofLE_toPartialEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PartialDiffeomorph.ofLE_toPartialEquiv ``Submission.DifferentialGeometry.PartialDiffeomorph.ofLE_toPartialEquiv

end DifferentialGeometry.PartialDiffeomorph
