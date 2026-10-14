import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeMaps

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Integral singular cochains on the same original chain complex

Cochains are actual integer-linear functionals on the original singular
chains. Their differential is precomposition with the original boundary.
-/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap

universe u

namespace DifferentialGeometry.Topology

/-- Integral cochains are actual linear maps on the original chain groups. -/
abbrev integralSingularCochain (n : ℕ) (X : Type u) [TopologicalSpace X] :=
  (integralSingularChains X).X n →ₗ[ℤ] integralSingularCoefficients.{u}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCochain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCochain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCochain ``Submission.DifferentialGeometry.Topology.integralSingularCochain

/-- The actual coboundary, by precomposition with the original boundary. -/
def integralSingularCoboundary (X : Type u) [TopologicalSpace X] (i j : ℕ) :
    integralSingularCochain i X →ₗ[ℤ] integralSingularCochain j X where
  toFun φ := φ.comp ((integralSingularChains X).d j i).hom
  map_add' φ ψ := by ext c; rfl
  map_smul' k φ := by ext c; rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCoboundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCoboundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCoboundary ``Submission.DifferentialGeometry.Topology.integralSingularCoboundary

/-- The integral singular cochain complex of the original space. -/
def integralSingularCochains (X : Type u) [TopologicalSpace X] :
    CochainComplex (ModuleCat.{u} ℤ) ℕ where
  X n := ModuleCat.of ℤ (integralSingularCochain n X)
  d i j := ModuleCat.ofHom (integralSingularCoboundary X i j)
  shape i j h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro c
    change φ ((integralSingularChains X).d j i c) = 0
    rw [(integralSingularChains X).shape j i h]
    exact φ.map_zero
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro c
    change φ ((integralSingularChains X).d j i ((integralSingularChains X).d k j c)) = 0
    have h := congrArg (fun f : (integralSingularChains X).X k ⟶
      (integralSingularChains X).X i => f c) ((integralSingularChains X).d_comp_d k j i)
    change (integralSingularChains X).d j i ((integralSingularChains X).d k j c) = 0 at h
    rw [h, map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCochains then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCochains"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCochains ``Submission.DifferentialGeometry.Topology.integralSingularCochains

/-- Cohomology is the actual cohomology of those original integer cochains. -/
abbrev integralSingularCohomology (n : ℕ) (X : Type u) [TopologicalSpace X] : ModuleCat.{u} ℤ :=
  (integralSingularCochains X).homology n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomology ``Submission.DifferentialGeometry.Topology.integralSingularCohomology

/-- Degree-one vanishing says every original integral 1-cocycle is the
coboundary of an original integral 0-cochain. -/
theorem integralSingularCohomology_one_vanishing_iff (X : Type u) [TopologicalSpace X] :
    Subsingleton (integralSingularCohomology 1 X) ↔
      ∀ φ : integralSingularCochain 1 X, integralSingularCoboundary X 1 2 φ = 0 →
        ∃ ψ : integralSingularCochain 0 X, integralSingularCoboundary X 0 1 ψ = φ := by
  rw [← ModuleCat.isZero_iff_subsingleton, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomology_one_vanishing_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomology_one_vanishing_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomology_one_vanishing_iff ``Submission.DifferentialGeometry.Topology.integralSingularCohomology_one_vanishing_iff

end DifferentialGeometry.Topology
