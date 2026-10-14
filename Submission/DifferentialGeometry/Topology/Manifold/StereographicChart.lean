import Mathlib.Geometry.Manifold.Instances.Sphere
import Submission.DifferentialGeometry.Topology.Manifold.OpenEmbedding

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Manifold _root_.TopologicalSpace
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.Manifold
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E3 target :: scope.openDecls } }
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E4 target :: scope.openDecls } }
private abbrev S3 := Metric.sphere (0 : E4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE4HAddOfNat : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE4HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE4HAddOfNat target :: scope.openDecls } }

theorem stereographicInverse_isLocalDiffeomorph
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] (v : Metric.sphere (0 : E) 1) :
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (stereographic' n v).symm := by
  let V := EuclideanSpace ℝ (Fin n)
  have he : chartAt V (-v) = stereographic' n v := by
    change stereographic' n (-(-v)) = stereographic' n v
    rw [neg_neg]
  let D : PartialDiffeomorph (𝓡 n) (𝓡 n) (Metric.sphere (0 : E) 1) V ∞ :=
    { toPartialEquiv := (chartAt V (-v)).toPartialEquiv
      open_source := (chartAt V (-v)).open_source
      open_target := (chartAt V (-v)).open_target
      contMDiffOn_toFun := contMDiffOn_chart
      contMDiffOn_invFun := contMDiffOn_chart_symm }
  intro x
  have h := PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ D.symm
    (show x ∈ D.target from by change x ∈ (chartAt V (-v)).target; rw [he]; simp)
  change IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ (chartAt V (-v)).symm x at h
  simpa only [he] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.stereographicInverse_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.stereographicInverse_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.stereographicInverse_isLocalDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.stereographicInverse_isLocalDiffeomorph

theorem stereographic_isLocalDiffeomorphOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] (p : Metric.sphere (0 : E) 1) :
    IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (stereographic' n p)
      (stereographic' n p).source := by
  let V := EuclideanSpace ℝ (Fin n)
  have he : chartAt V (-p) = stereographic' n p := by
    change stereographic' n (-(-p)) = stereographic' n p
    rw [neg_neg]
  let D : PartialDiffeomorph (𝓡 n) (𝓡 n) (Metric.sphere (0 : E) 1) V ∞ :=
    { toPartialEquiv := (chartAt V (-p)).toPartialEquiv
      open_source := (chartAt V (-p)).open_source
      open_target := (chartAt V (-p)).open_target
      contMDiffOn_toFun := contMDiffOn_chart
      contMDiffOn_invFun := contMDiffOn_chart_symm }
  intro x
  have h := PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ D
    (show x.val ∈ D.source by change x.val ∈ (chartAt V (-p)).source; rw [he]; exact x.property)
  change IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ (chartAt V (-p)) x at h
  simpa only [he] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.stereographic_isLocalDiffeomorphOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.stereographic_isLocalDiffeomorphOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.stereographic_isLocalDiffeomorphOn ``Submission.DifferentialGeometry.Topology.Manifold.stereographic_isLocalDiffeomorphOn

def stereographicImage (north : S3) : _root_.TopologicalSpace.Opens S3 :=
  (stereographicInverse_isLocalDiffeomorph (n := 3) north).image

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.stereographicImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.stereographicImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.stereographicImage ``Submission.DifferentialGeometry.Topology.Manifold.stereographicImage

theorem stereographicImage_eq (north : S3) : (stereographicImage north : Set S3) = {north}ᶜ := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    simpa only [stereographic'_source] using
      (stereographic' 3 north).map_target (show x ∈ (stereographic' 3 north).target by simp)
  · intro hp
    exact ⟨stereographic' 3 north p, (stereographic' 3 north).left_inv
      (by simpa only [stereographic'_source] using hp)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.stereographicImage_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.stereographicImage_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.stereographicImage_eq ``Submission.DifferentialGeometry.Topology.Manifold.stereographicImage_eq

def stereographicDiffeomorph (north : S3) : E3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ stereographicImage north :=
  diffeomorphOntoImage (stereographic' 3 north).symm
    (stereographicInverse_isLocalDiffeomorph (n := 3) north)
    ((stereographic' 3 north).symm.isOpenEmbedding (by simp)).injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.stereographicDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.stereographicDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.stereographicDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.stereographicDiffeomorph

theorem stereographicDiffeomorph_apply (north : S3) (x : E3) :
    (stereographicDiffeomorph north x : S3) = (stereographic' 3 north).symm x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.stereographicDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.stereographicDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.stereographicDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.Manifold.stereographicDiffeomorph_apply

theorem stereographicDiffeomorph_coordinates (north : S3) (x : E3) :
    stereographic' 3 north (stereographicDiffeomorph north x : S3) = x :=
  (stereographic' 3 north).right_inv (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.stereographicDiffeomorph_coordinates then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.stereographicDiffeomorph_coordinates"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.stereographicDiffeomorph_coordinates ``Submission.DifferentialGeometry.Topology.Manifold.stereographicDiffeomorph_coordinates

theorem stereographicDiffeomorph_symm_apply (north : S3) (p : stereographicImage north) :
    (stereographicDiffeomorph north).symm p = stereographic' 3 north p.val := by
  have h := stereographicDiffeomorph_coordinates north ((stereographicDiffeomorph north).symm p)
  rw [Diffeomorph.apply_symm_apply] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.stereographicDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.stereographicDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.stereographicDiffeomorph_symm_apply ``Submission.DifferentialGeometry.Topology.Manifold.stereographicDiffeomorph_symm_apply
end DifferentialGeometry.Topology.Manifold
