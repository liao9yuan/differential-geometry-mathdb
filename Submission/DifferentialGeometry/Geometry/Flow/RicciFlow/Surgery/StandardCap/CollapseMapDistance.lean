import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CollapseDomination
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.WeakLength

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal _root_.NNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.IC target :: scope.openDecls } }
private abbrev EC := EuclideanSpace ℝ (Fin 2) × ℝ

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.EC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.EC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

theorem collapseMap_riemannianCurveLength_le_of_cylinder_lower {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (g : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (hlower : ∀ q : DifferentialGeometry.Geometry.Neck.openCylinder B, ∀ v : TangentSpace IC q,
      η * (roundCylinderMetric (E := E3) (n := 2)).inner q.val v v ≤ g.inner q v v)
    (γ : ℝ → DifferentialGeometry.Geometry.Neck.openCylinder B) (a b : ℝ)
    (hγ : ContinuousOn γ (_root_.Set.Icc a b)) :
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength
        (insertedMetric hA hAB hη g) (collapseMap hA hAB ∘ γ) a b ≤
      DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength g γ a b := by
  have h := collapseMap_eVariationOn_le_of_cylinder_lower hA hAB hη g hlower γ a b hγ
  rw [DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_eq_eVariationOn
      (insertedMetric hA hAB hη g) (collapseMap hA hAB ∘ γ) a b,
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength_eq_eVariationOn
      g γ a b]
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_riemannianCurveLength_le_of_cylinder_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_riemannianCurveLength_le_of_cylinder_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_riemannianCurveLength_le_of_cylinder_lower ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_riemannianCurveLength_le_of_cylinder_lower

theorem collapseMap_riemannianEDistOf_le_of_cylinder_lower {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (g : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (hlower : ∀ q : DifferentialGeometry.Geometry.Neck.openCylinder B, ∀ v : TangentSpace IC q,
      η * (roundCylinderMetric (E := E3) (n := 2)).inner q.val v v ≤ g.inner q v v) :
    ∀ x y : DifferentialGeometry.Geometry.Neck.openCylinder B,
      riemannianEDistOf (insertedMetric hA hAB hη g) (collapseMap hA hAB x)
          (collapseMap hA hAB y) ≤
        riemannianEDistOf g x y := by
  let F : C(DifferentialGeometry.Geometry.Neck.openCylinder B, insertionBall B) :=
    ⟨collapseMap hA hAB, continuous_collapseMap hA hAB⟩
  have hF : ⇑F = collapseMap hA hAB := rfl
  have hloc : ∀ x : DifferentialGeometry.Geometry.Neck.openCylinder B,
      ∃ U ∈ 𝓝 x, ∀ (a b : ℝ)
        (γ : ℝ → DifferentialGeometry.Geometry.Neck.openCylinder B),
        a ≤ b → ContinuousOn γ (_root_.Set.Icc a b) → _root_.Set.MapsTo γ (_root_.Set.Icc a b) U →
        DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength g γ a b ≠ ⊤ →
        DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength
            (insertedMetric hA hAB hη g) (⇑F ∘ γ) a b ≤
          1 * DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.riemannianCurveLength
            g γ a b := by
    intro x
    exact ⟨univ, Filter.univ_mem, fun a b γ _ hγ _ _ => by
      rw [one_mul]
      simpa only [← hF] using
        collapseMap_riemannianCurveLength_le_of_cylinder_lower hA hAB hη g hlower γ a b hγ⟩
  have hmain := DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rfs_local_to_global_length_of_ne_zero
    g (insertedMetric hA hAB hη g) F 1 (by norm_num) hloc
  intro x y
  simpa [hF, one_mul] using hmain x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_riemannianEDistOf_le_of_cylinder_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_riemannianEDistOf_le_of_cylinder_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_riemannianEDistOf_le_of_cylinder_lower ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseMap_riemannianEDistOf_le_of_cylinder_lower

end DifferentialGeometry.PDE.RicciFlow.StandardCap
