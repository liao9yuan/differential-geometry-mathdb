import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Distance
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Polar
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import Submission.DifferentialGeometry.Geometry.Metric.RoundCylinder
import Submission.DifferentialGeometry.Geometry.Metric.PolarCoordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian _root_.Submission.DifferentialGeometry.Geometry.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.S2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

def cylindricalEndDomain : _root_.TopologicalSpace.Opens (S2 × ℝ) :=
  ⟨{q | transitionEnd < q.2}, isOpen_lt continuous_const continuous_snd⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEndDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEndDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEndDomain ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEndDomain

def cylindricalEndImage : _root_.TopologicalSpace.Opens E3 :=
  ⟨euclideanPolarDiffeomorph (n := 2) '' (cylindricalEndDomain : Set (S2 × ℝ)),
    image_opens_isOpen _ (fun _ hq => transitionEnd_pos.trans hq)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEndImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEndImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEndImage ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEndImage

def cylindricalEnd : cylindricalEndDomain ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), 𝓡 3⟯ cylindricalEndImage :=
  PartialDiffeomorph.toOpensDiffeo (euclideanPolarDiffeomorph (n := 2))
    (fun _ hq => transitionEnd_pos.trans hq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd

@[simp] theorem cylindricalEnd_apply (q : cylindricalEndDomain) :
    (cylindricalEnd q : E3) = euclideanPolarMap (q : S2 × ℝ) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd_apply

theorem cylindricalEndImage_eq_compl_core : (cylindricalEndImage : Set E3) = coreᶜ := by
  rw [core_eq_radial]
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    change ¬ ‖euclideanPolarMap q‖ ≤ transitionEnd
    rw [euclideanPolarMap_norm_of_pos (transitionEnd_pos.trans hq)]
    exact not_le.mpr hq
  · intro hx
    have hxL : transitionEnd < ‖x‖ := lt_of_not_ge hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp (transitionEnd_pos.trans hxL)
    refine ⟨(euclideanPolarDiffeomorph (n := 2)).symm x, ?_,
      (euclideanPolarDiffeomorph (n := 2)).right_inv' hx0⟩
    change transitionEnd < ((euclideanPolarDiffeomorph (n := 2)).symm x).2
    simpa only [euclideanPolarDiffeomorph_symm_snd hx0] using hxL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEndImage_eq_compl_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEndImage_eq_compl_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEndImage_eq_compl_core ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEndImage_eq_compl_core

theorem polar_image_closed_end :
    euclideanPolarMap '' {q : S2 × ℝ | transitionEnd ≤ q.2} =
      {x : E3 | transitionEnd ≤ ‖x‖} := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    change transitionEnd ≤ ‖euclideanPolarMap q‖
    rw [euclideanPolarMap_norm_of_pos (transitionEnd_pos.trans_le hq)]
    exact hq
  · intro hx
    change transitionEnd ≤ ‖x‖ at hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp (transitionEnd_pos.trans_le hx)
    refine ⟨(euclideanPolarDiffeomorph (n := 2)).symm x, ?_,
      (euclideanPolarDiffeomorph (n := 2)).right_inv' hx0⟩
    change transitionEnd ≤ ((euclideanPolarDiffeomorph (n := 2)).symm x).2
    simpa only [euclideanPolarDiffeomorph_symm_snd hx0] using hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.polar_image_closed_end then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.polar_image_closed_end"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.polar_image_closed_end ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.polar_image_closed_end

theorem polar_bijOn_closed_end :
    _root_.Set.BijOn euclideanPolarMap {q : S2 × ℝ | transitionEnd ≤ q.2}
      {x : E3 | transitionEnd ≤ ‖x‖} := by
  refine ⟨?_, euclideanPolarMap_injOn.mono (fun q hq => transitionEnd_pos.trans_le hq), ?_⟩
  · intro q hq
    change transitionEnd ≤ q.2 at hq
    change transitionEnd ≤ ‖euclideanPolarMap q‖
    simpa only [euclideanPolarMap_norm_of_pos (transitionEnd_pos.trans_le hq)] using hq
  · intro x hx
    rw [← polar_image_closed_end] at hx
    exact hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.polar_bijOn_closed_end then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.polar_bijOn_closed_end"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.polar_bijOn_closed_end ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.polar_bijOn_closed_end

theorem cylindricalEnd_norm (q : cylindricalEndDomain) :
    ‖(cylindricalEnd q : E3)‖ = (q : S2 × ℝ).2 :=
  euclideanPolarMap_norm_of_pos (transitionEnd_pos.trans q.property)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd_norm ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd_norm

theorem cylindricalEnd_symm_snd (x : cylindricalEndImage) :
    (cylindricalEnd.symm x : S2 × ℝ).2 = ‖(x : E3)‖ := by
  have h := cylindricalEnd_norm (cylindricalEnd.symm x)
  simpa only [cylindricalEnd.apply_symm_apply] using h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd_symm_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd_symm_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd_symm_snd ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd_symm_snd

theorem cylindricalEnd_mfderiv (q : cylindricalEndDomain)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) cylindricalEnd q v =
      mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) euclideanPolarMap (q : S2 × ℝ) v :=
  PartialDiffeomorph.mfderiv_toOpensDiffeo _
    (fun _ hq => transitionEnd_pos.trans hq) q v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd_mfderiv ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd_mfderiv

theorem cylindricalEnd_metric_inner (q : cylindricalEndDomain)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) q) :
    metric.inner (cylindricalEnd q : E3)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) cylindricalEnd q v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) cylindricalEnd q w) =
      (roundCylinderMetric (E := E3) (n := 2)).inner (q : S2 × ℝ) v w := by
  rw [cylindricalEnd_apply, cylindricalEnd_mfderiv, cylindricalEnd_mfderiv]
  exact metric_polar_pullback_cylindrical q q.property.le v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd_metric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd_metric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd_metric_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.cylindricalEnd_metric_inner

end DifferentialGeometry.PDE.RicciFlow.StandardCap
