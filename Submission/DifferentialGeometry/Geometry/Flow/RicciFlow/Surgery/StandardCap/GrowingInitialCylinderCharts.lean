import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.EndChart
import Submission.DifferentialGeometry.Geometry.Neck.CylinderExhaustion
import Submission.DifferentialGeometry.Geometry.Metric.RoundCylinder
import Submission.DifferentialGeometry.Geometry.Metric.PolarCoordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter _root_.Function _root_.TopologicalSpace _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Neck
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal

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
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.IC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

def initialPolarDiffeomorph (e : E3 ≃ₗᵢ[ℝ] E3) (a : ℝ) :
    PartialDiffeomorph IC (𝓡 3) (S2 × ℝ) E3 ∞ :=
  (roundCylinderDiffeomorph (n := 2) e a).toPartialDiffeomorph.trans
    (euclideanPolarDiffeomorph (n := 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph

@[simp] theorem initialPolarDiffeomorph_apply (e : E3 ≃ₗᵢ[ℝ] E3) (a : ℝ)
    (q : S2 × ℝ) :
    initialPolarDiffeomorph e a q = (a + q.2) • e (q.1 : E3) := by
  change euclideanPolarMap (roundCylinderDiffeomorph (n := 2) e a q) = _
  rw [roundCylinderDiffeomorph_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_apply

@[simp] theorem initialPolarDiffeomorph_source (e : E3 ≃ₗᵢ[ℝ] E3) (a : ℝ) :
    (initialPolarDiffeomorph e a).source = {q : S2 × ℝ | 0 < a + q.2} := by
  ext q
  change (q ∈ (_root_.Set.univ : Set (S2 × ℝ)) ∧
    0 < (roundCylinderDiffeomorph (n := 2) e a q).2) ↔ 0 < a + q.2
  rw [roundCylinderDiffeomorph_apply]
  simp only [_root_.Set.mem_univ, true_and]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_source ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_source

@[simp] theorem initialPolarDiffeomorph_target (e : E3 ≃ₗᵢ[ℝ] E3) (a : ℝ) :
    (initialPolarDiffeomorph e a).target = {0}ᶜ := by
  ext x
  change (x ≠ 0 ∧ (euclideanPolarDiffeomorph (n := 2)).symm x ∈
    (_root_.Set.univ : Set (S2 × ℝ))) ↔ x ≠ 0
  simp only [_root_.Set.mem_univ, and_true]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_target ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_target

theorem initialPolarDiffeomorph_norm (e : E3 ≃ₗᵢ[ℝ] E3) (a : ℝ)
    {q : S2 × ℝ} (hq : 0 < a + q.2) :
    ‖initialPolarDiffeomorph e a q‖ = a + q.2 := by
  rw [initialPolarDiffeomorph_apply, norm_smul, e.norm_map,
    norm_eq_of_mem_sphere, mul_one, Real.norm_eq_abs, abs_of_pos hq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_norm ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_norm

theorem initialPolarDiffeomorph_symm_height (e : E3 ≃ₗᵢ[ℝ] E3) (a : ℝ)
    {x : E3} (hx : x ≠ 0) :
    ((initialPolarDiffeomorph e a).symm x).2 = ‖x‖ - a := by
  change ((roundCylinderDiffeomorph (n := 2) e a).symm
    ((euclideanPolarDiffeomorph (n := 2)).symm x)).2 = _
  rw [roundCylinderDiffeomorph_symm_apply, euclideanPolarDiffeomorph_symm_snd hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_symm_height then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_symm_height"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_symm_height ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_symm_height

private theorem initialPolarDiffeomorph_mfderiv (e : E3 ≃ₗᵢ[ℝ] E3) (a : ℝ)
    (q : S2 × ℝ) (v : TangentSpace IC q) :
    mfderiv IC (𝓡 3) (initialPolarDiffeomorph e a) q v =
      mfderiv IC (𝓡 3) euclideanPolarMap (roundCylinderDiffeomorph (n := 2) e a q)
        (mfderiv IC IC (roundCylinderDiffeomorph (n := 2) e a) q v) := by
  change mfderiv IC (𝓡 3)
    (euclideanPolarMap ∘ roundCylinderDiffeomorph (n := 2) e a) q v = _
  rw [mfderiv_comp q
    (euclideanPolarMap_smooth.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0))
    ((roundCylinderDiffeomorph (n := 2) e a).contMDiff.mdifferentiableAt (by decide)),
    ContinuousLinearMap.comp_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_mfderiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_mfderiv target :: scope.openDecls } }

theorem initialPolarDiffeomorph_metric_inner (e : E3 ≃ₗᵢ[ℝ] E3) (a : ℝ)
    (q : S2 × ℝ) (hq : transitionEnd ≤ a + q.2) (v w : TangentSpace IC q) :
    metric.inner (initialPolarDiffeomorph e a q)
      (mfderiv IC (𝓡 3) (initialPolarDiffeomorph e a) q v)
      (mfderiv IC (𝓡 3) (initialPolarDiffeomorph e a) q w) =
      (roundCylinderMetric (E := E3) (n := 2)).inner q v w := by
  rw [initialPolarDiffeomorph_mfderiv, initialPolarDiffeomorph_mfderiv]
  change metric.inner (euclideanPolarMap (roundCylinderDiffeomorph (n := 2) e a q))
    _ _ = _
  rw [metric_polar_pullback_cylindrical _ (by
    simpa only [roundCylinderDiffeomorph_apply] using hq)]
  have h := congrArg
    (fun g : SmoothRiemannianMetric IC (S2 × ℝ) => g.inner q v w)
    (pullback_roundCylinderMetric_roundCylinderDiffeomorph (n := 2) e a)
  rw [Diffeomorph.pullbackMetric_inner] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_metric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_metric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_metric_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.initialPolarDiffeomorph_metric_inner

private theorem openCylinder_subset_polar_source (e : E3 ≃ₗᵢ[ℝ] E3)
    {a L : ℝ} (hfit : transitionEnd + L ≤ a) :
    (openCylinder L : Set (S2 × ℝ)) ⊆ (initialPolarDiffeomorph e a).source := by
  intro q hq
  rw [initialPolarDiffeomorph_source]
  change 0 < a + q.2
  have hz : -L < q.2 := hq.1
  linarith [transitionEnd_pos]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.openCylinder_subset_polar_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.openCylinder_subset_polar_source target :: scope.openDecls } }

def initialCylinderImage (e : E3 ≃ₗᵢ[ℝ] E3) (a L : ℝ)
    (hfit : transitionEnd + L ≤ a) : _root_.TopologicalSpace.Opens E3 :=
  ⟨initialPolarDiffeomorph e a '' (openCylinder L : Set (S2 × ℝ)),
    image_opens_isOpen _ (openCylinder_subset_polar_source e hfit)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderImage ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderImage

def initialCylinderChart (e : E3 ≃ₗᵢ[ℝ] E3) (a L : ℝ)
    (hfit : transitionEnd + L ≤ a) :
    openCylinder L ≃ₘ⟮IC, 𝓡 3⟯ initialCylinderImage e a L hfit :=
  PartialDiffeomorph.toOpensDiffeo (initialPolarDiffeomorph e a)
    (openCylinder_subset_polar_source e hfit)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderChart ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderChart

@[simp] theorem initialCylinderChart_apply (e : E3 ≃ₗᵢ[ℝ] E3) (a L : ℝ)
    (hfit : transitionEnd + L ≤ a) (q : openCylinder L) :
    (initialCylinderChart e a L hfit q : E3) = initialPolarDiffeomorph e a q.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderChart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderChart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderChart_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderChart_apply

theorem initialCylinderImage_eq_shell (e : E3 ≃ₗᵢ[ℝ] E3) (a L : ℝ)
    (hfit : transitionEnd + L ≤ a) :
    (initialCylinderImage e a L hfit : Set E3) =
      {x : E3 | a - L < ‖x‖ ∧ ‖x‖ < a + L} := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hpos : 0 < a + q.2 := by
      have hs := openCylinder_subset_polar_source e hfit hq
      simpa only [initialPolarDiffeomorph_source, _root_.Set.mem_ofPred_eq] using hs
    change a - L < ‖initialPolarDiffeomorph e a q‖ ∧
      ‖initialPolarDiffeomorph e a q‖ < a + L
    rw [initialPolarDiffeomorph_norm e a hpos]
    exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
  · intro hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp (by linarith [transitionEnd_pos, hx.1])
    refine ⟨(initialPolarDiffeomorph e a).symm x, ?_,
      (initialPolarDiffeomorph e a).right_inv' (by
        simpa only [initialPolarDiffeomorph_target, _root_.Set.mem_compl_singleton_iff] using hx0)⟩
    change -L < ((initialPolarDiffeomorph e a).symm x).2 ∧
      ((initialPolarDiffeomorph e a).symm x).2 < L
    rw [initialPolarDiffeomorph_symm_height e a hx0]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderImage_eq_shell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderImage_eq_shell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderImage_eq_shell ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderImage_eq_shell

theorem initialCylinderChart_pullback (e : E3 ≃ₗᵢ[ℝ] E3) (a L : ℝ)
    (hfit : transitionEnd + L ≤ a) :
    Diffeomorph.pullbackMetricCross (metric.restrictOpen (initialCylinderImage e a L hfit))
      (initialCylinderChart e a L hfit) =
        (roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder L) := by
  apply SmoothRiemannianMetric.ext_inner
  intro q v w
  rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner,
    SmoothRiemannianMetric.restrictOpen_inner, initialCylinderChart_apply]
  rw [show mfderiv IC (𝓡 3) (initialCylinderChart e a L hfit) q v =
      mfderiv IC (𝓡 3) (initialPolarDiffeomorph e a) q.val v from
    PartialDiffeomorph.mfderiv_toOpensDiffeo _
      (openCylinder_subset_polar_source e hfit) q v]
  rw [show mfderiv IC (𝓡 3) (initialCylinderChart e a L hfit) q w =
      mfderiv IC (𝓡 3) (initialPolarDiffeomorph e a) q.val w from
    PartialDiffeomorph.mfderiv_toOpensDiffeo _
      (openCylinder_subset_polar_source e hfit) q w]
  exact initialPolarDiffeomorph_metric_inner e a q.val (by linarith [q.property.1]) v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderChart_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderChart_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderChart_pullback ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderChart_pullback

theorem initialCylinderChart_distance (e : E3 ≃ₗᵢ[ℝ] E3) (a L : ℝ)
    (hfit : transitionEnd + L ≤ a) (q : openCylinder L) :
    (riemannianEDistOf metric 0 (initialCylinderChart e a L hfit q : E3)).toReal = a + q.val.2 := by
  rw [distance_zero, initialCylinderChart_apply]
  apply initialPolarDiffeomorph_norm
  linarith [transitionEnd_pos, q.property.1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderChart_distance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderChart_distance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderChart_distance ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderChart_distance

private theorem exists_pointedInitialRotation (x : E3) :
    ∃ e : E3 ≃ₗᵢ[ℝ] E3, initialPolarDiffeomorph e ‖x‖ (spherePoint, 0) = x := by
  by_cases hx : x = 0
  · refine ⟨LinearIsometryEquiv.refl ℝ E3, ?_⟩
    simp [hx]
  let p := ((euclideanPolarDiffeomorph (n := 2)).symm x).1
  obtain ⟨e, _, he⟩ := exists_sphereDiffeo_det_one (n := 2) (by norm_num) spherePoint p
  refine ⟨e, ?_⟩
  change euclideanPolarMap (roundCylinderDiffeomorph (n := 2) e ‖x‖ (spherePoint, 0)) = x
  rw [roundCylinderDiffeomorph_apply, add_zero, he]
  have hrad := euclideanPolarDiffeomorph_symm_snd (n := 2) hx
  have hq : (p, ‖x‖) = (euclideanPolarDiffeomorph (n := 2)).symm x := by
    exact Prod.ext rfl hrad.symm
  rw [hq]
  exact (euclideanPolarDiffeomorph (n := 2)).right_inv' hx

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pointedInitialRotation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pointedInitialRotation target :: scope.openDecls } }

def pointedInitialRotation (x : E3) : E3 ≃ₗᵢ[ℝ] E3 :=
  (exists_pointedInitialRotation x).choose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.pointedInitialRotation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.pointedInitialRotation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.pointedInitialRotation ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.pointedInitialRotation

theorem pointedInitialRotation_center (x : E3) :
    initialPolarDiffeomorph (pointedInitialRotation x) ‖x‖ (spherePoint, 0) = x :=
  (exists_pointedInitialRotation x).choose_spec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.pointedInitialRotation_center then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.pointedInitialRotation_center"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.pointedInitialRotation_center ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.pointedInitialRotation_center

theorem initialCylinderChart_center (x : E3) (L : ℝ) (hL : 0 < L)
    (hfit : transitionEnd + L ≤ ‖x‖) :
    (initialCylinderChart (pointedInitialRotation x) ‖x‖ L hfit
      ⟨(spherePoint, 0), by exact ⟨neg_neg_of_pos hL, hL⟩⟩ : E3) = x :=
  pointedInitialRotation_center x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderChart_center then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderChart_center"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderChart_center ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.initialCylinderChart_center

end DifferentialGeometry.PDE.RicciFlow.StandardCap

end
