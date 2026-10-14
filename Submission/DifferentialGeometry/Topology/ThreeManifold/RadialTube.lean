import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCap
import Submission.DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import Submission.DifferentialGeometry.Topology.Manifold.InverseFunction.ContDiffOn
import Mathlib.Geometry.Manifold.Instances.Icc

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Manifold _root_.Submission.Manifold _root_.Filter _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.SphericalTubeSystem

universe u
local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Sphere" => Metric.sphere (0 : E3) 1
local notation "Interval" => _root_.Set.Icc (-2 : ℝ) 2
local notation "CI" => ModelWithCorners.prod (𝓡 2) (𝓡∂ 1)
local notation "PI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
private local instance tubeBounds : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.tubeBounds
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalTubeSystem.tubeBounds target :: scope.openDecls } }
private local instance sphereDimension : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.sphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalTubeSystem.sphereDimension target :: scope.openDecls } }

private def tubeProjection : ℝ → Interval := _root_.Set.projIcc (-2) 2 (by norm_num)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.tubeProjection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalTubeSystem.tubeProjection target :: scope.openDecls } }

private theorem tubeProjection_val_eventually {t : ℝ} (ht : t ∈ _root_.Set.Ioo (-2 : ℝ) 2) :
    (Subtype.val : Interval → ℝ) ∘ tubeProjection =ᶠ[𝓝 t] id := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  change (_root_.Set.projIcc (-2 : ℝ) 2 (by norm_num) s).val = s
  rw [_root_.Set.projIcc_of_mem _ ⟨hs.1.le, hs.2.le⟩]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.tubeProjection_val_eventually
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalTubeSystem.tubeProjection_val_eventually target :: scope.openDecls } }

private theorem tubeProjection_contMDiffAt {t : ℝ} (ht : t ∈ _root_.Set.Ioo (-2 : ℝ) 2) :
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ tubeProjection t := by
  apply (ContMDiffAt.iff_comp_isImmersionAt
    ((isSmoothEmbedding_subtypeVal_Icc (x := (-2 : ℝ)) (y := 2) (n := ∞)).isImmersion.isImmersionAt
      (tubeProjection t))).mpr
  exact ⟨continuous_projIcc.continuousAt,
    (tubeProjection_val_eventually ht).contMDiffAt_iff.mpr contMDiffAt_id⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.tubeProjection_contMDiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalTubeSystem.tubeProjection_contMDiffAt target :: scope.openDecls } }

private theorem tubeProjection_injective_mfderiv {t : ℝ} (ht : t ∈ _root_.Set.Ioo (-2 : ℝ) 2) :
    Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) tubeProjection t) := by
  have hchain := mfderiv_comp t
    ((contMDiff_subtypeVal_Icc (x := (-2 : ℝ)) (y := 2) (n := ∞)).mdifferentiableAt (by simp))
    ((tubeProjection_contMDiffAt ht).mdifferentiableAt (by simp))
  rw [(tubeProjection_val_eventually ht).mfderiv_eq, mfderiv_id] at hchain
  have hinj : _root_.Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id t) := by
    rw [mfderiv_id]
    exact _root_.Function.injective_id
  rw [mfderiv_id, hchain] at hinj
  change _root_.Function.Injective ((mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Interval → ℝ) (tubeProjection t)) ∘
    mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) tubeProjection t) at hinj
  exact hinj.of_comp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.tubeProjection_injective_mfderiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalTubeSystem.tubeProjection_injective_mfderiv target :: scope.openDecls } }

variable {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)

private def clampedTube (a : T.Index) (p : Sphere × ℝ) : M.Carrier :=
  T.tube a (p.1, tubeProjection p.2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.clampedTube
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalTubeSystem.clampedTube target :: scope.openDecls } }

private theorem clampedTube_contMDiffAt (a : T.Index) {p : Sphere × ℝ}
    (hp : p.2 ∈ _root_.Set.Ioo (-2 : ℝ) 2) :
    ContMDiffAt PI (𝓡 3) ∞ (T.clampedTube a) p :=
  (T.smooth a).contMDiff.contMDiffAt.comp p
    (contMDiffAt_id.prodMap (tubeProjection_contMDiffAt hp))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.clampedTube_contMDiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalTubeSystem.clampedTube_contMDiffAt target :: scope.openDecls } }

private theorem clampedTube_injective_mfderiv (a : T.Index) {p : Sphere × ℝ}
    (hp : p.2 ∈ _root_.Set.Ioo (-2 : ℝ) 2) :
    Injective (mfderiv PI (𝓡 3) (T.clampedTube a) p) := by
  have hj : ContMDiffAt PI CI ∞ (Prod.map (id : Sphere → Sphere) tubeProjection) p :=
    contMDiffAt_id.prodMap (tubeProjection_contMDiffAt hp)
  change _root_.Function.Injective (mfderiv PI (𝓡 3) ((T.tube a) ∘ Prod.map id tubeProjection) p)
  rw [mfderiv_comp p ((T.smooth a).contMDiff.mdifferentiableAt (by simp))
    (hj.mdifferentiableAt (by simp)),
    mfderiv_prodMap mdifferentiableAt_id ((tubeProjection_contMDiffAt hp).mdifferentiableAt (by simp)),
    mfderiv_id]
  exact ((T.smooth a).isImmersion.isImmersionAt _ |>.injective_mfderiv (by simp)).comp
    (injective_id.prodMap (tubeProjection_injective_mfderiv hp))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.clampedTube_injective_mfderiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalTubeSystem.clampedTube_injective_mfderiv target :: scope.openDecls } }

private theorem isLocalDiffeomorphAt_clampedTube (a : T.Index) {p : Sphere × ℝ}
    (hp : p.2 ∈ _root_.Set.Ioo (-2 : ℝ) 2) :
    IsLocalDiffeomorphAt PI (𝓡 3) ∞ (T.clampedTube a) p := by
  let U : Set (Sphere × ℝ) := {q | q.2 ∈ _root_.Set.Ioo (-2 : ℝ) 2}
  have hU : IsOpen U := isOpen_Ioo.preimage continuous_snd
  have hs : ContMDiffOn PI (𝓡 3) ∞ (T.clampedTube a) U :=
    fun q hq => (clampedTube_contMDiffAt T a hq).contMDiffWithinAt
  let D : (E2 × ℝ) →L[ℝ] E3 := mfderiv PI (𝓡 3) (T.clampedTube a) p
  have hD : _root_.Function.Injective D := clampedTube_injective_mfderiv T a hp
  let A : (E2 × ℝ) ≃L[ℝ] E3 :=
    (D.toLinearMap.linearEquivOfInjective hD (by simp)).toContinuousLinearEquiv
  exact Manifold.isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
    (T.clampedTube a) hs hU p hp A
    ((clampedTube_contMDiffAt T a hp).mdifferentiableAt (by simp)).hasMFDerivAt

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.isLocalDiffeomorphAt_clampedTube
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalTubeSystem.isLocalDiffeomorphAt_clampedTube target :: scope.openDecls } }

private def axialSign (side : Bool) : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ where
  toFun t := if side then t else -t
  invFun t := if side then t else -t
  left_inv t := by cases side <;> simp
  right_inv t := by cases side <;> simp
  contMDiff_toFun := by
    change ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => if side then t else -t)
    cases side <;> simp only [Bool.false_eq_true, if_false, if_true]
    · exact contMDiff_id.neg
    · exact contMDiff_id
  contMDiff_invFun := by
    change ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => if side then t else -t)
    cases side <;> simp only [Bool.false_eq_true, if_false, if_true]
    · exact contMDiff_id.neg
    · exact contMDiff_id

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.axialSign
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalTubeSystem.axialSign target :: scope.openDecls } }

def radialTube (a : T.Index) (A : Sphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere)
    (side : Bool) (v : Sphere) (x : E3) : M.Carrier :=
  T.tube a (A (Manifold.sphereDirection v x),
    _root_.Set.projIcc (-2) 2 (by norm_num) (if side then ‖x‖ else -‖x‖))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.radialTube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.radialTube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.radialTube ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.radialTube

theorem radialTube_apply (a : T.Index) (A : Sphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere)
    (side : Bool) (v : Sphere) {x : E3} (hx : ‖x‖ < 2) :
    T.radialTube a A side v x = T.tube a
      (A (Manifold.sphereDirection v x),
        ⟨if side then ‖x‖ else -‖x‖, by
          cases side <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
            constructor <;> linarith [norm_nonneg x]⟩) := by
  unfold radialTube
  rw [_root_.Set.projIcc_of_mem]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.radialTube_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.radialTube_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.radialTube_apply ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.radialTube_apply

theorem isLocalDiffeomorphAt_radialTube (a : T.Index)
    (A : Sphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere) (side : Bool) (v : Sphere)
    {x : E3} (hx0 : 0 < ‖x‖) (hx2 : ‖x‖ < 2) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (T.radialTube a A side v) x := by
  let P := Manifold.spherePolarChart (n := 2) v
  let R : Diffeomorph PI PI (Sphere × ℝ) (Sphere × ℝ) ∞ := A.prodCongr (axialSign side)
  have hP : IsLocalDiffeomorphAt (𝓡 3) PI ∞ P.symm x :=
    P.symm.isLocalDiffeomorphAt _ _ ∞ (norm_pos_iff.mp hx0)
  have hrange : (R (P.symm x)).2 ∈ _root_.Set.Ioo (-2 : ℝ) 2 := by
    change (if side then ‖x‖ else -‖x‖) ∈ _root_.Set.Ioo (-2 : ℝ) 2
    cases side <;> simp only [Bool.false_eq_true, if_false, if_true, _root_.Set.mem_Ioo] <;>
      constructor <;> linarith
  have hR := hP.comp PI (Sphere × ℝ) (R.isLocalDiffeomorph (P.symm x))
  exact hR.comp (𝓡 3) M.Carrier (isLocalDiffeomorphAt_clampedTube T a hrange)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalTubeSystem.isLocalDiffeomorphAt_radialTube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalTubeSystem.isLocalDiffeomorphAt_radialTube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalTubeSystem.isLocalDiffeomorphAt_radialTube ``Submission.DifferentialGeometry.Topology.SphericalTubeSystem.isLocalDiffeomorphAt_radialTube

end DifferentialGeometry.Topology.SphericalTubeSystem
