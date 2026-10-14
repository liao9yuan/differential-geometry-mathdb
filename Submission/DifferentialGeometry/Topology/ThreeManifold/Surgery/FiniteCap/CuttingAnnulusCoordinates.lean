import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapChartOverlap
import Submission.DifferentialGeometry.Geometry.Metric.PolarCoordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment _root_.Submission.DifferentialGeometry.Geometry.Neck
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.S2 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.IC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

def cuttingAnnulus (L δ : ℝ) : _root_.TopologicalSpace.Opens E3 :=
  ⟨{x | L < ‖x‖ ∧ ‖x‖ < L + cuttingCollarWidth δ},
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulus ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulus

def cuttingAnnulusCollar {L δ : ℝ} (hL : 0 < L) (x : cuttingAnnulus L δ) :
    S2 × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth δ) :=
  (retainedCylinderHomeomorphShell hL).symm ⟨⟨x.val, x.property.2⟩, x.property.1.le⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar

theorem cuttingAnnulusCollar_radius {L δ : ℝ} (hL : 0 < L) (x : cuttingAnnulus L δ) :
    (cuttingAnnulusCollar hL x).2.val = ‖x.val‖ - L := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_radius ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_radius

theorem cuttingAnnulusCollar_direction {L δ : ℝ} (hL : 0 < L) (x : cuttingAnnulus L δ) :
    (cuttingAnnulusCollar hL x).1.val = ‖x.val‖⁻¹ • x.val := by
  exact homeomorphUnitSphereProd_apply_fst_coe E3 _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_direction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_direction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_direction ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_direction

theorem cuttingAnnulusCollar_radial {L δ : ℝ} (hL : 0 < L) (x : cuttingAnnulus L δ) :
    (L + (cuttingAnnulusCollar hL x).2.val) • (cuttingAnnulusCollar hL x).1.val = x.val :=
  congrArg (fun z : {y : {v : E3 // ‖v‖ < L + cuttingCollarWidth δ} // L ≤ ‖y.val‖} => z.val.val)
    ((retainedCylinderHomeomorphShell hL).apply_symm_apply ⟨⟨x.val, x.property.2⟩, x.property.1.le⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_radial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_radial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_radial ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_radial

def cuttingAnnulusCylinderMap {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (b : Bool) :
    cuttingAnnulus L δ → bufferedCylinder δ :=
  fun x => cuttingCollarCylinderMap hδ b (cuttingAnnulusCollar hL x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCylinderMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCylinderMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCylinderMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCylinderMap

theorem cuttingAnnulusCylinderMap_val {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (b : Bool) (x : cuttingAnnulus L δ) :
    (cuttingAnnulusCylinderMap hL hδ b x).val =
      ((cuttingAnnulusCollar hL x).1, cuttingSign b + cuttingSign b * (‖x.val‖ - L)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCylinderMap_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCylinderMap_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCylinderMap_val ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCylinderMap_val

theorem contMDiff_cuttingAnnulusCylinderMap {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (b : Bool) :
    ContMDiff (𝓡 3) IC ∞ (cuttingAnnulusCylinderMap hL hδ b) := by
  have hn : ContMDiff (𝓡 3) 𝓘(ℝ) ∞ (fun x : cuttingAnnulus L δ => ‖x.val‖) := by
    intro x
    apply (contMDiffAt_subtype_iff (U := cuttingAnnulus L δ)).mpr
    exact (contDiffAt_norm ℝ (norm_pos_iff.mp (hL.trans x.property.1))).contMDiffAt
  have hne (x : cuttingAnnulus L δ) : ‖x.val‖ ≠ 0 := (hL.trans x.property.1).ne'
  have hang : ContMDiff (𝓡 3) (𝓡 2) ∞ (fun x : cuttingAnnulus L δ => (cuttingAnnulusCollar hL x).1) := by
    have hv : ContMDiff (𝓡 3) (𝓡 3) ∞
        (fun x : cuttingAnnulus L δ => (cuttingAnnulusCollar hL x).1.val) := by
      simp_rw [cuttingAnnulusCollar_direction]
      exact (hn.inv₀ hne).smul (contMDiff_subtype_val (U := cuttingAnnulus L δ))
    exact ContMDiff.codRestrict_sphere hv (fun x => (cuttingAnnulusCollar hL x).1.property)
  apply (ContMDiff.subtypeVal_comp_iff (bufferedCylinder δ) (cuttingAnnulusCylinderMap hL hδ b)).mp
  exact hang.prodMk (contMDiff_const.add (contMDiff_const.mul (hn.sub contMDiff_const)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_cuttingAnnulusCylinderMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_cuttingAnnulusCylinderMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_cuttingAnnulusCylinderMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_cuttingAnnulusCylinderMap

def cuttingCylinderRadialMap (L δ : ℝ) (b : Bool) (q : bufferedCylinder δ) : E3 :=
  (L + cuttingSign b * q.val.2 - 1) • q.val.1.val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCylinderRadialMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCylinderRadialMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCylinderRadialMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCylinderRadialMap

theorem contMDiff_cuttingCylinderRadialMap (L δ : ℝ) (b : Bool) :
    ContMDiff IC (𝓡 3) ∞ (cuttingCylinderRadialMap L δ b) := by
  have hv := contMDiff_subtype_val (n := ∞) (I := IC) (U := bufferedCylinder δ)
  exact ((contMDiff_const.add (contMDiff_const.mul (contMDiff_snd.comp hv))).sub contMDiff_const).smul
    ((contMDiff_coe_sphere (n := 2)).comp (contMDiff_fst.comp hv))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_cuttingCylinderRadialMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_cuttingCylinderRadialMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_cuttingCylinderRadialMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_cuttingCylinderRadialMap

theorem cuttingCylinderRadialMap_annulus {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (b : Bool) (x : cuttingAnnulus L δ) :
    cuttingCylinderRadialMap L δ b (cuttingAnnulusCylinderMap hL hδ b x) = x.val := by
  change (L + cuttingSign b * (cuttingSign b + cuttingSign b * (‖x.val‖ - L)) - 1) •
    (cuttingAnnulusCollar hL x).1.val = x.val
  have he : L + cuttingSign b * (cuttingSign b + cuttingSign b * (‖x.val‖ - L)) - 1 =
      L + (cuttingAnnulusCollar hL x).2.val := by
    rw [cuttingAnnulusCollar_radius]
    calc
      _ = L + cuttingSign b ^ 2 + cuttingSign b ^ 2 * (‖x.val‖ - L) - 1 := by ring
      _ = _ := by rw [cuttingSign_sq]; ring
  rw [he]
  exact cuttingAnnulusCollar_radial hL x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCylinderRadialMap_annulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCylinderRadialMap_annulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCylinderRadialMap_annulus ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCylinderRadialMap_annulus

theorem cuttingAnnulusCylinderMap_injective {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (b : Bool) :
    Injective (cuttingAnnulusCylinderMap hL hδ b) := by
  intro x y h
  apply Subtype.ext
  simpa only [cuttingCylinderRadialMap_annulus] using congrArg (cuttingCylinderRadialMap L δ b) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCylinderMap_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCylinderMap_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCylinderMap_injective ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCylinderMap_injective

theorem cuttingAnnulusCylinderMap_mfderiv_injective {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (b : Bool) (x : cuttingAnnulus L δ) :
    Injective (mfderiv (𝓡 3) IC (cuttingAnnulusCylinderMap hL hδ b) x) := by
  let F := cuttingAnnulusCylinderMap hL hδ b
  let G := cuttingCylinderRadialMap L δ b
  have he : G ∘ F = (Subtype.val : cuttingAnnulus L δ → E3) :=
    funext (cuttingCylinderRadialMap_annulus hL hδ b)
  have hd := mfderiv_comp (I := 𝓡 3) (I' := IC) (I'' := 𝓡 3) x
    ((contMDiff_cuttingCylinderRadialMap L δ b).mdifferentiable (by decide) (F x))
    ((contMDiff_cuttingAnnulusCylinderMap hL hδ b).mdifferentiable (by decide) x)
  change mfderiv (𝓡 3) (𝓡 3) (G ∘ F) x =
    (mfderiv IC (𝓡 3) G (F x)).comp (mfderiv (𝓡 3) IC F x) at hd
  rw [he, DifferentialGeometry.mfderiv_subtype_val] at hd
  intro v w hvw
  have h := congrArg (mfderiv IC (𝓡 3) G (F x)) hvw
  have hv := congrArg (fun D => D v) hd
  have hw := congrArg (fun D => D w) hd
  exact hv.trans (h.trans hw.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCylinderMap_mfderiv_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCylinderMap_mfderiv_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCylinderMap_mfderiv_injective ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCylinderMap_mfderiv_injective

theorem cuttingAnnulusCylinderMap_isLocalDiffeomorph {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (b : Bool) :
    IsLocalDiffeomorph (𝓡 3) IC ∞ (cuttingAnnulusCylinderMap hL hδ b) :=
  DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    (contMDiff_cuttingAnnulusCylinderMap hL hδ b)
    (cuttingAnnulusCylinderMap_mfderiv_injective hL hδ b) (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCylinderMap_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCylinderMap_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCylinderMap_isLocalDiffeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCylinderMap_isLocalDiffeomorph
end DifferentialGeometry.Topology.ThreeManifold.Surgery
