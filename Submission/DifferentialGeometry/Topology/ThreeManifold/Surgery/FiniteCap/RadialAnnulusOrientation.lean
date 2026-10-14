import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CuttingAnnulusCoordinates
import Submission.DifferentialGeometry.Topology.Manifold.HalfClosedIntervalSmoothMaps
import Submission.DifferentialGeometry.Topology.Manifold.Attachment.RadialCollarOrientation
import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationComposition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
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
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.IR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.IR target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

theorem cuttingAnnulusCollar_contMDiff {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) :
    letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos hδ)
    ContMDiff (𝓡 3) IR ∞ (cuttingAnnulusCollar (δ := δ) hL) := by
  let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos hδ)
  have hn : ContMDiff (𝓡 3) 𝓘(ℝ) ∞ (fun x : cuttingAnnulus L δ => ‖x.val‖) := by
    intro x
    apply (contMDiffAt_subtype_iff (U := cuttingAnnulus L δ)).mpr
    exact (contDiffAt_norm ℝ (norm_pos_iff.mp (hL.trans x.property.1))).contMDiffAt
  have hang : ContMDiff (𝓡 3) (𝓡 2) ∞
      (fun x : cuttingAnnulus L δ => (cuttingAnnulusCollar hL x).1) := by
    have hv : ContMDiff (𝓡 3) (𝓡 3) ∞
        (fun x : cuttingAnnulus L δ => (cuttingAnnulusCollar hL x).1.val) := by
      simp_rw [cuttingAnnulusCollar_direction]
      exact (hn.inv₀ (fun x => (hL.trans x.property.1).ne')).smul (contMDiff_subtype_val (U := cuttingAnnulus L δ))
    exact ContMDiff.codRestrict_sphere hv (fun x => (cuttingAnnulusCollar hL x).1.property)
  have ht : ContMDiff (𝓡 3) (𝓡∂ 1) ∞
      (fun x : cuttingAnnulus L δ => (cuttingAnnulusCollar hL x).2) :=
    contMDiff_halfClosedInterval_of_val (𝓡 3) (cuttingCollarWidth_pos hδ) _
      (by simpa only [cuttingAnnulusCollar_radius] using hn.sub contMDiff_const)
  exact hang.prodMk ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_contMDiff ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_contMDiff

theorem cuttingAnnulusCollar_mfderiv_bijective {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (x : cuttingAnnulus L δ) :
    letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos hδ)
    Bijective (mfderiv (𝓡 3) IR (cuttingAnnulusCollar hL) x) := by
  let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos hδ)
  let a := cuttingAnnulusCollar (δ := δ) hL
  let ρ := radialCollarOrientationMap L (cuttingCollarWidth δ)
  have hρ := (radialCollarOrientationMap_isSmoothEmbedding hL (cuttingCollarWidth_pos hδ)).contMDiff
  have ha := cuttingAnnulusCollar_contMDiff hL hδ
  have he : ρ ∘ a = (Subtype.val : cuttingAnnulus L δ → E3) :=
    funext (cuttingAnnulusCollar_radial hL)
  have hc := mfderiv_comp (f := a) (g := ρ) x (hρ.mdifferentiableAt (by simp)) (ha.mdifferentiableAt (by simp))
  rw [he, DifferentialGeometry.mfderiv_subtype_val] at hc
  have hb : _root_.Function.Bijective ((mfderiv IR (𝓡 3) ρ (a x)) ∘ (mfderiv (𝓡 3) IR a x)) := by
    change _root_.Function.Bijective ((mfderiv IR (𝓡 3) ρ (a x)).comp (mfderiv (𝓡 3) IR a x))
    rw [← hc]
    exact Function.bijective_id
  exact hb.of_comp_left (radialCollarOrientationMap_mfderiv_bijective hL (cuttingCollarWidth_pos hδ) (a x)).injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_mfderiv_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_mfderiv_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_mfderiv_bijective ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_mfderiv_bijective

theorem cuttingAnnulusCollar_pullback_radialOrientation {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (o : Orientation ℝ E3 (Fin (Module.finrank ℝ E3))) (x : cuttingAnnulus L δ) :
    letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos hδ)
    letI := halfClosedInterval_isManifold (cuttingCollarWidth_pos hδ)
    (pullbackSmoothOrientation (𝓡 3) IR (cuttingAnnulusCollar hL)
      (cuttingAnnulusCollar_contMDiff hL hδ) (cuttingAnnulusCollar_mfderiv_bijective hL hδ)
      (radialCollarSmoothOrientation hL (cuttingCollarWidth_pos hδ) o)).val x = o := by
  let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos hδ)
  let := halfClosedInterval_isManifold (cuttingCollarWidth_pos hδ)
  let a := cuttingAnnulusCollar (δ := δ) hL
  let ρ := radialCollarOrientationMap L (cuttingCollarWidth δ)
  have hρ := (radialCollarOrientationMap_isSmoothEmbedding hL (cuttingCollarWidth_pos hδ)).contMDiff
  have ha := cuttingAnnulusCollar_contMDiff hL hδ
  have hba := cuttingAnnulusCollar_mfderiv_bijective hL hδ
  have hbρ := radialCollarOrientationMap_mfderiv_bijective hL (cuttingCollarWidth_pos hδ)
  have hb := bijective_mfderiv_comp (𝓡 3) IR (𝓡 3) a ρ ha hρ hba hbρ
  have hcomp := pullbackSmoothOrientation_comp_apply (𝓡 3) IR (𝓡 3)
    a ρ ha hρ hba hbρ hb (euclideanSmoothOrientation E3 o) x
  have he : ρ ∘ a = (Subtype.val : cuttingAnnulus L δ → E3) :=
    funext (cuttingAnnulusCollar_radial hL)
  have hd : differentialEquivOfBijective (𝓡 3) (𝓡 3) (ρ ∘ a) hb x =
      ContinuousLinearEquiv.refl ℝ E3 := by
    apply ContinuousLinearEquiv.ext
    funext v
    change mfderiv (𝓡 3) (𝓡 3) (ρ ∘ a) x v = v
    rw [he, DifferentialGeometry.mfderiv_subtype_val]
    rfl
  refine hcomp.symm.trans ?_
  change tangentOrientationEquiv
    (differentialEquivOfBijective (𝓡 3) (𝓡 3) (ρ ∘ a) hb x).symm.toLinearEquiv o = o
  rw [hd]
  exact tangentOrientationEquiv_refl o

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_pullback_radialOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_pullback_radialOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_pullback_radialOrientation ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingAnnulusCollar_pullback_radialOrientation
end DifferentialGeometry.Topology.ThreeManifold.Surgery
