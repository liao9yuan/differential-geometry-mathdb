import Submission.DifferentialGeometry.Topology.Manifold.Attachment.RadialCollarOrientation
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold.Attachment

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.S2 target :: scope.openDecls } }
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.IR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.IR target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

theorem mfderiv_radialCollarOrientationMap {L B : ℝ} (hB : 0 < B)
    (q : S2 × _root_.Set.Ico (0 : ℝ) B)
    (v : EuclideanSpace ℝ (Fin 2)) (t : EuclideanSpace ℝ (Fin 1)) :
    let := halfClosedIntervalChartedSpace hB
    mfderiv IR (𝓡 3) (radialCollarOrientationMap L B) q (v, t) =
      (L + q.2.val) • mvfderiv (I := (𝓡 2)) (Subtype.val : S2 → E3) q.1 v +
        (mvfderiv (I := (𝓡∂ 1)) (Subtype.val : _root_.Set.Ico (0 : ℝ) B → ℝ) q.2 t : ℝ) • q.1.val := by
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  let a : S2 × _root_.Set.Ico (0 : ℝ) B → ℝ := fun q => L + q.2.val
  let g : S2 × _root_.Set.Ico (0 : ℝ) B → E3 := fun q => q.1.val
  have hs := (isSmoothEmbedding_halfClosedInterval_inclusion hB).contMDiff
  have ha : MDifferentiableAt IR 𝓘(ℝ) a q :=
    (contMDiff_const.add (hs.comp contMDiff_snd)).mdifferentiableAt (by simp)
  have hg : MDifferentiableAt IR (𝓡 3) g q :=
    ((contMDiff_coe_sphere (m := ∞)).comp contMDiff_fst).mdifferentiableAt (by simp)
  have h := congrArg (fun D => D (v, t)) (mvfderiv_smul ha hg)
  change mfderiv IR (𝓡 3) (fun q => a q • g q) q (v, t) =
    a q • mvfderiv (I := IR) g q (v, t) + (mvfderiv (I := IR) a q (v, t)) • g q at h
  change mfderiv IR (𝓡 3) (fun q => a q • g q) q (v, t) = _
  rw [h]
  have hga : mvfderiv (I := IR) g q (v, t) =
      mvfderiv (I := (𝓡 2)) (Subtype.val : S2 → E3) q.1 v := by
    change mfderiv IR (𝓡 3) ((Subtype.val : S2 → E3) ∘ Prod.fst) q (v, t) = _
    erw [mfderiv_comp_apply q ((contMDiff_coe_sphere (m := ∞)).mdifferentiableAt (by simp))
      mdifferentiableAt_fst, mfderiv_fst]
    rfl
  have haa : mvfderiv (I := IR) a q (v, t) =
      mvfderiv (I := (𝓡∂ 1)) (Subtype.val : _root_.Set.Ico (0 : ℝ) B → ℝ) q.2 t := by
    change mfderiv IR 𝓘(ℝ) (fun p : S2 × _root_.Set.Ico (0 : ℝ) B => L + p.2.val) q (v, t) = _
    change mfderiv IR 𝓘(ℝ) (fun p : S2 × _root_.Set.Ico (0 : ℝ) B => L + p.2.val) q (v, t) =
      mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : _root_.Set.Ico (0 : ℝ) B → ℝ) q.2 t
    erw [mfderiv_add mdifferentiableAt_const ((hs.comp contMDiff_snd).mdifferentiableAt (by simp)),
      mfderiv_const, zero_add]
    erw [mfderiv_comp_apply q (hs.mdifferentiableAt (by simp)) mdifferentiableAt_snd, mfderiv_snd]
    rfl
  rw [hga, haa]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.mfderiv_radialCollarOrientationMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.mfderiv_radialCollarOrientationMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.mfderiv_radialCollarOrientationMap ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.mfderiv_radialCollarOrientationMap

end DifferentialGeometry.Topology.Manifold.Attachment

end

end

section

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold.Attachment

private abbrev E2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.E2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.E2 target :: scope.openDecls } }
private abbrev E1 := EuclideanSpace ℝ (Fin 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.E1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.E1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment.instFactEqNatFinrankRealE3HAddOfNat_1 : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.instFactEqNatFinrankRealE3HAddOfNat_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.instFactEqNatFinrankRealE3HAddOfNat_1 target :: scope.openDecls } }

theorem mfderiv_sphere_linear_isometry_coe
    (A : E3 ≃ₗᵢ[ℝ] E3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    (ha : ∀ z, (a z : E3) = A z) (z : S2) (v : E2) :
    mvfderiv (I := (𝓡 2)) (Subtype.val : S2 → E3) (a z)
        (mfderiv (𝓡 2) (𝓡 2) a z v) =
      A (mvfderiv (I := (𝓡 2)) (Subtype.val : S2 → E3) z v) := by
  have heq : (Subtype.val : S2 → E3) ∘ a = A ∘ (Subtype.val : S2 → E3) := funext ha
  have hc : MDifferentiableAt (𝓡 2) (𝓡 3) (Subtype.val : S2 → E3) (a z) :=
    (contMDiff_coe_sphere (m := ∞)).mdifferentiableAt (by simp)
  have h := mfderiv_comp_apply z hc (a.contMDiff.mdifferentiableAt (by simp)) v
  rw [heq] at h
  have hc' : MDifferentiableAt (𝓡 2) (𝓡 3) (Subtype.val : S2 → E3) z :=
    (contMDiff_coe_sphere (m := ∞)).mdifferentiableAt (by simp)
  erw [mfderiv_comp_apply z ((A.contDiff (n := ∞)).contMDiff.mdifferentiableAt (by simp)) hc',
    mfderiv_eq_fderiv, A.toContinuousLinearEquiv.fderiv] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.mfderiv_sphere_linear_isometry_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.mfderiv_sphere_linear_isometry_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.mfderiv_sphere_linear_isometry_coe ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.mfderiv_sphere_linear_isometry_coe

theorem radialCollar_mfderiv_normal {L B : ℝ} (hB : 0 < B) (z : S2) (ν : E1) :
    letI := halfClosedIntervalChartedSpace hB
    let q : S2 × _root_.Set.Ico (0 : ℝ) B := (z, ⟨0, le_rfl, hB⟩)
    mvfderiv (I := (𝓡∂ 1)) (Subtype.val : _root_.Set.Ico (0 : ℝ) B → ℝ) q.2 ν = 1 →
      mfderiv IR (𝓡 3) (radialCollarOrientationMap L B) q (0, ν) = (z : E3) := by
  let := halfClosedIntervalChartedSpace hB
  intro q hν
  erw [mfderiv_radialCollarOrientationMap hB q 0 ν, map_zero, smul_zero, zero_add, hν, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCollar_mfderiv_normal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCollar_mfderiv_normal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCollar_mfderiv_normal ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCollar_mfderiv_normal

theorem radialCollar_mfderiv_tangent {L B : ℝ} (hB : 0 < B)
    (A : E3 ≃ₗᵢ[ℝ] E3) (a : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    (ha : ∀ z, (a z : E3) = A z) (z : S2) (v : E2) :
    letI := halfClosedIntervalChartedSpace hB
    let q : S2 × _root_.Set.Ico (0 : ℝ) B := (a z, ⟨0, le_rfl, hB⟩)
    mfderiv IR (𝓡 3) (radialCollarOrientationMap L B) q
      (mfderiv (𝓡 2) (𝓡 2) a z v, (0 : E1)) =
        L • A (mvfderiv (I := (𝓡 2)) (Subtype.val : S2 → E3) z v) := by
  let := halfClosedIntervalChartedSpace hB
  intro q
  erw [mfderiv_radialCollarOrientationMap hB q _ 0, map_zero, zero_smul, add_zero]
  change (L + 0) • _ = _
  rw [add_zero, mfderiv_sphere_linear_isometry_coe A a ha z v]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCollar_mfderiv_tangent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCollar_mfderiv_tangent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCollar_mfderiv_tangent ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCollar_mfderiv_tangent

end DifferentialGeometry.Topology.Manifold.Attachment

end

end
