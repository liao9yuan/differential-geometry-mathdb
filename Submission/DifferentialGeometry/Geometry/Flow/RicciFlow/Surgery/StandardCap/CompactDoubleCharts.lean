import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CompactDouble
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Atlas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E4 target :: scope.openDecls } }
private abbrev S3 := Metric.sphere (0 : E4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.S3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.S3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE4HAddOfNat : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE4HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE4HAddOfNat target :: scope.openDecls } }

private def capCoordinateDiffeomorph (R : ℝ) : E3 ≃ₘ[ℝ] E3 :=
  radialExponentialDiffeomorph.trans
    (LinearEquiv.smulOfNeZero ℝ E3 (2 * Real.exp (-R))
      (mul_ne_zero (by norm_num) (Real.exp_ne_zero _))).toContinuousLinearEquiv.toDiffeomorph

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.capCoordinateDiffeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.capCoordinateDiffeomorph target :: scope.openDecls } }

private theorem native_chart_eq (north : S3) : chartAt E3 (-north) = stereographic' 3 north := by
  change stereographic' 3 (-(-north)) = stereographic' 3 north
  rw [neg_neg]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.native_chart_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.native_chart_eq target :: scope.openDecls } }

private def nativeStereoPartial (north : S3) : PartialDiffeomorph (𝓡 3) (𝓡 3) S3 E3 ∞ where
  toPartialEquiv := (stereographic' 3 north).toPartialEquiv
  open_source := (stereographic' 3 north).open_source
  open_target := (stereographic' 3 north).open_target
  contMDiffOn_toFun := by
    change ContMDiffOn (𝓡 3) (𝓡 3) ∞ (stereographic' 3 north) (stereographic' 3 north).source
    rw [← native_chart_eq]
    exact contMDiffOn_chart
  contMDiffOn_invFun := by
    change ContMDiffOn (𝓡 3) (𝓡 3) ∞ (stereographic' 3 north).symm (stereographic' 3 north).target
    rw [← native_chart_eq]
    exact contMDiffOn_chart_symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.nativeStereoPartial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.nativeStereoPartial target :: scope.openDecls } }

private def fullCapPartial (north : S3) (R : ℝ) : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞ :=
  (capCoordinateDiffeomorph R).toPartialDiffeomorph.trans (nativeStereoPartial north).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.fullCapPartial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.fullCapPartial target :: scope.openDecls } }

private theorem fullCapPartial_source (north : S3) (R : ℝ) :
    (fullCapPartial north R).source = univ := by
  change _root_.Set.univ ∩ (capCoordinateDiffeomorph R) ⁻¹' (stereographic' 3 north).target = _root_.Set.univ
  simp only [stereographic'_target, _root_.Set.preimage_univ, _root_.Set.inter_self]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.fullCapPartial_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.fullCapPartial_source target :: scope.openDecls } }

def compactDoubleCapPartialDiffeomorph (north : S3) (R : ℝ) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞ := by
  let Φ := fullCapPartial north R
  have hsrc : Metric.ball (0 : E3) (R + 1) ⊆ Φ.source := by
    rw [fullCapPartial_source]
    exact _root_.Set.subset_univ _
  exact PartialDiffeomorph.ofOpenPartialHomeomorphRestr Φ.toOpenPartialHomeomorph
    (Metric.ball 0 (R + 1)) Metric.isOpen_ball hsrc
    (Φ.contMDiffOn_toFun.mono hsrc)
    (Φ.contMDiffOn_invFun.mono (by rintro _ ⟨x, hx, rfl⟩; exact Φ.map_source' (hsrc hx)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph

theorem compactDoubleCapPartialDiffeomorph_apply (north : S3) (R : ℝ) (x : E3) :
    compactDoubleCapPartialDiffeomorph north R x = compactDoubleCapMap north R x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph_apply

theorem compactDoubleCapPartialDiffeomorph_source (north : S3) (R : ℝ) :
    (compactDoubleCapPartialDiffeomorph north R).source = Metric.ball 0 (R + 1) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph_source ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph_source

theorem compactDoubleCapPartialDiffeomorph_target (north : S3) (R : ℝ) :
    (compactDoubleCapPartialDiffeomorph north R).target =
      compactDoubleCapMap north R '' Metric.ball 0 (R + 1) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph_target ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph_target

theorem compactDoubleCapPartialDiffeomorph_symm_apply (north : S3) (R : ℝ) (p : S3) :
    (compactDoubleCapPartialDiffeomorph north R).symm p =
      radialExponentialDiffeomorph.symm ((2 * Real.exp (-R))⁻¹ • stereographic' 3 north p) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph_symm_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph_symm_apply

theorem compactDoubleCapMap_zero (north : S3) (R : ℝ) : compactDoubleCapMap north R 0 = -north := by
  unfold compactDoubleCapMap
  rw [radialExponentialDiffeomorph_of_norm_le_one 0 (by simp), smul_zero]
  apply Subtype.ext
  change ((stereographic' 3 north).symm 0 : E4) = -(north : E4)
  norm_num [stereographic'_symm_apply, smul_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapMap_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapMap_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapMap_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapMap_zero

theorem compactDoubleCapPartialDiffeomorph_pullback (north : S3) (R : ℝ)
    (hR : _root_.Max.max transitionEnd 2 + 2 ≤ R) (x : E3)
    (hx : x ∈ (compactDoubleCapPartialDiffeomorph north R).source) (v w : E3) :
    (compactDoubleMetric north R hR).inner (compactDoubleCapPartialDiffeomorph north R x)
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapPartialDiffeomorph north R) x v)
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapPartialDiffeomorph north R) x w) = metric.inner x v w :=
  compactDoubleMetric_cap_pullback north R hR x hx v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph_pullback ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCapPartialDiffeomorph_pullback
end DifferentialGeometry.PDE.RicciFlow.StandardCap
