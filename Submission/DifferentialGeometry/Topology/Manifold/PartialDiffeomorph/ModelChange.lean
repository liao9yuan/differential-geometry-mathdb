import Submission.DifferentialGeometry.Topology.Manifold.ModelWithCorners
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open scoped _root_.Manifold _root_.ContDiff
namespace PartialDiffeomorph
open _root_.PartialDiffeomorph
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' F F' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n : WithTop ℕ∞}
open _root_.PartialDiffeomorph in
def transContinuousLinearEquiv (Phi : PartialDiffeomorph I J M N n)
    (e : E ≃L[𝕜] E') (f : F ≃L[𝕜] F') :
    PartialDiffeomorph (I.transContinuousLinearEquiv e) (J.transContinuousLinearEquiv f) M N n where
  toPartialEquiv := Phi.toPartialEquiv
  open_source := Phi.open_source
  open_target := Phi.open_target
  contMDiffOn_toFun := by simpa only [ContinuousLinearEquiv.contMDiffOn_transContinuousLinearEquiv_left,
    ContinuousLinearEquiv.contMDiffOn_transContinuousLinearEquiv_right] using Phi.contMDiffOn_toFun
  contMDiffOn_invFun := by simpa only [ContinuousLinearEquiv.contMDiffOn_transContinuousLinearEquiv_left,
    ContinuousLinearEquiv.contMDiffOn_transContinuousLinearEquiv_right] using Phi.contMDiffOn_invFun

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.transContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.transContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.transContinuousLinearEquiv ``Submission.PartialDiffeomorph.transContinuousLinearEquiv
open _root_.PartialDiffeomorph in
@[simp] theorem transContinuousLinearEquiv_source (Phi : PartialDiffeomorph I J M N n)
    (e : E ≃L[𝕜] E') (f : F ≃L[𝕜] F') :
    (Phi.transContinuousLinearEquiv e f).source = Phi.source := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.transContinuousLinearEquiv_source then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.transContinuousLinearEquiv_source"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.transContinuousLinearEquiv_source ``Submission.PartialDiffeomorph.transContinuousLinearEquiv_source
open _root_.PartialDiffeomorph in
@[simp] theorem transContinuousLinearEquiv_target (Phi : PartialDiffeomorph I J M N n)
    (e : E ≃L[𝕜] E') (f : F ≃L[𝕜] F') :
    (Phi.transContinuousLinearEquiv e f).target = Phi.target := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.transContinuousLinearEquiv_target then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.transContinuousLinearEquiv_target"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.transContinuousLinearEquiv_target ``Submission.PartialDiffeomorph.transContinuousLinearEquiv_target
open _root_.PartialDiffeomorph in
@[simp] theorem transContinuousLinearEquiv_apply (Phi : PartialDiffeomorph I J M N n)
    (e : E ≃L[𝕜] E') (f : F ≃L[𝕜] F') (x : M) :
    (Phi.transContinuousLinearEquiv e f) x = Phi x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.transContinuousLinearEquiv_apply then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.transContinuousLinearEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.transContinuousLinearEquiv_apply ``Submission.PartialDiffeomorph.transContinuousLinearEquiv_apply
open _root_.PartialDiffeomorph in
@[simp] theorem transContinuousLinearEquiv_symm (Phi : PartialDiffeomorph I J M N n)
    (e : E ≃L[𝕜] E') (f : F ≃L[𝕜] F') :
    (Phi.transContinuousLinearEquiv e f).symm = Phi.symm.transContinuousLinearEquiv f e := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.transContinuousLinearEquiv_symm then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.transContinuousLinearEquiv_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.transContinuousLinearEquiv_symm ``Submission.PartialDiffeomorph.transContinuousLinearEquiv_symm
variable {G G' : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup G'] [NormedSpace 𝕜 G']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 G H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]

open _root_.PartialDiffeomorph in
theorem transContinuousLinearEquiv_trans
    (Phi : PartialDiffeomorph I J M N n) (Psi : PartialDiffeomorph J K N P n)
    (e : E ≃L[𝕜] E') (f : F ≃L[𝕜] F') (g : G ≃L[𝕜] G') :
    (Phi.trans Psi).transContinuousLinearEquiv e g =
      (Phi.transContinuousLinearEquiv e f).trans (Psi.transContinuousLinearEquiv f g) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.transContinuousLinearEquiv_trans then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.transContinuousLinearEquiv_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.transContinuousLinearEquiv_trans ``Submission.PartialDiffeomorph.transContinuousLinearEquiv_trans

open _root_.PartialDiffeomorph in
def ofTransContinuousLinearEquiv (e : E ≃L[𝕜] E') (f : F ≃L[𝕜] F')
    (Phi : PartialDiffeomorph (I.transContinuousLinearEquiv e) (J.transContinuousLinearEquiv f) M N n) :
    PartialDiffeomorph I J M N n where
  toPartialEquiv := Phi.toPartialEquiv
  open_source := Phi.open_source
  open_target := Phi.open_target
  contMDiffOn_toFun := by simpa only [ContinuousLinearEquiv.contMDiffOn_transContinuousLinearEquiv_left,
    ContinuousLinearEquiv.contMDiffOn_transContinuousLinearEquiv_right] using Phi.contMDiffOn_toFun
  contMDiffOn_invFun := by simpa only [ContinuousLinearEquiv.contMDiffOn_transContinuousLinearEquiv_left,
    ContinuousLinearEquiv.contMDiffOn_transContinuousLinearEquiv_right] using Phi.contMDiffOn_invFun

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.ofTransContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.ofTransContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.ofTransContinuousLinearEquiv ``Submission.PartialDiffeomorph.ofTransContinuousLinearEquiv
open _root_.PartialDiffeomorph in
@[simp] theorem transContinuousLinearEquiv_ofTransContinuousLinearEquiv
    (e : E ≃L[𝕜] E') (f : F ≃L[𝕜] F')
    (Phi : PartialDiffeomorph (I.transContinuousLinearEquiv e) (J.transContinuousLinearEquiv f) M N n) :
    (Phi.ofTransContinuousLinearEquiv e f).transContinuousLinearEquiv e f = Phi := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.transContinuousLinearEquiv_ofTransContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.transContinuousLinearEquiv_ofTransContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.transContinuousLinearEquiv_ofTransContinuousLinearEquiv ``Submission.PartialDiffeomorph.transContinuousLinearEquiv_ofTransContinuousLinearEquiv
open _root_.PartialDiffeomorph in
@[simp] theorem ofTransContinuousLinearEquiv_transContinuousLinearEquiv
    (Phi : PartialDiffeomorph I J M N n) (e : E ≃L[𝕜] E') (f : F ≃L[𝕜] F') :
    (Phi.transContinuousLinearEquiv e f).ofTransContinuousLinearEquiv e f = Phi := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.ofTransContinuousLinearEquiv_transContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.ofTransContinuousLinearEquiv_transContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.ofTransContinuousLinearEquiv_transContinuousLinearEquiv ``Submission.PartialDiffeomorph.ofTransContinuousLinearEquiv_transContinuousLinearEquiv

end PartialDiffeomorph
