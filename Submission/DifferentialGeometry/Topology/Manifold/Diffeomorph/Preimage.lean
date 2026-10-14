import Submission.DifferentialGeometry.Topology.Manifold.ContMDiff.OpenSubtype
import Mathlib.Geometry.Manifold.Diffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Set _root_.Function _root_.Manifold _root_.TopologicalSpace
open scoped _root_.ContDiff _root_.Topology
noncomputable section
namespace DifferentialGeometry.Manifold.Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace G] [TopologicalSpace N] [ChartedSpace G N]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G} {n : ℕ∞ω}

def preimage (e : Diffeomorph I J M N n) (U : _root_.TopologicalSpace.Opens N) :
    Diffeomorph I J (⟨e ⁻¹' U, U.isOpen.preimage e.continuous⟩ : _root_.TopologicalSpace.Opens M) U n := by
  let S : _root_.TopologicalSpace.Opens M := ⟨e ⁻¹' U, U.isOpen.preimage e.continuous⟩
  let h : S ≃ₜ U := e.toHomeomorph.subtype (fun _ => Iff.rfl)
  have hf : ContMDiff I J n h := by
    apply (DifferentialGeometry.Manifold.contMDiff_subtypeVal_comp_iff U h).mp
    exact e.contMDiff.comp contMDiff_subtype_val
  have hg : ContMDiff J I n h.symm := by
    apply (DifferentialGeometry.Manifold.contMDiff_subtypeVal_comp_iff S h.symm).mp
    exact e.symm.contMDiff.comp contMDiff_subtype_val
  exact ⟨h.toEquiv, hf, hg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Diffeomorph.preimage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Diffeomorph.preimage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Diffeomorph.preimage ``Submission.DifferentialGeometry.Manifold.Diffeomorph.preimage


theorem preimage_apply (e : Diffeomorph I J M N n) (U : _root_.TopologicalSpace.Opens N)
    (x : (⟨e ⁻¹' U, U.isOpen.preimage e.continuous⟩ : _root_.TopologicalSpace.Opens M)) :
    (preimage e U x : N) = e x.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Diffeomorph.preimage_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Diffeomorph.preimage_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Diffeomorph.preimage_apply ``Submission.DifferentialGeometry.Manifold.Diffeomorph.preimage_apply


theorem preimage_symm_apply (e : Diffeomorph I J M N n) (U : _root_.TopologicalSpace.Opens N) (y : U) :
    ((preimage e U).symm y : M) = e.symm y.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Diffeomorph.preimage_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Diffeomorph.preimage_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Diffeomorph.preimage_symm_apply ``Submission.DifferentialGeometry.Manifold.Diffeomorph.preimage_symm_apply

end DifferentialGeometry.Manifold.Diffeomorph
