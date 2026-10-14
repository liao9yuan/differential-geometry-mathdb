import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Manifold
open scoped _root_.Topology _root_.ContDiff _root_.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in


theorem continuousOn_source_tangentMap {r : V → M} {U : Set V} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, V) I 1 r U) :
    ContinuousOn (fun p : V × V =>
      TotalSpace.mk' E (r p.1) (mfderiv 𝓘(ℝ, V) I r p.1 p.2)) (U ×ˢ _root_.Set.univ) := by
  have htr := hr.continuousOn_tangentMapWithin le_rfl hU.uniqueMDiffOn
  have hv : Continuous (fun p : V × V =>
      (TotalSpace.mk' V p.1 p.2 : TangentBundle 𝓘(ℝ, V) V)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, V)).symm.continuous
  apply (htr.comp hv.continuousOn (fun p hp => hp.1)).congr
  intro p hp
  dsimp only [_root_.Function.comp_apply, tangentMapWithin]
  rw [mfderivWithin_of_mem_nhds (hU.mem_nhds hp.1)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.continuousOn_source_tangentMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.continuousOn_source_tangentMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.continuousOn_source_tangentMap ``Submission.DifferentialGeometry.Geometry.continuousOn_source_tangentMap

omit [IsManifold I ∞ M] in
set_option backward.isDefEq.respectTransparency false in
theorem tangent_velocity_comp {r : V → M} {v : ℝ → V} {t : ℝ}
    (hr : MDifferentiableAt 𝓘(ℝ, V) I r (v t)) (hv : DifferentiableAt ℝ v t) :
    tangentMap 𝓘(ℝ, ℝ) I (r ∘ v) (TotalSpace.mk' ℝ t (1 : ℝ)) =
      TotalSpace.mk' E (r (v t)) (mfderiv 𝓘(ℝ, V) I r (v t) (deriv v t)) := by
  rw [tangentMap_comp_at _ hr hv.mdifferentiableAt]
  have hDv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V) v t (1 : ℝ) = deriv v t := by
    rw [mfderiv_eq_fderiv]
    exact fderiv_apply_one_eq_deriv (𝕜 := ℝ) (f := v) (x := t)
  simp only [tangentMap, hDv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.tangent_velocity_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.tangent_velocity_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.tangent_velocity_comp ``Submission.DifferentialGeometry.Geometry.tangent_velocity_comp

omit [IsManifold I ∞ M] in
theorem source_mfderiv_line {r : V → M} {z : V}
    (hr : MDifferentiableAt 𝓘(ℝ, V) I r z) (v : V) :
    mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ => r (z + t • v)) 0 (1 : ℝ) =
      mfderiv 𝓘(ℝ, V) I r z v := by
  have hl : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h := tangent_velocity_comp (r := r) (v := fun t : ℝ => z + t • v)
    (t := 0) (by simpa using hr) hl.differentiableAt
  have heq := congrArg (fun p : TangentBundle I M => (p.2 : E)) h
  change mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ => r (z + t • v)) 0 (1 : ℝ) =
    mfderiv 𝓘(ℝ, V) I r (z + 0 • v) (deriv (fun t : ℝ => z + t • v) 0) at heq
  erw [hl.deriv, zero_smul, add_zero] at heq
  exact heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.source_mfderiv_line then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.source_mfderiv_line"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.source_mfderiv_line ``Submission.DifferentialGeometry.Geometry.source_mfderiv_line

end DifferentialGeometry.Geometry
