import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskCovariantCoordinates
import Submission.DifferentialGeometry.Geometry.Comparison.Variation.Covariant.TwoParameterFields

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.Filter
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Variation
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



def diskMapCovariantThirdPartial (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (z v w x : ℂ) : TangentSpace 𝓘(ℝ, E) (U z) :=
  covDerivAlong g (fun t : ℝ => U (z + t • v))
    (fun t : ℝ => diskMapCovariantPartial g U (z + t • v) w x) 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapCovariantThirdPartial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapCovariantThirdPartial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapCovariantThirdPartial ``Submission.DifferentialGeometry.Geometry.diskMapCovariantThirdPartial

omit [FiniteDimensional ℝ E] in
private theorem diskPartial_plane_smooth {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {z : ℂ} (hz : z ∈ s) (v w x : ℂ) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q : ℝ × ℝ => TotalSpace.mk' E (U ((z + q.1 • v) + q.2 • w))
        (diskMapPartial (E := E) U ((z + q.1 • v) + q.2 • w) x)) (0, 0) := by
  let plane : ℝ × ℝ → ℂ := fun q => (z + q.1 • v) + q.2 • w
  have hp : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ) ∞ plane :=
    contMDiff_const.add (contMDiff_fst.smul contMDiff_const) |>.add
      (contMDiff_snd.smul contMDiff_const)
  have hp0 : plane (0, 0) = z := by simp [plane]
  have h := ((contMDiffOn_source_partial hs hU (m := ∞) (by simp) x) z hz).contMDiffAt
    (hs.mem_nhds hz)
  have hcomp := h.comp_of_eq (hp.contMDiffAt (x := (0, 0))) hp0
  exact hcomp.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.diskPartial_plane_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.diskPartial_plane_smooth target :: scope.openDecls } }



theorem contMDiffAt_diskMapCovariantPartial_line
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {z : ℂ} (hz : z ∈ s) (v w x : ℂ) :
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 1
      (fun t : ℝ => TotalSpace.mk' E (U (z + t • v))
        (diskMapCovariantPartial g U (z + t • v) w x)) 0 := by
  let plane : ℝ × ℝ → ℂ := fun q => (z + q.1 • v) + q.2 • w
  have hV := diskPartial_plane_smooth hs hU hz v w x
  have hcov := cov_snd_mdiff_at g (fun a b => U (plane (a, b)))
    (fun a b => diskMapPartial U (plane (a, b)) x) 0 0 hV
  have hi : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 1
      (fun a : ℝ => (a, (0 : ℝ))) 0 := contMDiffAt_id.prodMk contMDiffAt_const
  have hh := hcov.comp (f := fun a : ℝ => (a, (0 : ℝ))) 0 hi
  convert hh using 1
  funext a
  dsimp only [Function.comp_apply, plane]
  congr 1
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contMDiffAt_diskMapCovariantPartial_line then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contMDiffAt_diskMapCovariantPartial_line"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contMDiffAt_diskMapCovariantPartial_line ``Submission.DifferentialGeometry.Geometry.contMDiffAt_diskMapCovariantPartial_line




theorem diskMapCovariantThirdPartial_commute [T2Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {z : ℂ} (hz : z ∈ s) (v w x : ℂ) :
    diskMapCovariantThirdPartial g U z v w x - diskMapCovariantThirdPartial g U z w v x =
      riemannOp (LeviCivita g) (U z)
        (diskMapPartial U z v) (diskMapPartial U z w) (diskMapPartial U z x) := by
  let plane : ℝ × ℝ → ℂ := fun q => (z + q.1 • v) + q.2 • w
  have hV := diskPartial_plane_smooth hs hU hz v w x
  have hc := cov_commute_at g (fun a b => U (plane (a, b)))
    (fun a b => diskMapPartial U (plane (a, b)) x) 0 0 hV
  have hswap (b : ℝ) :
      covDerivAlong g (fun a : ℝ => U ((z + a • v) + b • w))
        (fun a : ℝ => diskMapPartial U ((z + a • v) + b • w) x) 0 =
      diskMapCovariantPartial g U (z + b • w) v x := by
    unfold diskMapCovariantPartial
    congr 1 <;> funext a <;> congr 1 <;> abel
  dsimp only [plane] at hc
  have hleft :
      covDerivAlong g (fun a : ℝ => U ((z + a • v) + (0 : ℝ) • w))
        (fun a : ℝ => diskMapCovariantPartial g U (z + a • v) w x) 0 =
      diskMapCovariantThirdPartial g U z v w x := by
    unfold diskMapCovariantThirdPartial
    congr 1
    funext a
    simp
  have hright :
      covDerivAlong g (fun b : ℝ => U ((z + (0 : ℝ) • v) + b • w))
        (fun b : ℝ => diskMapCovariantPartial g U (z + b • w) v x) 0 =
      diskMapCovariantThirdPartial g U z w v x := by
    unfold diskMapCovariantThirdPartial
    congr 1
    funext b
    simp
  change (covDerivAlong g (fun a : ℝ => U ((z + a • v) + (0 : ℝ) • w))
    (fun a => diskMapCovariantPartial g U (z + a • v) w x) 0) - _ = _ at hc
  rw [hleft] at hc
  simp only [hswap] at hc
  rw [hright] at hc
  have hd := ((hU z hz).contMDiffAt (hs.mem_nhds hz)).mdifferentiableAt (by simp)
  refine hc.trans ?_
  let R : M → E → E → E → E := fun p A B C => riemannOp (LeviCivita g) p A B C
  change R (U (z + (0 : ℝ) • v + (0 : ℝ) • w)) _ _ _ = R (U z) _ _ _
  congr 1
  · simp
  · have heq : (fun a : ℝ => U ((z + a • v) + (0 : ℝ) • w)) =
        (fun a : ℝ => U (z + a • v)) := by funext a; simp
    rw [heq]
    exact source_mfderiv_line hd v
  · have heq : (fun b : ℝ => U ((z + (0 : ℝ) • v) + b • w)) =
        (fun b : ℝ => U (z + b • w)) := by funext b; simp
    rw [heq]
    exact source_mfderiv_line hd w
  · congr 1
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapCovariantThirdPartial_commute then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapCovariantThirdPartial_commute"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapCovariantThirdPartial_commute ``Submission.DifferentialGeometry.Geometry.diskMapCovariantThirdPartial_commute

end DifferentialGeometry.Geometry
