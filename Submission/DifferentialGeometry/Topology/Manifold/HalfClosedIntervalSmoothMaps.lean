import Submission.DifferentialGeometry.Topology.Manifold.HalfClosedInterval

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E H P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace P] [ChartedSpace H P]

theorem contMDiff_halfClosedInterval_of_val {a b : ℝ} (hab : a < b)
    (f : P → _root_.Set.Ico a b) (hf : ContMDiff I 𝓘(ℝ) ∞ (fun p => (f p).val)) :
    let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico a b) := halfClosedIntervalChartedSpace hab
    ContMDiff I (𝓡∂ 1) ∞ f := by
  let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico a b) := halfClosedIntervalChartedSpace hab
  let e : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).symm
  have hc : ContMDiff I (𝓡 1) ∞ (fun p => e ((f p).val - a)) :=
    e.contDiff.contMDiff.comp (hf.sub contMDiff_const)
  dsimp only
  intro p
  rw [contMDiffAt_iff_target]
  refine ⟨_root_.Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hf.continuous.continuousAt, ?_⟩
  have he : (extChartAt (𝓡∂ 1) (f p) ∘ f) = (fun q => e ((f q).val - a)) := by
    funext q
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change (extChartAt (𝓡∂ 1) (f p) (f q)) 0 = (f q).val - a
    exact halfClosedInterval_extChartAt_apply hab (f p) (f q)
  rw [he]
  exact hc.contMDiffAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.contMDiff_halfClosedInterval_of_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.contMDiff_halfClosedInterval_of_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.contMDiff_halfClosedInterval_of_val ``Submission.DifferentialGeometry.Topology.Manifold.contMDiff_halfClosedInterval_of_val
end DifferentialGeometry.Topology.Manifold
