import Submission.DifferentialGeometry.Geometry.Boundary.ModelExtension
import Submission.DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
import Mathlib.Analysis.Normed.Module.FiniteDimension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter _root_.Topology
open scoped _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Geometry.Boundary

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [HasSmoothBoundary E H I]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_localInverse_of_model
    {f : E → F} {U : Set E} {y : E} (hU : IsOpen U) (hyU : y ∈ U)
    (hy : y ∈ _root_.Set.range I) (hf : ContDiffOn ℝ ∞ f (U ∩ _root_.Set.range I))
    (hinj : Function.Injective (fderivWithin ℝ f (_root_.Set.range I) y))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    ∃ e : OpenPartialHomeomorph E F,
      y ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      EqOn e f (e.source ∩ _root_.Set.range I) := by
  have hex : ∃ V : Set E, IsOpen V ∧ y ∈ V ∧ V ⊆ U ∧
      ∃ g : E → F, ContDiffOn ℝ ∞ g V ∧ _root_.Set.EqOn g f (V ∩ _root_.Set.range I) := by
    by_cases hb : y ∈ frontier (_root_.Set.range I)
    · exact exists_contDiffOn_extension_of_model I hU hyU hb hf
    · have hi : y ∈ interior (_root_.Set.range I) := (mem_interior_iff_notMem_frontier hy).mpr hb
      exact ⟨U ∩ interior (_root_.Set.range I), hU.inter isOpen_interior, ⟨hyU, hi⟩,
        _root_.Set.inter_subset_left, f, hf.mono (_root_.Set.inter_subset_inter_right U interior_subset),
        fun _ _ ↦ rfl⟩
  obtain ⟨V, hV, hyV, hVU, g, hg, heq⟩ := hex
  have hevent : g =ᶠ[𝓝[_root_.Set.range I] y] f := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hyV), self_mem_nhdsWithin]
      with z hz hzI
    exact heq ⟨hz, hzI⟩
  have hdg := ((hg.contDiffAt (hV.mem_nhds hyV)).differentiableAt (by simp)).hasFDerivAt
  have hdf : fderiv ℝ g y = fderivWithin ℝ f (_root_.Set.range I) y :=
    (hdg.hasFDerivWithinAt.congr_of_eventuallyEq hevent.symm (heq ⟨hyV, hy⟩).symm).fderivWithin
      (I.uniqueDiffOn y hy) |>.symm
  let A := fderivWithin ℝ f (_root_.Set.range I) y
  let L : E ≃L[ℝ] F := (A.toLinearMap.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv
  have hd : HasFDerivAt g (L : E →L[ℝ] F) y := by
    change HasFDerivAt g A y
    rwa [hdf] at hdg
  obtain ⟨e, hye, heV, he, hi, heg⟩ :=
    DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivAt_equiv hg hV hyV hd
  exact ⟨e, hye, heV.trans hVU, he, hi, fun z hz ↦ (heg z).trans (heq ⟨heV hz.1, hz.2⟩)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Boundary.exists_localInverse_of_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Boundary.exists_localInverse_of_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Boundary.exists_localInverse_of_model ``Submission.DifferentialGeometry.Geometry.Boundary.exists_localInverse_of_model

end DifferentialGeometry.Geometry.Boundary
