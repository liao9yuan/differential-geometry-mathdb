import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.Diffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Manifold _root_.TopologicalSpace
open scoped _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Manifold.Interval


def shorterStripDiffeomorph
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (J : ModelWithCorners ℝ E H)
    {a ε : ℝ} [Fact ((0 : ℝ) < a)] [Fact ((0 : ℝ) < ε)] (haε : a ≤ ε) :
    let U : _root_.TopologicalSpace.Opens (B × _root_.Set.Icc (0 : ℝ) a) :=
      ⟨{q | q.2.val < a}, isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
    let V : _root_.TopologicalSpace.Opens (B × _root_.Set.Icc (0 : ℝ) ε) :=
      ⟨{q | q.2.val < a}, isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
    Diffeomorph (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)) U V ∞ := by
  intro U V
  let f : U → V := fun q =>
    ⟨(q.val.1, ⟨q.val.2.val, q.val.2.property.1, q.val.2.property.2.trans haε⟩), q.property⟩
  let g : V → U := fun q =>
    ⟨(q.val.1, ⟨q.val.2.val, q.val.2.property.1, q.property.le⟩), q.property⟩
  have hf : ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)) ∞ f := by
    apply (ContMDiff.subtypeVal_comp_iff V f).mp
    apply (contMDiff_fst.comp contMDiff_subtype_val).prodMk
    apply (contMDiff_iff_comp_subtypeVal_Icc (n := ∞)).mpr
    exact ⟨by fun_prop, (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := a)).comp
      (contMDiff_snd.comp contMDiff_subtype_val)⟩
  have hg : ContMDiff (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1)) ∞ g := by
    apply (ContMDiff.subtypeVal_comp_iff U g).mp
    apply (contMDiff_fst.comp contMDiff_subtype_val).prodMk
    apply (contMDiff_iff_comp_subtypeVal_Icc (n := ∞)).mpr
    exact ⟨by fun_prop, (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := ε)).comp
      (contMDiff_snd.comp contMDiff_subtype_val)⟩
  exact ⟨⟨f, g, (fun _ => rfl), (fun _ => rfl)⟩, hf, hg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Interval.shorterStripDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Interval.shorterStripDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Interval.shorterStripDiffeomorph ``Submission.DifferentialGeometry.Manifold.Interval.shorterStripDiffeomorph

end DifferentialGeometry.Manifold.Interval
