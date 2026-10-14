import Submission.DifferentialGeometry.Geometry.Metric.Construction.BumpExtension
import Mathlib.Geometry.Manifold.PartitionOfUnity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.TopologicalSpace
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem exists_smooth_metric_agrees_on_neighborhood_of_is_closed
    (R : SmoothRiemannianMetric I M) (U : _root_.TopologicalSpace.Opens M)
    (gU : SmoothRiemannianMetric I U) {K : Set M}
    (hK : IsClosed K) (hKU : K ⊆ (U : Set M)) :
    ∃ (g : SmoothRiemannianMetric I M) (V : _root_.TopologicalSpace.Opens M),
      K ⊆ (V : Set M) ∧ ∃ hVU : (V : Set M) ⊆ (U : Set M),
        (∀ (x : M) (hx : x ∈ V) (v w : TangentSpace I x),
          g.inner x v w = gU.inner ⟨x, hVU hx⟩ v w) ∧
        (∀ (x : M), x ∉ U → ∀ v w : TangentSpace I x,
          g.inner x v w = R.inner x v w) := by
  let _ : SecondCountableTopology H := I.secondCountableTopology
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let _ : LocallyCompactSpace U := ChartedSpace.locallyCompactSpace H U
  let _ : SecondCountableTopology U := inferInstance
  let _ : SigmaCompactSpace U := inferInstance
  let _ : NormalSpace M := inferInstance
  obtain ⟨W, hWopen, hKW, hWcl⟩ :=
    normal_exists_closure_subset hK U.isOpen hKU
  obtain ⟨χ, hχone, hχzero, hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := I) (M := M)
      (n := (⊤ : ℕ∞)) hK (hKW.trans hWopen.interior_eq.ge)
  have hχsupport : tsupport (χ : M → ℝ) ⊆ (U : Set M) := by
    apply (closure_mono ?_).trans hWcl
    intro x hx
    by_contra hxW
    exact hx (hχzero x hxW)
  obtain ⟨V, hVopen, hKV, hVone⟩ := mem_nhdsSet_iff_exists.mp hχone
  let O : _root_.TopologicalSpace.Opens M := ⟨V ∩ U, hVopen.inter U.isOpen⟩
  have hKO : K ⊆ (O : Set M) := fun x hx => ⟨hKV hx, hKU hx⟩
  have hOU : (O : Set M) ⊆ (U : Set M) := _root_.Set.inter_subset_right
  let g := R.bumpExtendOpen U gU χ χ.contMDiff hχrange hχsupport
  refine ⟨g, O, hKO, hOU, ?_, ?_⟩
  · intro x hx v w
    exact bumpExtendOpen_eq_gU_on R U gU χ χ.contMDiff hχrange hχsupport O
      (fun y hy => hVone hy.1) hOU x hx v w
  · intro x hx v w
    exact bumpExtendOpen_inner_of_notMem_tsupport R U gU χ χ.contMDiff hχrange hχsupport
      x (fun h => hx (hχsupport h)) v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.exists_smooth_metric_agrees_on_neighborhood_of_is_closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.exists_smooth_metric_agrees_on_neighborhood_of_is_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.exists_smooth_metric_agrees_on_neighborhood_of_is_closed ``Submission.DifferentialGeometry.exists_smooth_metric_agrees_on_neighborhood_of_is_closed

theorem exists_smooth_metric_agrees_on_neighborhood_of_is_compact
    (R : SmoothRiemannianMetric I M) (U : _root_.TopologicalSpace.Opens M)
    (gU : SmoothRiemannianMetric I U) {K : Set M}
    (hK : IsCompact K) (hKU : K ⊆ (U : Set M)) :
    ∃ (g : SmoothRiemannianMetric I M) (V : _root_.TopologicalSpace.Opens M),
      K ⊆ (V : Set M) ∧ ∃ hVU : (V : Set M) ⊆ (U : Set M),
        (∀ (x : M) (hx : x ∈ V) (v w : TangentSpace I x),
          g.inner x v w = gU.inner ⟨x, hVU hx⟩ v w) ∧
        (∀ (x : M), x ∉ U → ∀ v w : TangentSpace I x,
          g.inner x v w = R.inner x v w) :=
  exists_smooth_metric_agrees_on_neighborhood_of_is_closed R U gU hK.isClosed hKU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.exists_smooth_metric_agrees_on_neighborhood_of_is_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.exists_smooth_metric_agrees_on_neighborhood_of_is_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.exists_smooth_metric_agrees_on_neighborhood_of_is_compact ``Submission.DifferentialGeometry.exists_smooth_metric_agrees_on_neighborhood_of_is_compact

end DifferentialGeometry
