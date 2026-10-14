import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.DiffeomorphRows
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NormalizedConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ShrinkingCylinder
import Submission.DifferentialGeometry.Geometry.Metric.PullbackCompleteness
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness

universe u
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat target :: scope.openDecls } }

theorem exists_pointed_convergence_of_cylindrical_local_pullbacks
    {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel} (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (e : NeckCylinder ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ P.M)
    {v : ℝ} (hv : v ≤ 0) (f : ℕ → ℕ)
    (eps : ℕ → ℝ) (heps : ∀ i, 0 < eps i) (hepslim : _root_.Filter.Tendsto eps _root_.Filter.atTop (𝓝 0))
    (hp : ∀ i, e.symm P.basepoint ∈ neckBuffer (eps i))
    (psi : ∀ i, neckBuffer (eps i) → (X.obj (f i)).M)
    (hpsi : ∀ i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (psi i))
    (hinj : ∀ i, Function.Injective (psi i))
    (hbase : ∀ i, psi i ⟨e.symm P.basepoint, hp i⟩ = (X.obj (f i)).basepoint)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hδlim : _root_.Filter.Tendsto δ _root_.Filter.atTop (𝓝 0))
    (Gm : ∀ n, ℕ → SmoothRiemannianMetric NeckCylinderModel (neckBuffer (δ n)))
    (hconv : ∀ n, MetricCInfConvergenceOnCompacts (Gm n)
      ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v).restrictOpen (neckBuffer (δ n)))
      (roundCylinderMetric.restrictOpen (neckBuffer (δ n))))
    (hmetric : ∀ n, ∀ᶠ i in _root_.Filter.atTop, ∃ hni : eps i ≤ δ n,
      ∀ (z : neckBuffer (δ n)) (a b : TangentSpace NeckCylinderModel z),
        (Gm n i).inner z a b = (X.obj (f i)).metric.inner
          (psi i (TopologicalSpace.Opens.inclusion (neckBuffer_le_of_le (heps i) hni) z))
          (mfderiv NeckCylinderModel ThreeModel
            (fun w : neckBuffer (δ n) => psi i (TopologicalSpace.Opens.inclusion
              (neckBuffer_le_of_le (heps i) hni) w)) z a)
          (mfderiv NeckCylinderModel ThreeModel
            (fun w : neckBuffer (δ n) => psi i (TopologicalSpace.Opens.inclusion
              (neckBuffer_le_of_le (heps i) hni) w)) z b)) :
    let Pτ : PointedRiemannianManifold ThreeModel := { P with
      metric := Diffeomorph.pullbackMetricCross (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v) e.symm}
    RiemannianMetricComplete Pτ.metric ∧
      (∀ y : Pτ.M, metricScalarAt Pτ.metric y = (1 - v)⁻¹) ∧
      (∀ y : Pτ.M, metricScalarAt Pτ.metric y ≤ 1) ∧
      Diffeomorph.pullbackMetricCross Pτ.metric e =
        (scaleMetric (2 * (1 - v)) (mul_pos (by norm_num) (by linarith))
          (Geometry.roundMetric (E := ThreeSpace) (n := 2))).prod (euclideanMetric (E := ℝ)) ∧
      ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ maps : PointedRiemannianConvergenceMaps X Pτ (f ∘ k),
        (∀ i (z : neckBuffer (eps (k i))), maps.map i (e z) = psi (k i) z) ∧
        (∀ i, maps.source i ⊆ e.symm ⁻¹' neckBuffer (eps (k i))) ∧
        (∀ i, IsCompact (closure (maps.source i))) ∧ (∀ i, IsConnected (maps.source i)) ∧
        ∃ C : MetricConvergenceData maps,
          ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData maps i := by
  intro Pτ
  let _ : PreconnectedSpace (Sphere 2) := Subtype.preconnectedSpace
    (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) 1)
  let _ : PreconnectedSpace P.M := e.surjective.denseRange.preconnectedSpace e.continuous
  have hv1 : v < 1 := hv.trans_lt zero_lt_one
  have hc : RiemannianMetricComplete Pτ.metric :=
    RiemannianMetricComplete.pullbackCross _ e.symm
      (PDE.RicciFlow.shrinkingCylinderMetric_complete (E := ThreeSpace) v)
  have hscalar (y : Pτ.M) : metricScalarAt Pτ.metric y = (1 - v)⁻¹ := by
    change metricScalarAt (Diffeomorph.pullbackMetricCross _ e.symm) y = _
    rw [metricScalar_cross,
      PDE.RicciFlow.shrinkingCylinderMetric_scalar hv1]
  have hbound (y : Pτ.M) : metricScalarAt Pτ.metric y ≤ 1 := by
    rw [hscalar]
    exact inv_le_one_of_one_le₀ (by linarith)
  have hproduct : Diffeomorph.pullbackMetricCross Pτ.metric e =
      (scaleMetric (2 * (1 - v)) (mul_pos (by norm_num) (by linarith))
        (Geometry.roundMetric (E := ThreeSpace) (n := 2))).prod (euclideanMetric (E := ℝ)) := by
    change Diffeomorph.pullbackMetricCross (Diffeomorph.pullbackMetricCross _ e.symm) e = _
    rw [show Diffeomorph.pullbackMetricCross (Diffeomorph.pullbackMetricCross
        (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v) e.symm) e =
        PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v from
      Diffeomorph.pullbackMetricCross_symm_eq_iff.mpr rfl]
    exact PDE.RicciFlow.shrinkingCylinderMetric_eq_prod hv1
  refine ⟨hc, hscalar, hbound, hproduct, ?_⟩
  have hexhaust_general {η : ℕ → ℝ} (hη : ∀ i, 0 < η i) (hηlim : _root_.Filter.Tendsto η _root_.Filter.atTop (𝓝 0))
      (K : Set NeckCylinder) (hK : IsCompact K) : ∀ᶠ i in _root_.Filter.atTop, K ⊆ neckBuffer (η i) := by
    obtain ⟨A, hA⟩ := hK.bddAbove_image (continuous_abs.comp continuous_snd).continuousOn
    have hpA : 0 < (|A| + 1)⁻¹ := by positivity
    filter_upwards [hηlim.eventually_lt_const hpA] with i hi
    have hwidth : |A| + 1 < (η i)⁻¹ := by
      simpa only [inv_inv] using (inv_lt_inv₀ hpA (hη i)).mpr hi
    intro z hz
    have hzA : |z.2| ≤ A := hA (_root_.Set.mem_image_of_mem (fun z : NeckCylinder => |z.2|) hz)
    change -(η i)⁻¹ - 1 < z.2 ∧ z.2 < (η i)⁻¹ + 1
    constructor <;> linarith [le_abs_self A, le_abs_self z.2, neg_le_abs z.2]
  have hexhaust := hexhaust_general heps hepslim
  apply exists_pointed_convergence_of_local_pullbacks_along_diffeomorph
    (P := Pτ) e.symm (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) v) rfl f
      (fun i => neckBuffer (eps i)) hp psi hpsi hinj hbase hexhaust
  intro K hK
  obtain ⟨n, hn⟩ := (hexhaust_general hδ hδlim K hK).exists
  let _ : SigmaCompactSpace (neckBuffer (δ n)) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen NeckCylinderModel (neckBuffer (δ n)).isOpen)
  refine ⟨neckBuffer (δ n), hn, Gm n,
    (hconv n).change_reference _, ?_⟩
  exact (hmetric n).mono fun i hi => by
    obtain ⟨hni, hh⟩ := hi
    exact ⟨neckBuffer_le_of_le (heps i) hni, hh⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_pointed_convergence_of_cylindrical_local_pullbacks then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_pointed_convergence_of_cylindrical_local_pullbacks"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_pointed_convergence_of_cylindrical_local_pullbacks ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_pointed_convergence_of_cylindrical_local_pullbacks

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
