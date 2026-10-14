import Submission.DifferentialGeometry.Geometry.Neck.SpatialRestriction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonComposition
import Submission.DifferentialGeometry.Geometry.Curvature.EmbeddingIsometry
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N] [T2Space N]

theorem SpatialNeck.exists_image_of_local_isometry
    {g : SmoothRiemannianMetric I3 M} {h : SmoothRiemannianMetric I3 N}
    {eps : ℝ} {p : M} (nk : SpatialNeck g eps p)
    (f : M → N) (hf : IsLocalDiffeomorph I3 I3 ∞ f) (hinj : _root_.Function.Injective f)
    (hmetric : ∀ (x : M) (v w : TangentSpace I3 x),
      g.inner x v w = h.inner (f x) (mfderiv I3 I3 f x v) (mfderiv I3 I3 f x w)) :
    ∃ out : SpatialNeck h eps (f p), out.center = nk.center ∧
      (∀ z, out.map z = f (nk.map z)) ∧ out.map.source = nk.map.source := by
  have hne : (_root_.Set.univ : Set M).Nonempty := ⟨p,_root_.Set.mem_univ _⟩
  obtain ⟨F,hsource,_,hmap⟩ := IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    (fun x : (_root_.Set.univ : Set M) => hf x.val) isOpen_univ hne hinj.injOn
  let Φ := partialDiffeomorphTransMixed nk.map F
  have hΦ (z : Cylinder) : Φ z = f (nk.map z) := by
    change F (nk.map z) = _
    exact congrFun hmap _
  have hsrc : Φ.source = nk.map.source := by
    ext z
    change (z ∈ nk.map.source ∧ nk.map z ∈ F.source) ↔ z ∈ nk.map.source
    rw [hsource]
    simp only [_root_.Set.mem_univ,and_true]
  have hscalar : metricScalarAt g p = metricScalarAt h (f p) :=
    (curvature_of_injective_local_isometry g h f hf hinj hmetric p).1
  have hQ : 0 < metricScalarAt h (f p) := hscalar ▸ nk.Q_pos
  have hder (z : Cylinder) (hz : z ∈ nk.map.source) (v : TangentSpace IC z) :
      mfderiv IC I3 Φ z v = mfderiv I3 I3 f (nk.map z) (mfderiv IC I3 nk.map z v) := by
    have he : (Φ : Cylinder → N) = f ∘ nk.map := funext hΦ
    rw [he,mfderiv_comp z ((hf _).mdifferentiableAt (by simp))
      (nk.map.mdifferentiableAt (by simp) hz)]
    rfl
  let cmp : MetricComparisonOn (fun _ => nk.cylinder.metric 0)
      (fun _ => DifferentialGeometry.scaleMetric (metricScalarAt h (f p)) hQ h) Φ
      (_root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹) {0} ⌈eps⁻¹⌉₊ eps :=
    { pullback := nk.comparison.pullback
      pullback_eq := by
        intro s z hz v
        rw [nk.comparison.pullback_eq s z hz v]
        simp only [scaleMetric_inner]
        have hd0 := hder z (nk.domain hz) (v 0)
        have hd1 := hder z (nk.domain hz) (v 1)
        change metricScalarAt g p * g.inner (nk.map z)
            (show ThreeSpace from mfderiv IC I3 nk.map z (v 0))
            (show ThreeSpace from mfderiv IC I3 nk.map z (v 1)) =
          metricScalarAt h (f p) * h.inner (Φ z)
            (show ThreeSpace from mfderiv IC I3 Φ z (v 0))
            (show ThreeSpace from mfderiv IC I3 Φ z (v 1))
        rw [hd0,hd1,hmetric,hscalar,hΦ]
      jet := nk.comparison.jet
      jet_zero := nk.comparison.jet_zero
      jet_succ := nk.comparison.jet_succ
      equivalence := nk.comparison.equivalence
      close := nk.comparison.close }
  refine ⟨{
    eps_pos := nk.eps_pos
    eps_small := nk.eps_small
    Q_pos := hQ
    cylinder := nk.cylinder
    map := Φ
    center := nk.center
    center_eq := ?_
    domain := fun z hz => hsrc.symm ▸ nk.domain hz
    comparison := cmp },rfl,hΦ,hsrc⟩
  rw [hΦ,nk.center_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_image_of_local_isometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_image_of_local_isometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_image_of_local_isometry ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.exists_image_of_local_isometry

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
