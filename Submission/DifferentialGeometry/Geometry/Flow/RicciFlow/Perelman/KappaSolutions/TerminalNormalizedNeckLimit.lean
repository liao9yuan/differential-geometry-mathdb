import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AscrNormalizedSequence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientKappaFixedCompactness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalNormalizedCylinder
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderScalarNormalization
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedCylinderNecks
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckScaling
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StrongNeckRescaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_terminalNormalized_neckWitnesses_limit_of_diffeomorph_euclidean
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F)
    (hEuclidean : Nonempty (F.M ≃ₘ⟮I3, 𝓡 3⟯ ThreeSpace))
    (p : F.M) (x : ℕ → F.M) (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (hescape : _root_.Filter.Tendsto (fun i => (riemannianEDistOf (F.S.base.metric 0) p (x i)).toReal) _root_.Filter.atTop _root_.Filter.atTop)
    (hscaled : _root_.Filter.Tendsto (fun i => Real.sqrt (F.S.scalar 0 (x i)) *
      (riemannianEDistOf (F.S.base.metric 0) p (x i)).toReal) _root_.Filter.atTop _root_.Filter.atTop) :
    let hK := ancientKappaThree_toKLim F hF (by simp [ThreeSpace])
    let Y := terminalCurvatureNormalizedFlowSeq F hK x hQ
    ∃ (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) (phi : ℕ → ℕ), StrictMono phi ∧
      ∃ Phi : PointedCGHMaps Y (L.atTime 0) phi,
        IsAncientKappaSolution kappa L ∧ PointedFlowScalarAtBase L 1 ∧
        (∀ a b : ℝ, a ≤ b → b ≤ 0 → ∀ K : Set L.M, IsCompact K → ∀ order : ℕ,
          ∀ delta : ℝ, 0 < delta → ∀ᶠ i in _root_.Filter.atTop,
            Nonempty (MetricComparisonOn L.S.base.metric (Y.term (phi i)).S.base.metric
              (Phi.map i) K (_root_.Set.Icc a b) order delta)) ∧
        ∃ (mark : SpatialNeckSphere)
          (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I3⟯ L.M),
          e (mark, 0) = L.basepoint ∧
          (∀ s : ℝ, ∀ hs : s ≤ 0, Diffeomorph.pullbackMetricCross (L.S.base.metric s) e =
            scalarOneShrinkingCylinderMetric s (hs.trans_lt (by norm_num))) ∧
          ∀ epsilon eta : ℝ, 0 < epsilon → epsilon < 1 → 0 < eta → ∀ᶠ i in _root_.Filter.atTop,
            ∃ W : StrongNeckWitness F.S mark (x (phi i)) 0 epsilon,
              ∃ V : SpatialNeckWitness (F.S.base.metric 0) mark (x (phi i)) eta,
                (∀ z : spatialNeckBuffer epsilon, W.embedding z = Phi.map i (e (z : SpatialNeckCylinder))) ∧
                (∀ z : spatialNeckBuffer eta, V.embedding z = Phi.map i
                  (e (cylinderAxialScale (Real.sqrt 2) (by positivity) (z : SpatialNeckCylinder)))) ∧
                W.embedding '' spatialNeckCentralDomain epsilon = V.centralSphere := by
  intro hK Y
  have hterms (i : ℕ) : IsAncientKappaSolution kappa (Y.term i) :=
    isAncientKappaSolution_curvatureNormalizedFlow F hF 0 (F.S.scalar 0 (x i))
      (hQ i) (by simp) (x i) rfl
  have hbase : ∀ i, PointedFlowScalarAtBase (Y.term i) 1 :=
    terminalCurvatureNormalizedFlowSeq_scalar_base F hK x hQ
  obtain ⟨L, phi, hphi, Phi, hL, hLbase, _hKL, hconv, hcmp⟩ :=
    exists_ancientKappa_fixed_kappa_compactness (fun i => Y.term i) hterms hbase
  let hPhi : PointedCGHMaps Y (L.atTime 0) phi := Phi
  obtain ⟨C0, hC0⟩ := hconv 0 le_rfl
  obtain ⟨T, hT, d, hmetric⟩ := exists_cylinder_of_terminalCurvatureNormalizedFlowSeq_limit
    F L hK hL (by simp [ThreeSpace]) p x hQ hescape hscaled hphi
      (hPhi.atTime (X := Y) (L := L) (phi := phi) 0) C0 hC0 hEuclidean
  obtain ⟨mark, e, hmarked, _hzero, hflow⟩ := exists_marked_normalized_cylinder
    L.S.base.metric T hT d hmetric L.basepoint hLbase
  have hmodel (s : ℝ) (hs : s ≤ 0) : Diffeomorph.pullbackMetricCross (L.S.base.metric s) e =
      scalarOneShrinkingCylinderMetric s (hs.trans_lt (by norm_num)) := by
    apply SmoothRiemannianMetric.ext_inner
    intro z V W
    have hpull := Diffeomorph.pullbackMetricCross_inner (L.S.base.metric s) e z V W
    have hh := hflow s hs z.1 z.2 V.1 W.1 V.2 W.2
    have hm := scalarOneShrinkingCylinderMetric_inner s (hs.trans_lt (by norm_num)) z.1 z.2 V.1 W.1 V.2 W.2
    exact hpull.trans (hh.trans hm.symm)
  refine ⟨L, phi, hphi, hPhi, hL, hLbase, hcmp, mark, e, hmarked, hmodel, ?_⟩
  intro epsilon eta hepsilon hepsilon1 heta
  have hnecks := pointedCylinderFlowLimit_eventually_neckWitnesses hPhi rfl hbase
    (fun K hK order delta hdelta => hcmp (-1) 0 (by norm_num) le_rfl K hK order delta hdelta)
    C0 hC0 (fun i => (hterms i).complete 0 (show (0 : ℝ) ≤ 0 from le_rfl)) mark e hmarked hmodel
    epsilon eta hepsilon hepsilon1 heta
  filter_upwards [hnecks] with i hi
  obtain ⟨W, V, hW, hV, hcentral⟩ := hi
  let W' := W.ofCurvatureNormalization F.S F.isSolution rfl mark (x (phi i)) 0 (by simp) (hQ (phi i))
  let property (g : SmoothRiemannianMetric I3 F.M) : Prop :=
    ∃ Vs : SpatialNeckWitness g mark (x (phi i)) eta,
      (∀ z : spatialNeckBuffer eta, Vs.embedding z = hPhi.map i
        (e (cylinderAxialScale (Real.sqrt 2) (by positivity) (z : SpatialNeckCylinder)))) ∧
      W.embedding '' spatialNeckCentralDomain epsilon = Vs.centralSphere
  have hproperty : property ((Y.term (phi i)).S.base.metric 0) := ⟨V, hV, hcentral⟩
  have heq := terminalCurvatureNormalizedFlowSeq_metric F hK x hQ (phi i)
  have hscaledProperty : property (scaleMetric (F.S.scalar 0 (x (phi i))) (hQ (phi i)) (F.S.base.metric 0)) :=
    Eq.mp (congrArg property heq) hproperty
  obtain ⟨Vscaled, hVscaled, hcentralScaled⟩ := hscaledProperty
  let V' := Vscaled.ofScaleMetric (F.S.scalar 0 (x (phi i))) (hQ (phi i))
  exact ⟨W', V', hW, hVscaled, hcentralScaled⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_terminalNormalized_neckWitnesses_limit_of_diffeomorph_euclidean then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_terminalNormalized_neckWitnesses_limit_of_diffeomorph_euclidean"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_terminalNormalized_neckWitnesses_limit_of_diffeomorph_euclidean ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_terminalNormalized_neckWitnesses_limit_of_diffeomorph_euclidean

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

noncomputable section

open _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact
theorem ancientKappaThree_exists_ascr_strongNeck_limit_of_diffeomorph_euclidean
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F)
    (hEuclidean : Nonempty (F.M ≃ₘ⟮I3, 𝓡 3⟯ ThreeSpace)) (p : F.M) :
    let hK := ancientKappaThree_toKLim F hF (by simp [ThreeSpace])
    let d := fun y z : F.M =>
      (riemannianEDistOf (F.S.base.metric 0) y z).toReal
    ∃ (x : ℕ → F.M) (r eps : ℕ → ℝ) (hQ : ∀ i, 0 < F.S.scalar 0 (x i)),
      (∀ i, 0 < r i ∧ r i ≤ d p (x i) / 6) ∧
      (∀ i, 0 < eps i ∧ eps i < 1) ∧ StrictAnti eps ∧
      _root_.Filter.Tendsto eps _root_.Filter.atTop (𝓝 0) ∧
      Pairwise (fun i j =>
        Disjoint
          {z : F.M | riemannianEDistOf (F.S.base.metric 0) z (x i) <
            ENNReal.ofReal (r i)}
          {z : F.M | riemannianEDistOf (F.S.base.metric 0) z (x j) <
            ENNReal.ofReal (r j)}) ∧
      _root_.Filter.Tendsto (fun i => d p (x i)) _root_.Filter.atTop _root_.Filter.atTop ∧
      _root_.Filter.Tendsto (fun i => F.S.scalar 0 (x i) * r i ^ 2) _root_.Filter.atTop _root_.Filter.atTop ∧
      _root_.Filter.Tendsto (fun i => d p (x i) / r i) _root_.Filter.atTop _root_.Filter.atTop ∧
      _root_.Filter.Tendsto (fun i => r i * Real.sqrt (F.S.scalar 0 (x i))) _root_.Filter.atTop _root_.Filter.atTop ∧
      _root_.Filter.Tendsto (fun i => Real.sqrt (F.S.scalar 0 (x i)) * d p (x i)) _root_.Filter.atTop _root_.Filter.atTop ∧
      (∀ i z, d z (x i) < r i →
        F.S.scalar 0 z ≤ (1 + eps i) * F.S.scalar 0 (x i)) ∧
      let Y := terminalCurvatureNormalizedFlowSeq F hK x hQ
      (∀ i, IsAncientKappaSolution kappa (Y.term i)) ∧
      (∀ i, PointedFlowScalarAtBase (Y.term i) 1) ∧
    ∃ (L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) (phi : ℕ → ℕ), StrictMono phi ∧
      ∃ Phi : PointedCGHMaps Y (L.atTime 0) phi,
        IsAncientKappaSolution kappa L ∧ PointedFlowScalarAtBase L 1 ∧
        (∀ a b : ℝ, a ≤ b → b ≤ 0 → ∀ K : Set L.M, IsCompact K → ∀ order : ℕ,
          ∀ delta : ℝ, 0 < delta → ∀ᶠ i in _root_.Filter.atTop,
            Nonempty (MetricComparisonOn L.S.base.metric (Y.term (phi i)).S.base.metric
              (Phi.map i) K (_root_.Set.Icc a b) order delta)) ∧
        ∃ (mark : SpatialNeckSphere)
          (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I3⟯ L.M),
          e (mark, 0) = L.basepoint ∧
          (∀ s : ℝ, ∀ hs : s ≤ 0, Diffeomorph.pullbackMetricCross (L.S.base.metric s) e =
            scalarOneShrinkingCylinderMetric s (hs.trans_lt (by norm_num))) ∧
          ∀ epsilon eta : ℝ, 0 < epsilon → epsilon < 1 → 0 < eta → ∀ᶠ i in _root_.Filter.atTop,
            ∃ W : StrongNeckWitness F.S mark (x (phi i)) 0 epsilon,
              ∃ V : SpatialNeckWitness (F.S.base.metric 0) mark (x (phi i)) eta,
                (∀ z : spatialNeckBuffer epsilon, W.embedding z = Phi.map i (e (z : SpatialNeckCylinder))) ∧
                (∀ z : spatialNeckBuffer eta, V.embedding z = Phi.map i
                  (e (cylinderAxialScale (Real.sqrt 2) (by positivity) (z : SpatialNeckCylinder)))) ∧
                W.embedding '' spatialNeckCentralDomain epsilon = V.centralSphere := by
  intro hK distance
  have hnoncompact : NoncompactSpace F.M := by
    obtain ⟨e⟩ := hEuclidean
    exact e.symm.toHomeomorph.isClosedEmbedding.noncompactSpace
  obtain ⟨x, r, eps, hQ, hr, heps, hanti, hepsLimit, hdisjoint, hescape, hQr, hratio,
      hexpand, hscaled, hlocal, hterms, _hcomplete, _hconnected, _hnoncollapse, _hoperator,
      hbase, _hbackward, _heventual⟩ := ancientKappaThree_exists_ascr_normalized_sequence
    F hF (by simp [ThreeSpace]) hnoncompact p
  refine ⟨x, r, eps, hQ, hr, heps, hanti, hepsLimit, hdisjoint, hescape, hQr, hratio,
    hexpand, hscaled, hlocal, hterms, hbase, ?_⟩
  exact exists_terminalNormalized_neckWitnesses_limit_of_diffeomorph_euclidean
    F hF hEuclidean p x hQ hescape hscaled

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_exists_ascr_strongNeck_limit_of_diffeomorph_euclidean then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_exists_ascr_strongNeck_limit_of_diffeomorph_euclidean"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_exists_ascr_strongNeck_limit_of_diffeomorph_euclidean ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_exists_ascr_strongNeck_limit_of_diffeomorph_euclidean

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
