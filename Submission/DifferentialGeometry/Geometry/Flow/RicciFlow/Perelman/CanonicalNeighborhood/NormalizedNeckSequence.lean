import Submission.DifferentialGeometry.Geometry.Neck.FiniteEnd
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedLimitNecks

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_terminal_pointed_limit_with_missing_endpoint_and_disjoint_neck_sequence
    {kappa : ℝ} (hkappa : 0 < kappa) {A : ℝ} (hA : 0 ≤ A)
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 2000000) :
    ∃ epsStar c : ℝ, 0 < epsStar ∧ 0 < c ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ¬ BoundedAtDistance X → ∃ f : ℕ → ℕ, ∃ hf : StrictMono f,
              ∃ F : FiniteControlledRadius (X.reindex f hf), ∃ r : ℕ → ℝ,
                (∀ k, 0 < r k ∧ r k < F.radius) ∧ _root_.Filter.Tendsto r _root_.Filter.atTop (nhds F.radius) ∧
                ∃ L : PointedRiemannianManifold.{u, 0, 0} (I := I3),
                ∃ hL : PathConnectedSpace L.M,
                let _ : PathConnectedSpace L.M := hL
                ∃ maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f,
                  ∃ C : PointedRiemannianConverges (X.toFlowSequence.atTime 0) L f maps,
                  (∀ k, C.metrics.domain k = CanonicalMetricCompactness.canonicalSourceData maps k) ∧
                  (∀ k, maps.target k = riemannianBallOf ((X.term (f k)).S.base.metric 0)
                    (X.term (f k)).basepoint (r k)) ∧
                  (∀ eta : ℝ, 0 < eta → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
                    ∀ x ∈ maps.source k, ∀ v : TangentSpace I3 x,
                      (1 - eta) * L.metric.inner x v v ≤
                        ((X.term (f k)).S.base.metric 0).inner (maps.partialDiffeomorph k x)
                          (mfderiv I3 I3 (maps.partialDiffeomorph k) x v)
                          (mfderiv I3 I3 (maps.partialDiffeomorph k) x v) ∧
                      ((X.term (f k)).S.base.metric 0).inner (maps.partialDiffeomorph k x)
                          (mfderiv I3 I3 (maps.partialDiffeomorph k) x v)
                          (mfderiv I3 I3 (maps.partialDiffeomorph k) x v) ≤
                        (1 + eta) * L.metric.inner x v v) ∧
                  (∀ R : ℝ, 0 ≤ R → R < F.radius →
                    IsCompact (riemannianClosedBallOf L.metric L.basepoint R)) ∧
                  metricScalarAt L.metric L.basepoint = 1 ∧
                  (∀ (x : L.M) (v w : TangentSpace I3 x),
                    0 ≤ metricRm04StandardAt L.metric x v w w v) ∧
                    let _ : EMetricSpace L.M := L.emetricSpace
                    let _ : MetricSpace L.M := EMetricSpace.toMetricSpace
                      (fun x y => riemannianEDistOf_ne_top L.metric x y)
                    ∃ phi : ℕ → ℕ, ∃ (γ : ∀ n, ℝ → (X.term (f (phi n))).M)
                      (s : ℕ → ℝ) (g : C(_root_.Set.Ico 0 F.radius, L.M)),
                      StrictMono phi ∧ Isometry g ∧ g ⟨0, le_rfl, F.radius_pos⟩ = L.basepoint ∧
                      (∀ n,
                        let ell := metricDistance ((X.term (f (phi n))).S.base.metric 0)
                          (X.term (f (phi n))).basepoint (F.points (phi n))
                        s n ∈ _root_.Set.Ico 0 ell ∧ γ n 0 = (X.term (f (phi n))).basepoint ∧
                          γ n ell = F.points (phi n) ∧ ContMDiff 𝓘(ℝ, ℝ) I3 ∞ (γ n) ∧
                          (∀ t, IsGeodesicAt ((X.term (f (phi n))).S.base.metric 0) (γ n) t) ∧
                          (∀ t, ((X.term (f (phi n))).S.base.metric 0).inner (γ n t)
                            (mfderiv 𝓘(ℝ, ℝ) I3 (γ n) t 1)
                            (mfderiv 𝓘(ℝ, ℝ) I3 (γ n) t 1) = 1) ∧
                          (∀ t ∈ _root_.Set.Icc 0 ell, ∀ v ∈ _root_.Set.Icc 0 ell,
                            metricDistance ((X.term (f (phi n))).S.base.metric 0)
                              (γ n t) (γ n v) = |t - v|) ∧
                          (X.term (f (phi n))).S.scalar 0 (γ n (s n)) = 2 ∧
                          (∀ t ∈ _root_.Set.Ioc (s n) ell, 2 < (X.term (f (phi n))).S.scalar 0 (γ n t)) ∧
                          c < ell - s n) ∧
                      (∀ A : Set (_root_.Set.Ico 0 F.radius), IsCompact A → TendstoUniformlyOn
                        (fun n (t : _root_.Set.Ico 0 F.radius) => (maps.partialDiffeomorph (phi n)).symm (γ n t))
                        g _root_.Filter.atTop A) ∧
                      (∀ x : L.M, ¬ _root_.Filter.Tendsto g
                        (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 F.radius → ℝ) (𝓝 F.radius)) (𝓝 x)) ∧
                      _root_.Filter.Tendsto (fun t => metricScalarAt L.metric (g t))
                        (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 F.radius → ℝ) (𝓝 F.radius)) _root_.Filter.atTop ∧
                      ∃ q : UniformSpace.Completion L.M,
                        _root_.Filter.Tendsto (fun t => (g t : UniformSpace.Completion L.M))
                          (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 F.radius → ℝ) (𝓝 F.radius)) (𝓝 q) ∧
                        (∀ t : _root_.Set.Ico 0 F.radius, _root_.Dist.dist q (g t : UniformSpace.Completion L.M) =
                          F.radius - t) ∧
                        (q ∉ _root_.Set.range (fun x : L.M => (x : UniformSpace.Completion L.M))) ∧
                        (∀ t : _root_.Set.Ico 0 F.radius, 2 < metricScalarAt L.metric (g t) →
                          A ^ 2 ≤ metricScalarAt L.metric (g t) *
                            _root_.Dist.dist q (g t : UniformSpace.Completion L.M) ^ 2) ∧
                        (∀ᶠ (tau : _root_.Set.Ico 0 F.radius) in
                          _root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 F.radius → ℝ) (𝓝 F.radius),
                          Nonempty (SpatialNeck L.metric (2 * alpha) (g tau))) ∧
                        ∃ t : ℕ → _root_.Set.Ico 0 F.radius,
                          ∃ nk : ∀ n, SpatialNeck L.metric (2 * alpha) (g (t n)),
                            StrictMono (fun n => (t n : ℝ)) ∧
                            _root_.Filter.Tendsto (fun n => (t n : ℝ)) _root_.Filter.atTop (𝓝 F.radius) ∧
                            (∀ n, (t (n + 1) : ℝ) - t n =
                              ((2 * alpha)⁻¹ / 40) /
                                Real.sqrt (metricScalarAt L.metric (g (t n)))) ∧
                            (∀ n, ∃ (eta : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2)
                              (height : Sphere 2 → ℝ), ContMDiff I2 𝓘(ℝ, ℝ) ∞ height ∧
                              (∀ p, height p ∈ _root_.Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹) ∧
                              ∀ p, (nk n).map (p, height p) = (nk (n + 1)).map (eta p, 0)) ∧
                            Pairwise (fun i j =>
                              Disjoint ((nk i).map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ)))
                                ((nk j).map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ)))) ∧
                            LocallyFinite (fun n =>
                              (nk n).map '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹)) ∧
                            ∃ eta : ℕ → Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2,
                              ∃ Ψ : ℕ → PartialDiffeomorph IC I3 Cylinder L.M ∞,
                                (∀ n, (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ (Ψ n).source) ∧
                                  (∀ p, Ψ n (p, 0) = (nk n).map (p, 0)) ∧
                                  (∀ p, Ψ n (p, 1) = (nk (n + 1)).map (eta n p, 0)) ∧
                                  IsCompact (Ψ n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∧
                                  (frontier (Ψ n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) =
                                    (nk n).map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ)) ∪
                                      (nk (n + 1)).map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ))) ∧
                                  (Ψ n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆
                                    (nk n).map '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹)) ∧
                                  Ψ n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆
                                    riemannianClosedBallOf L.metric (g (t n))
                                      ((3 * (2 * alpha)⁻¹ / 100) /
                                        Real.sqrt (metricScalarAt L.metric (g (t n)))) ∩
                                    riemannianClosedBallOf L.metric (g (t (n + 1)))
                                      ((3 * (2 * alpha)⁻¹ / 100) /
                                        Real.sqrt (metricScalarAt L.metric (g (t n))))) ∧
                                (∀ i j, i + 1 < j →
                                  Disjoint (Ψ i '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1))
                                    (Ψ j '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1))) ∧
                                Pairwise (fun i j =>
                                  Disjoint (interior (Ψ (i + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)))
                                    (interior (Ψ (j + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)))) ∧
                                (∀ n, (Ψ (n + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∩
                                  (Ψ (n + 2) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) =
                                    (nk (n + 2)).map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ))) ∧
                                (∀ n, (nk (n + 2)).map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ)) ⊆
                                  interior ((Ψ (n + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∪
                                    (Ψ (n + 2) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)))) ∧
                                LocallyFinite (fun n => Ψ n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∧
                                IsClosed (⋃ n, Ψ n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∧
                                IsConnected (⋃ n, Ψ n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∧
                                ¬ IsCompact (⋃ n, Ψ n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∧
                                (frontier (⋃ n, Ψ n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ⊆
                                  ⋃ n, (nk n).map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ))) ∧
                                IsClosed (⋃ n, Ψ (n + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∧
                                IsConnected (⋃ n, Ψ (n + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∧
                                ¬ IsCompact (⋃ n, Ψ (n + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∧
                                (frontier (⋃ n, Ψ (n + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) =
                                  (nk 1).map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ))) ∧
                                (∀ v : _root_.Set.Ico 0 F.radius, (t 2 : ℝ) ≤ v →
                                  g v ∈ interior (⋃ n, Ψ (n + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1))) ∧
                                (∀ n (x : L.M), x ∈ Ψ n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) →
                                  _root_.Dist.dist q (x : UniformSpace.Completion L.M) ≤
                                    (11 / 5) * (F.radius - (t n : ℝ))) ∧
                                (∀ n (x : L.M), x ∈ Ψ n '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) →
                                  ((2 * alpha)⁻¹) ^ 2 / 8 ≤ metricScalarAt L.metric x *
                                    _root_.Dist.dist q (x : UniformSpace.Completion L.M) ^ 2) ∧
                                (∀ᶠ n in _root_.Filter.atTop,
                                  (nk n).map '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹) ⊆
                                    interior (⋃ n, Ψ (n + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1))) ∧
                                ∃ E : Sphere 2 × _root_.Set.Ici (0 : ℝ) ≃ₜ
                                  (⋃ n, Ψ (n + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)),
                                  ∃ theta : ℕ → Sphere 2 ≃ₜ Sphere 2,
                                    theta 0 = Homeomorph.refl (Sphere 2) ∧
                                    (∀ n, theta (n + 1) =
                                      (theta n).trans (eta (n + 1)).toHomeomorph) ∧
                                    (∀ (n : ℕ) (p : Sphere 2) (s : _root_.Set.Icc (0 : ℝ) 1),
                                      (E (p, ⟨n + (s : ℝ),
                                        add_nonneg (Nat.cast_nonneg n) s.property.1⟩) : L.M) =
                                          Ψ (n + 1) (theta n p, s)) ∧
                                    (∀ s : _root_.Set.Ici (0 : ℝ), Nonempty
                                      (DifferentialGeometry.Topology.SmoothTwoSidedCollar I2 I3
                                        (fun p : Sphere 2 => (E (p, s) : L.M)))) ∧
                                    ∃ D : Sphere 2 × _root_.Set.Ioi (0 : ℝ) ≃ₜ
                                      interior (⋃ n, Ψ (n + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)),
                                      (∀ (p : Sphere 2) (s : _root_.Set.Ioi (0 : ℝ)),
                                        (D (p, s) : L.M) =
                                          (E (p, Set.inclusion _root_.Set.Ioi_subset_Ici_self s) : L.M)) ∧
                                      let W : TopologicalSpace.Opens L.M :=
                                        ⟨interior (⋃ n, Ψ (n + 1) '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)),
                                          isOpen_interior⟩
                                      ∃ gW : C(_root_.Set.Ico (t 2 : ℝ) F.radius, W),
                                        (∀ v : _root_.Set.Ico (t 2 : ℝ) F.radius, (gW v : L.M) =
                                          g ⟨v, (t 2).property.1.trans v.property.1, v.property.2⟩) ∧
                                        (∀ v w : _root_.Set.Ico (t 2 : ℝ) F.radius,
                                          riemannianEDistOf (L.metric.restrictOpen W) (gW v) (gW w) =
                                            _root_.EDist.edist v w) ∧
                                        (∀ᶠ n in _root_.Filter.atTop, ∃ hn : (t 2 : ℝ) ≤ t n,
                                          ∃ nkW : SpatialNeck (L.metric.restrictOpen W) (2 * alpha)
                                            (gW ⟨t n, hn, (t n).property.2⟩),
                                            nkW.map.source = (nk n).map.source ∩
                                              (nk n).map ⁻¹' (W : Set L.M) ∧
                                            (∀ y ∈ _root_.Set.univ ×ˢ _root_.Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹,
                                              (nkW.map y : L.M) = (nk n).map y) ∧
                                            ∀ y : W, nkW.map.symm y = (nk n).map.symm (y : L.M)) ∧
                                        ∃ hW : PathConnectedSpace W,
                                          let _ : PathConnectedSpace W := hW
                                          let mW : MetricSpace W :=
                                            let _ : PseudoMetricSpace W :=
                                              (L.metric.restrictOpen W).toPseudoMetricSpace
                                            MetricSpace.ofT0PseudoMetricSpace W
                                          let _ : PseudoMetricSpace W := mW.toPseudoMetricSpace
                                          let _ : UniformSpace W := mW.toPseudoMetricSpace.toUniformSpace
                                          let eW : PseudoEMetricSpace W :=
                                            @PseudoMetricSpace.toPseudoEMetricSpace W mW.toPseudoMetricSpace
                                          let _ : WeakPseudoEMetricSpace W :=
                                            @PseudoEMetricSpace.toWeakPseudoEMetricSpace W eW
                                          ∃ qW : UniformSpace.Completion W,
                                            _root_.Filter.Tendsto (fun v => (gW v : UniformSpace.Completion W))
                                              (_root_.Filter.comap (Subtype.val : _root_.Set.Ico (t 2 : ℝ) F.radius → ℝ)
                                                (𝓝 F.radius)) (𝓝 qW) ∧
                                            (∀ v : _root_.Set.Ico (t 2 : ℝ) F.radius,
                                              _root_.Dist.dist qW (gW v : UniformSpace.Completion W) = F.radius - v) ∧
                                            qW ∉ _root_.Set.range (fun x : W => (x : UniformSpace.Completion W)) ∧
                                            UniformSpace.Completion.map (Subtype.val : W → L.M) qW = q ∧
                                            Topology.IsOpenEmbedding
                                              (fun x : W => (x : UniformSpace.Completion W)) ∧
                                            (∀ U ∈ 𝓝 qW, ∀ᶠ n in _root_.Filter.atTop,
                                              (fun x : W => (x : UniformSpace.Completion W)) ''
                                                {x : W | (x : L.M) ∈ Ψ (n + 2) ''
                                                  (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)} ⊆ U) ∧
                                            IsCompact (_root_.Insert.insert qW (⋃ n,
                                              (fun x : W => (x : UniformSpace.Completion W)) ''
                                                {x : W | (x : L.M) ∈ Ψ (n + 2) ''
                                                  (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)})) ∧
                                            _root_.Insert.insert qW (⋃ n,
                                              (fun x : W => (x : UniformSpace.Completion W)) ''
                                                {x : W | (x : L.M) ∈ Ψ (n + 2) ''
                                                  (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)}) ∈ 𝓝 qW ∧
                                            _root_.Filter.Tendsto (fun x : W => metricScalarAt (L.metric.restrictOpen W) x)
                                              (_root_.Filter.comap (fun x : W => (x : UniformSpace.Completion W))
                                                (𝓝 qW)) _root_.Filter.atTop ∧
                                            (∀ n (x : W), (x : L.M) ∈ Ψ (n + 2) ''
                                              (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) →
                                              ((2 * alpha)⁻¹) ^ 2 / 8 ≤
                                                metricScalarAt (L.metric.restrictOpen W) x *
                                                  _root_.Dist.dist qW (x : UniformSpace.Completion W) ^ 2) ∧
                                            (∀ (β : ℝ → UniformSpace.Completion W) (u v w : ℝ),
                                              u < v → v < w →
                                              (∀ s ∈ _root_.Set.Icc u w, ∀ t ∈ _root_.Set.Icc u w,
                                                _root_.Dist.dist (β s) (β t) = |s - t|) → β v ≠ qW) ∧
                                            (∃ C : ℝ, 0 < C ∧ ∀ᶠ n in _root_.Filter.atTop,
                                              metricScalarAt L.metric (g (t (n + 2))) *
                                                (F.radius - (t (n + 2) : ℝ)) ^ 2 ≤ C) ∧
                                            ∃ delta : ℝ, 0 < delta ∧
                                              IsCompact (Metric.closedBall qW delta) ∧
                                              Metric.closedBall qW delta ⊆ _root_.Insert.insert qW
                                                (_root_.Set.range (fun x : W => (x : UniformSpace.Completion W))) ∧
                                                Nonempty (DifferentialGeometry.Toponogov.PuncturedConeApproximation qW delta) ∧
                                                (∀ eps > 0, ∃ d ∈ _root_.Set.Ioo 0 (delta / 3), ∃ A : Finset C(ℝ, UniformSpace.Completion W),
                                                  (∀ ray ∈ A, ray 0 = qW ∧
                                                    ∀ s ∈ _root_.Set.Icc 0 d, ∀ t ∈ _root_.Set.Icc 0 d, _root_.Dist.dist (ray s) (ray t) = |s - t|) ∧
                                                  ∀ s ∈ _root_.Set.Ioc 0 d, ∀ x : W, _root_.Dist.dist (x : UniformSpace.Completion W) qW = s →
                                                    ∃ ray ∈ A, _root_.Dist.dist (x : UniformSpace.Completion W) (ray s) < eps * s) ∧
                                                ∀ {ι : Type u} (len : ι → ℝ) (ray : ι → C(ℝ, UniformSpace.Completion W)),
                                                  (∀ i, 0 < len i) → (∀ i, len i < delta / 3) → (∀ i, ray i 0 = qW) →
                                                  (∀ i, ∀ s ∈ _root_.Set.Icc 0 (len i), ∀ t ∈ _root_.Set.Icc 0 (len i),
                                                    _root_.Dist.dist (ray i s) (ray i t) = |s - t|) →
                                                  ∃ K : DifferentialGeometry.Toponogov.AngleKernel ι,
                                                    (∀ i j, K.angle i j = DifferentialGeometry.Toponogov.limitingRadialAngle
                                                      len (fun i => ray i) i j) ∧
                                                    let _ := K.metricSpace
                                                    TotallyBounded (_root_.Set.univ : Set (Quotient K.setoid)) ∧
                                                      CompactSpace (UniformSpace.Completion (Quotient K.setoid)) := by
  obtain ⟨epsStar, c, hepsStar, hc, hproduce⟩ :=
    exists_terminal_pointed_limit_with_missing_endpoint_and_spatialNecks.{u}
      hkappa (A := A) hA (alpha := alpha / 2) (by positivity) (by linarith only [hsmall])
  refine ⟨epsStar, c, hepsStar, hc, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X hnot
  obtain ⟨f, hf, F, r, hr, hrT, L, hL, maps, C, hcanonical, htargets, hmetrics,
    hcompact, hbase, hsec, phi, γ, s, g, hphi, hg, hgbase, hγ, hconv, hno, hblow,
    q, hq, hdist, hmissing, hquant, hnecks⟩ :=
      hproduce eps heps hle sigma hsigma Phi hPhi X hnot
  clear hproduce
  let _ : PathConnectedSpace L.M := hL
  let _ : EMetricSpace L.M := L.emetricSpace
  let _ : MetricSpace L.M := EMetricSpace.toMetricSpace
    (fun x y => riemannianEDistOf_ne_top L.metric x y)
  have hnecks' : ∀ᶠ tau : _root_.Set.Ico 0 F.radius in
      _root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 F.radius → ℝ) (𝓝 F.radius),
      Nonempty (SpatialNeck L.metric alpha (g tau)) := by
    simpa only [mul_div_cancel₀ alpha (by norm_num : (2 : ℝ) ≠ 0)] using hnecks
  have hnecksWide : ∀ᶠ tau : _root_.Set.Ico 0 F.radius in
      _root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 F.radius → ℝ) (𝓝 F.radius),
      Nonempty (SpatialNeck L.metric (2 * alpha) (g tau)) :=
    hnecks'.mono fun _ hn => hn.map
      (fun nk => nk.mono (by linarith only [ha]) (by linarith only [hsmall]))
  refine ⟨f, hf, F, r, hr, hrT, L, hL, maps, C, hcanonical, htargets, hmetrics,
    hcompact, hbase, hsec, ?_⟩
  refine ⟨phi, γ, s, g, hphi, hg, hgbase, hγ, hconv, hno, hblow, q, hq, hdist, hmissing,
    hquant, hnecksWide, ?_⟩
  exact exists_spatialNeck_sequence_with_punctured_completion L.metric (fun _ _ => rfl) F.radius_pos ha hsmall
    hsec g hg hblow q hq hnecks'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminal_pointed_limit_with_missing_endpoint_and_disjoint_neck_sequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminal_pointed_limit_with_missing_endpoint_and_disjoint_neck_sequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminal_pointed_limit_with_missing_endpoint_and_disjoint_neck_sequence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminal_pointed_limit_with_missing_endpoint_and_disjoint_neck_sequence


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
