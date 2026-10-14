import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedNeckCoordinates
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedArmCylinderLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedArmConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedOrientation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SeparatedRayCylinderBranch
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientKappaFixedCompactness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderNecks
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckArmCrossing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Comparison.Toponogov
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem exists_windowed_tolerances_for_original_arm_neck_positions :
    ∃ delta : ℕ → ℝ, (∀ i, 0 < delta i) ∧ _root_.Filter.Tendsto delta _root_.Filter.atTop (𝓝 0) ∧
      ∀ (M : ℕ → Type u) [∀ i, TopologicalSpace (M i)]
        [∀ i, ChartedSpace ThreeSpace (M i)] [∀ i, IsManifold I3 ∞ (M i)]
        [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]
        (D : ℕ → RealTimeInterval) (S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)),
        (∀ i, IsSolutionOn (S i)) →
        (∀ i, TangentOrientationSection (M i)) → ∀ (kappa : ℝ)
          (x : ∀ i, M i) (t eps : ℕ → ℝ)
          (W : ∀ i, WindowedModelWitness (eps i) kappa (S i) (x i) (t i)),
          (∀ i, eps i ≤ delta i) →
          (∀ i, _root_.Set.Ioo (t i - (eps i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular) →
          ∀ (arms : ∀ i, Fin 2 → MinimizingArm ((S i).base.metric (t i)) (x i))
            (ell : ℕ → Fin 2 → ℝ),
            (∀ i j, ell i j ∈ _root_.Set.Ioc 0 (arms i j).length) →
            (∀ (i : ℕ) j, Real.sqrt ((S i).scalar (t i) (x i)) * ell i j ∈
              _root_.Set.Icc ((i : ℝ) + 1) (2 * ((i : ℝ) + 1))) →
            ∀ theta : ℝ, 0 < theta →
              (∀ᶠ i in _root_.Filter.atTop, theta ≤ comparisonAngle (ell i 0) (ell i 1)
                (metricDistance ((S i).base.metric (t i))
                  ((arms i 0).point (ell i 0)) ((arms i 1).point (ell i 1)))) →
              ∀ alpha : ℝ, 0 < alpha → 2 * alpha < 1 / 11 → ∀ H : ℝ,
                ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ r : ℝ≥0, 0 < r ∧ ∃ᶠ i in _root_.Filter.atTop,
                  ∃ (modelMap : PartialDiffeomorph IC I3 Cylinder (W (phi i)).model.M ∞)
                    (nk : StrongNeck (S (phi i)) (2 * alpha) (x (phi i)) (t (phi i))),
                    nk.map = partialDiffeomorphTransMixed modelMap (W (phi i)).embedding ∧
                    (∀ j : Fin 2, (r : ℝ) / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i))) ∈
                      _root_.Set.Ioo 0 (arms (phi i) j).length) ∧
                    (∀ j : Fin 2, ∀ s ∈ _root_.Set.Icc 0 ((r : ℝ) / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i)))),
                      (arms (phi i) j).point s ∈ nk.map.target) ∧
                    (((nk.map.symm ((arms (phi i) 0).point
                        ((r : ℝ) / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i)))))).2 < -H ∧
                      H < (nk.map.symm ((arms (phi i) 1).point
                        ((r : ℝ) / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i)))))).2) ∨
                    ((nk.map.symm ((arms (phi i) 1).point
                        ((r : ℝ) / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i)))))).2 < -H ∧
                      H < (nk.map.symm ((arms (phi i) 0).point
                        ((r : ℝ) / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i)))))).2)) := by
  obtain ⟨delta, hdelta, hzero, hlimit⟩ := exists_windowed_tolerances_for_original_arm_cylinder_limit.{u}
  refine ⟨delta, hdelta, hzero, ?_⟩
  intro M _ _ _ _ _ D S hS o kappa x t eps W heps hregular arms ell hell hlength theta htheta hangle alpha halpha hsmall H
  obtain ⟨L, phi, hphi, hL, _hbase, F, hcmp, p, e, hmark, hmetric, hnecks,
      rays, hcluster, hraybase, hraymetric, hrayangle⟩ :=
    hlimit M D S hS o kappa x t eps W heps hregular arms ell hell hlength theta htheta hangle
  let _ : ConnectedSpace L.M := hL.connected
  have hcomplete : MetricComplete (L.atTime 0) := hL.complete 0 (by simp)
  have hepsZero : _root_.Filter.Tendsto eps _root_.Filter.atTop (𝓝 0) := squeeze_zero (fun i => (W i).eps_pos.le) heps hzero
  have hlong : ∀ j, _root_.Filter.Tendsto (fun i => Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i))) *
      (arms (phi i) j).length) _root_.Filter.atTop atTop := by
    intro j
    have hnat : _root_.Filter.Tendsto (fun i : ℕ => (i : ℝ) + 1) _root_.Filter.atTop atTop :=
      _root_.Filter.tendsto_atTop_mono (fun i : ℕ => le_add_of_nonneg_right zero_le_one) tendsto_natCast_atTop_atTop
    have hl : ∀ i : ℕ, (i : ℝ) + 1 ≤ Real.sqrt ((S i).scalar (t i) (x i)) * (arms i j).length :=
      fun i => (hlength i j).1.trans (mul_le_mul_of_nonneg_left (hell i j).2 (Real.sqrt_nonneg _))
    exact (_root_.Filter.tendsto_atTop_mono hl hnat).comp hphi.tendsto_atTop
  have hradial (j : Fin 2) (r : ℝ≥0) :
      metricDistance (L.S.base.metric 0) L.basepoint (rays (j, r)) = r := by
    rw [← hraybase j]
    simpa only [NNReal.coe_zero, zero_sub, abs_neg, abs_of_nonneg r.coe_nonneg] using hraymetric j 0 r
  obtain ⟨r, hr, hpositions⟩ := exists_frequently_original_arm_opposite_neck_coordinates
    hS W hepsZero hregular L hcomplete hphi.tendsto_atTop F hcmp (fun i => arms (phi i))
    hlong e p hmark (hmetric 0 le_rfl) hnecks rays hradial hcluster
    (div_pos htheta (by norm_num : (0 : ℝ) < 4)) hrayangle halpha hsmall H
  refine ⟨phi, hphi, r, hr, hpositions.mono ?_⟩
  intro i hi
  obtain ⟨nk, hmap, hmem, htarget, hsides⟩ := hi
  refine ⟨partialDiffeomorphTransMixed e.toPartialDiffeomorph (F.partialDiffeomorph i),
    nk, ?_, hmem, htarget, hsides⟩
  rw [hmap]
  apply (show Function.Injective (fun f : PartialDiffeomorph IC I3 Cylinder (M (phi i)) ∞ =>
      f.toPartialEquiv) from by
    intro f g h
    cases f
    cases g
    cases h
    rfl)
  exact (PartialEquiv.trans_assoc e.toPartialDiffeomorph.toPartialEquiv
    (F.partialDiffeomorph i).toPartialEquiv (W (phi i)).embedding.toPartialEquiv).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_windowed_tolerances_for_original_arm_neck_positions then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_windowed_tolerances_for_original_arm_neck_positions"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_windowed_tolerances_for_original_arm_neck_positions ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_windowed_tolerances_for_original_arm_neck_positions

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end

end

section
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Comparison.Toponogov
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem exists_windowed_tolerances_for_original_arm_opposite_slices :
    ∃ delta : ℕ → ℝ, (∀ i, 0 < delta i) ∧ _root_.Filter.Tendsto delta _root_.Filter.atTop (𝓝 0) ∧
      ∀ (M : ℕ → Type u) [∀ i, TopologicalSpace (M i)]
        [∀ i, ChartedSpace ThreeSpace (M i)] [∀ i, IsManifold I3 ∞ (M i)]
        [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]
        (D : ℕ → RealTimeInterval) (S : ∀ i, SolutionOn (I := I3) (M := M i) (D i)),
        (∀ i, IsSolutionOn (S i)) →
        (∀ i, TangentOrientationSection (M i)) → ∀ (kappa : ℝ)
          (x : ∀ i, M i) (t eps : ℕ → ℝ)
          (W : ∀ i, WindowedModelWitness (eps i) kappa (S i) (x i) (t i)),
          (∀ i, eps i ≤ delta i) →
          (∀ i, _root_.Set.Ioo (t i - (eps i * (S i).scalar (t i) (x i))⁻¹) (t i) ⊆ (D i).regular) →
          ∀ (arms : ∀ i, Fin 2 → MinimizingArm ((S i).base.metric (t i)) (x i))
            (ell : ℕ → Fin 2 → ℝ),
            (∀ i j, ell i j ∈ _root_.Set.Ioc 0 (arms i j).length) →
            (∀ (i : ℕ) j, Real.sqrt ((S i).scalar (t i) (x i)) * ell i j ∈
              _root_.Set.Icc ((i : ℝ) + 1) (2 * ((i : ℝ) + 1))) →
            ∀ theta : ℝ, 0 < theta →
              (∀ᶠ i in _root_.Filter.atTop, theta ≤ comparisonAngle (ell i 0) (ell i 1)
                (metricDistance ((S i).base.metric (t i))
                  ((arms i 0).point (ell i 0)) ((arms i 1).point (ell i 1)))) →
              ∀ alpha : ℝ, 0 < alpha → 2 * alpha < 1 / 11 → ∀ H : ℝ, 0 < H →
                ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ r : ℝ≥0, 0 < r ∧ ∃ᶠ i in _root_.Filter.atTop,
                  ∃ (modelMap : PartialDiffeomorph IC I3 Cylinder (W (phi i)).model.M ∞)
                    (nk : StrongNeck (S (phi i)) (2 * alpha) (x (phi i)) (t (phi i))),
                    nk.map = partialDiffeomorphTransMixed modelMap (W (phi i)).embedding ∧
                    (∀ j : Fin 2, (r : ℝ) / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i))) ∈
                      _root_.Set.Ioo 0 (arms (phi i) j).length) ∧
                    (∀ j : Fin 2, ∀ s ∈ _root_.Set.Icc 0 ((r : ℝ) / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i)))),
                      (arms (phi i) j).point s ∈ nk.map.target) ∧
                    ∃ sa sb : ℝ, sa ∈ _root_.Set.Ioc 0 ((r : ℝ) / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i)))) ∧
                      sb ∈ _root_.Set.Ioc 0 ((r : ℝ) / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i)))) ∧
                      ∃ pa pb : Sphere 2,
                        (((arms (phi i) 0).point sa = nk.map (pa, -H) ∧
                          (arms (phi i) 1).point sb = nk.map (pb, H)) ∨
                        ((arms (phi i) 0).point sa = nk.map (pa, H) ∧
                          (arms (phi i) 1).point sb = nk.map (pb, -H))) := by
  obtain ⟨delta, hdelta, hzero, hpositions⟩ := exists_windowed_tolerances_for_original_arm_neck_positions.{u}
  refine ⟨delta, hdelta, hzero, ?_⟩
  intro M _ _ _ _ _ D S hS o kappa x t eps W heps hregular arms ell hell hlength theta htheta hangle alpha halpha hsmall H hH
  obtain ⟨phi, hphi, r, hr, hfreq⟩ := hpositions M D S hS o kappa x t eps W heps hregular
    arms ell hell hlength theta htheta hangle alpha halpha hsmall H
  refine ⟨phi, hphi, r, hr, hfreq.mono ?_⟩
  intro i hi
  obtain ⟨modelMap, nk, hmap, hmem, htarget, hsides⟩ := hi
  have hcross (j : Fin 2) (h : ℝ) (hh : h ≠ 0)
      (hbetween : h ∈ _root_.Set.uIcc 0
        (nk.map.symm ((arms (phi i) j).point
          ((r : ℝ) / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i)))))).2) :
      ∃ s' ∈ _root_.Set.Ioc 0 ((r : ℝ) / Real.sqrt ((S (phi i)).scalar (t (phi i)) (x (phi i)))),
        ∃ p : Sphere 2, (arms (phi i) j).point s' = nk.map (p, h) :=
    nk.exists_arm_slice_crossing (arms (phi i) j) ⟨(hmem j).1, (hmem j).2.le⟩
      hh (htarget j) hbetween
  refine ⟨modelMap, nk, hmap, hmem, htarget, ?_⟩
  rcases hsides with hsides | hsides
  · obtain ⟨sa, hsa, pa, hpa⟩ := hcross 0 (-H) (neg_ne_zero.mpr hH.ne') (by
      rw [_root_.Set.uIcc_of_ge (by linarith [hsides.1])]
      exact ⟨hsides.1.le, by linarith⟩)
    obtain ⟨sb, hsb, pb, hpb⟩ := hcross 1 H hH.ne' (by
      rw [_root_.Set.uIcc_of_le (by linarith [hsides.2])]
      exact ⟨hH.le, hsides.2.le⟩)
    exact ⟨sa, sb, hsa, hsb, pa, pb, Or.inl ⟨hpa, hpb⟩⟩
  · obtain ⟨sa, hsa, pa, hpa⟩ := hcross 0 H hH.ne' (by
      rw [_root_.Set.uIcc_of_le (by linarith [hsides.2])]
      exact ⟨hH.le, hsides.2.le⟩)
    obtain ⟨sb, hsb, pb, hpb⟩ := hcross 1 (-H) (neg_ne_zero.mpr hH.ne') (by
      rw [_root_.Set.uIcc_of_ge (by linarith [hsides.1])]
      exact ⟨hsides.1.le, by linarith⟩)
    exact ⟨sa, sb, hsa, hsb, pa, pb, Or.inr ⟨hpa, hpb⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_windowed_tolerances_for_original_arm_opposite_slices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_windowed_tolerances_for_original_arm_opposite_slices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_windowed_tolerances_for_original_arm_opposite_slices ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_windowed_tolerances_for_original_arm_opposite_slices

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end

end
