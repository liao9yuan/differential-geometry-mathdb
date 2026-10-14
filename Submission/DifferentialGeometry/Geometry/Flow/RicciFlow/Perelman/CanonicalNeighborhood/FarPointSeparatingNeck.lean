import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FarSpatialNeck
import Submission.DifferentialGeometry.Geometry.Neck.SeparatingSphere
import Submission.DifferentialGeometry.Geometry.Neck.SpatialDiameter

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private theorem hasNonnegativeSectionalCurvature_of_secLower
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] (g : SmoothRiemannianMetric I3 M)
    (h : SecLower g 0 _root_.Set.univ) : HasNonnegativeSectionalCurvature g := by
  apply (hasNonnegativeSectionalCurvature_iff g).mpr
  intro x v w
  have hvec : (fun i => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
    funext i
    fin_cases i <;> simp [vec4]
  simpa only [_root_.MulZeroClass.zero_mul, metricRm04StandardAt_apply, hvec] using h x (_root_.Set.mem_univ x) v w

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hasNonnegativeSectionalCurvature_of_secLower
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hasNonnegativeSectionalCurvature_of_secLower target :: scope.openDecls } }

theorem exists_far_point_separating_neck
    (kappa : ℝ) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ {eps sigma : ℝ} {Phi : ℝ → ℝ}, eps ≤ epsStar →
        ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
          (J : RealTimeInterval) (B : BackwardExtension L J),
          ¬ CompactSpace L.space.M → ∀ D : ℝ, 0 ≤ D →
          (∀ s ∈ J.carrier, ∀ y z : L.space.M,
            |metricDistance (B.solution.base.metric s) y z -
              metricDistance L.space.metric y z| ≤ D) →
          ∀ p : L.space.M, ∃ alpha D0 C0 : ℝ, 0 < alpha ∧ alpha < 1 / 11 ∧
            0 < D0 ∧ 0 < C0 ∧ ∀ s ∈ J.carrier, ∀ y : L.space.M,
              D0 < metricDistance L.space.metric p y →
              C0 < B.solution.scalar s y →
              ∃ (neck : SpatialNeck (B.solution.base.metric s) alpha y) (z : L.space.M),
                metricDistance L.space.metric p y < metricDistance L.space.metric p z ∧
                p ∉ neck.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ)) ∧
                z ∉ connectedComponentIn (neck.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ)))ᶜ p ∧
                ∀ v ∈ neck.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-10 : ℝ) 10),
                  ∀ w ∈ neck.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-10 : ℝ) 10),
                    metricDistance (B.solution.base.metric s) v w ≤
                      C0 / Real.sqrt (B.solution.scalar s y) := by
  obtain ⟨eta0, heta0, hseparate⟩ :=
    exists_far_spatialNeck_unbounded_separated_component_of_nonnegative.{u}
  let alpha := _root_.Min.min (eta0 / 4) (1 / 128)
  have ha : 0 < alpha := lt_min (by positivity) (by norm_num)
  have hsmall : alpha < 1 / 32 := (min_le_right _ _).trans_lt (by norm_num)
  have hatol : 2 * alpha ≤ eta0 := by
    have hh : alpha ≤ eta0 / 4 := min_le_left _ _
    linarith
  obtain ⟨epsStar, hepsStar, hneck⟩ := exists_far_spatialNeck_of_backwardExtension.{u}
    kappa ha hsmall
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps sigma pinching heps X L J B hnoncompact D hD hdist p
  let _ : ConnectedSpace L.space.M := L.connected
  let _ : NoncompactSpace L.space.M := ⟨fun h => hnoncompact (isCompact_univ_iff.mp h)⟩
  have hcomplete0 : RiemannianMetricComplete L.space.metric := ⟨L.complete.complete⟩
  have hsec0 := hasNonnegativeSectionalCurvature_of_secLower L.space.metric L.nonnegative
  obtain ⟨Rn, hRn, hcenter⟩ := hneck heps X L hnoncompact D hD p
  obtain ⟨Rs, Cs, hRs, hCs, hsep⟩ := hseparate L.space.M L.space.metric hcomplete0 hsec0 p D hD
  obtain ⟨Cd, hCd, hdiam⟩ := exists_uniform_spatial_neck_core_diameter (M := L.space.M)
  let D0 := _root_.Max.max Rn (_root_.Max.max Rs (Cd + D)) + 1
  let C0 := _root_.Max.max 4 (_root_.Max.max Cs Cd) + 1
  have hD0 : 0 < D0 := by
    have hh := le_max_left Rn (_root_.Max.max Rs (Cd + D))
    dsimp [D0]
    linarith
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  refine ⟨2 * alpha, D0, C0, by positivity, by linarith, hD0, hC0, ?_⟩
  intro s hs y hy hq
  have hyn : Rn < metricDistance L.space.metric p y := by
    have hh := le_max_left Rn (_root_.Max.max Rs (Cd + D))
    dsimp only [D0] at hy
    linarith
  have hys : Rs < metricDistance L.space.metric p y := by
    have hh := (le_max_left Rs (Cd + D)).trans (le_max_right Rn (_root_.Max.max Rs (Cd + D)))
    dsimp only [D0] at hy
    linarith
  have hyd : Cd + D < metricDistance L.space.metric p y := by
    have hh := (le_max_right Rs (Cd + D)).trans (le_max_right Rn (_root_.Max.max Rs (Cd + D)))
    dsimp only [D0] at hy
    linarith
  have hq4 : 4 < B.solution.scalar s y := by
    have hh := le_max_left (4 : ℝ) (_root_.Max.max Cs Cd)
    dsimp only [C0] at hq
    linarith
  have hqs : Cs < metricScalarAt (B.solution.base.metric s) y := by
    have hh := (le_max_left Cs Cd).trans (le_max_right (4 : ℝ) (_root_.Max.max Cs Cd))
    dsimp only [C0] at hq
    change Cs < B.solution.scalar s y
    linarith
  obtain ⟨neck⟩ := hcenter J B s hs (hdist s hs) y hyn hq4
  have hcomplete : RiemannianMetricComplete (B.solution.base.metric s) :=
    ⟨(B.complete s hs).complete⟩
  have hsec := hasNonnegativeSectionalCurvature_of_secLower
    (B.solution.base.metric s) (B.nonnegative s hs)
  obtain ⟨z, hzfar, hzcomp⟩ := hsep (B.solution.base.metric s) hcomplete hsec
    (2 * alpha) y neck hatol (hdist s hs) hys hqs (metricDistance L.space.metric p y)
  have hycore : y ∈ neck.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-10 : ℝ) 10) :=
    ⟨(neck.center, 0), ⟨mem_univ _, by norm_num⟩, neck.center_eq⟩
  have hp : p ∉ neck.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ)) := by
    intro hpin
    have hpcore : p ∈ neck.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-10 : ℝ) 10) := by
      apply _root_.Set.image_mono (_root_.Set.prod_mono (Subset.refl _) ?_) hpin
      intro t ht
      have ht0 : t = 0 := ht
      rw [ht0]
      norm_num
    have hbound := hdiam (B.solution.base.metric s) (2 * alpha) y neck p hpcore y hycore
    have hroot : 1 ≤ Real.sqrt (metricScalarAt (B.solution.base.metric s) y) :=
      Real.le_sqrt_of_sq_le (by change 1 ^ 2 ≤ B.solution.scalar s y; linarith)
    have hbound' := hbound.trans (div_le_self hCd.le hroot)
    have herr := (abs_le.mp (hdist s hs p y)).1
    linarith
  refine ⟨neck, z, hzfar, hp, hzcomp, ?_⟩
  intro v hv w hw
  have hCdC0 : Cd ≤ C0 := by
    have hh := (le_max_right Cs Cd).trans (le_max_right (4 : ℝ) (_root_.Max.max Cs Cd))
    dsimp only [C0]
    linarith
  exact (hdiam (B.solution.base.metric s) (2 * alpha) y neck v hv w hw).trans
    (div_le_div_of_nonneg_right hCdC0 (Real.sqrt_nonneg _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_far_point_separating_neck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_far_point_separating_neck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_far_point_separating_neck ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_far_point_separating_neck

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
