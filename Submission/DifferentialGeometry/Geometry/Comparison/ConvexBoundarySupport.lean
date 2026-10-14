import Submission.DifferentialGeometry.Geometry.Comparison.ConvexStratum
import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.CompleteHinge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow
open _root_.Submission.DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem riemannian_toReal_eq_dist (p q : M) :
    (_root_.Manifold.riemannianEDist I p q).toReal = _root_.Dist.dist p q := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist, ENNReal.toReal_ofReal dist_nonneg]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.riemannian_toReal_eq_dist
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.riemannian_toReal_eq_dist target :: scope.openDecls } }

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
theorem intrinsicGeodesic_neg (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (p : M) (v : TangentSpace I p) (s : ℝ) :
    intrinsicGeodesic (I := I) g hEnorm p (-v) s =
      intrinsicGeodesic (I := I) g hEnorm p v (-s) := by
  rw [← neg_one_smul ℝ v, intrinsicGeo_smul_apply (I := I) g hEnorm p v (-1) s]
  congr 1
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.intrinsicGeodesic_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.intrinsicGeodesic_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.intrinsicGeodesic_neg ``Submission.DifferentialGeometry.Geometry.Topology.intrinsicGeodesic_neg

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
theorem expMapIntrinsic_smul_eq_intrinsicGeodesic (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (p : M) (v : TangentSpace I p) (s : ℝ) :
    expMapIntrinsic (I := I) g hEnorm p (s • v) =
      intrinsicGeodesic (I := I) g hEnorm p v s :=
  intrinsicGeodesic_smul (I := I) g hEnorm p v s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.expMapIntrinsic_smul_eq_intrinsicGeodesic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.expMapIntrinsic_smul_eq_intrinsicGeodesic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.expMapIntrinsic_smul_eq_intrinsicGeodesic ``Submission.DifferentialGeometry.Geometry.Topology.expMapIntrinsic_smul_eq_intrinsicGeodesic

def IsInnerDirection (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (C : Set M) (p : M) (v : TangentSpace I p) : Prop :=
  ∀ᶠ s in 𝓝[>] (0 : ℝ), expMapIntrinsic (I := I) g hEnorm p (s • v) ∈ maxSliceLocus I C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.IsInnerDirection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.IsInnerDirection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.IsInnerDirection ``Submission.DifferentialGeometry.Geometry.Topology.IsInnerDirection

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
theorem isInnerDirection_iff {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) g} {C : Set M} {p : M} {v : TangentSpace I p} :
    IsInnerDirection (I := I) g hEnorm C p v ↔
      ∀ᶠ s in 𝓝[>] (0 : ℝ),
        intrinsicGeodesic (I := I) g hEnorm p v s ∈ maxSliceLocus I C := by
  simp only [IsInnerDirection, expMapIntrinsic_smul_eq_intrinsicGeodesic]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.isInnerDirection_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.isInnerDirection_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.isInnerDirection_iff ``Submission.DifferentialGeometry.Geometry.Topology.isInnerDirection_iff



theorem exists_nearest_relBoundary
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCcomp : IsCompact C)
    (hne : (relBoundary I C).Nonempty) (q : M) :
    ∃ z ∈ relBoundary I C, _root_.Dist.dist q z = Metric.infDist q (relBoundary I C) := by
  have hclosed : IsClosed (relBoundary I C) := isClosed_relBoundary hEnorm hC hCcomp.isClosed
  have hcomp : IsCompact (relBoundary I C) :=
    hCcomp.of_isClosed_subset hclosed relBoundary_subset
  obtain ⟨z, hz, hdist⟩ := hcomp.exists_infDist_eq_dist hne q
  exact ⟨z, hz, hdist.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.exists_nearest_relBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.exists_nearest_relBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.exists_nearest_relBoundary ``Submission.DifferentialGeometry.Geometry.Topology.exists_nearest_relBoundary

theorem infDist_relBoundary_pos
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    (hne : (relBoundary I C).Nonempty) {q : M} (hq : q ∈ maxSliceLocus I C) :
    0 < Metric.infDist q (relBoundary I C) :=
  ((isClosed_relBoundary hEnorm hC hCclosed).notMem_iff_infDist_pos hne).1
    (not_mem_relBoundary_of_mem_maxSliceLocus hq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.infDist_relBoundary_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.infDist_relBoundary_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.infDist_relBoundary_pos ``Submission.DifferentialGeometry.Geometry.Topology.infDist_relBoundary_pos

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
theorem ball_inter_subset_maxSliceLocus {C : Set M} (x : M) {ρ : ℝ}
    (hρ : ρ ≤ Metric.infDist x (relBoundary I C)) :
    Metric.ball x ρ ∩ C ⊆ maxSliceLocus I C := by
  rintro y ⟨hyb, hyC⟩
  by_contra hyN
  have hle : Metric.infDist x (relBoundary I C) ≤ _root_.Dist.dist x y :=
    Metric.infDist_le_dist_of_mem ⟨hyC, hyN⟩
  have hlt : _root_.Dist.dist x y < ρ := by
    rw [dist_comm]
    exact hyb
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.ball_inter_subset_maxSliceLocus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.ball_inter_subset_maxSliceLocus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.ball_inter_subset_maxSliceLocus ``Submission.DifferentialGeometry.Geometry.Topology.ball_inter_subset_maxSliceLocus



omit [T2Space (TangentBundle I M)] in
theorem eventually_mem_maxSliceLocus_of_inner_pos
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C : Set M} {p q : M} {l : ℝ} (hl : 0 < l)
    {u v : TangentSpace I p} (hu : g.inner p u u = 1) (hv : g.inner p v v = 1)
    (hq : intrinsicGeodesic (I := I) g hEnorm p u l = q) (hpq : _root_.Dist.dist p q = l)
    (hdist : l ≤ Metric.infDist q (relBoundary I C))
    (huv : 0 < g.inner p u v)
    (hCmem : ∀ᶠ s in 𝓝[>] (0 : ℝ), intrinsicGeodesic (I := I) g hEnorm p v s ∈ C) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      intrinsicGeodesic (I := I) g hEnorm p v s ∈ maxSliceLocus I C := by
  have hmin : (_root_.Manifold.riemannianEDist I p (intrinsicGeodesic (I := I) g hEnorm p u l)).toReal = l := by
    rw [riemannian_toReal_eq_dist (I := I), hq, hpq]
  have hthr : (0 : ℝ) < 2 * l * g.inner p u v := by positivity
  filter_upwards [hCmem, self_mem_nhdsWithin, Ioo_mem_nhdsGT hthr] with b hbC hb0 hbsmall
  have hb : (0 : ℝ) < b := hb0
  have hhinge := complete_hinge_sq (I := I) g hEnorm hsec p u v l b hl hb hu hv hmin
  rw [riemannian_toReal_eq_dist (I := I), hq] at hhinge
  have hdnn : (0 : ℝ) ≤ _root_.Dist.dist q (intrinsicGeodesic (I := I) g hEnorm p v b) := dist_nonneg
  have hsq : _root_.Dist.dist q (intrinsicGeodesic (I := I) g hEnorm p v b) ^ 2 < l ^ 2 := by
    nlinarith [mul_pos hb (sub_pos.2 hbsmall.2)]
  have hlt : _root_.Dist.dist q (intrinsicGeodesic (I := I) g hEnorm p v b) < l := by
    nlinarith [hsq, hdnn, hl]
  refine ball_inter_subset_maxSliceLocus q hdist ⟨?_, hbC⟩
  rw [Metric.mem_ball, dist_comm]
  exact hlt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.eventually_mem_maxSliceLocus_of_inner_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.eventually_mem_maxSliceLocus_of_inner_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.eventually_mem_maxSliceLocus_of_inner_pos ``Submission.DifferentialGeometry.Geometry.Topology.eventually_mem_maxSliceLocus_of_inner_pos



theorem eventually_not_mem_maxSliceLocus_of_back
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    {p : M} (hp : p ∈ relBoundary I C) {v : TangentSpace I p}
    (hback : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      intrinsicGeodesic (I := I) g hEnorm p v (-s) ∈ maxSliceLocus I C) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      intrinsicGeodesic (I := I) g hEnorm p v s ∉ maxSliceLocus I C := by
  have hzero : intrinsicGeodesic (I := I) g hEnorm p v 0 = p :=
    intrinsicGeodesic_zero (I := I) g hEnorm p v
  have hcont : Continuous (intrinsicGeodesic (I := I) g hEnorm p v) :=
    intrinsicGeodesic_continuous (I := I) g hEnorm p v
  have hchord := minJoin_intrinsicGeodesic_near (I := I) (g := g) (hEnorm := hEnorm) v 0
    (standardDiagonalInverseBranch (I := I) g hEnorm (intrinsicGeodesic (I := I) g hEnorm p v 0))
  have hmap : _root_.Filter.Tendsto
      (fun st : ℝ × ℝ => (intrinsicGeodesic (I := I) g hEnorm p v st.1,
        intrinsicGeodesic (I := I) g hEnorm p v st.2)) (𝓝 ((0 : ℝ), (0 : ℝ))) (𝓝 (p, p)) := by
    have hcc : Continuous fun st : ℝ × ℝ =>
        (intrinsicGeodesic (I := I) g hEnorm p v st.1,
          intrinsicGeodesic (I := I) g hEnorm p v st.2) :=
      (hcont.comp continuous_fst).prodMk (hcont.comp continuous_snd)
    have hpair : _root_.Filter.Tendsto
        (fun st : ℝ × ℝ => (intrinsicGeodesic (I := I) g hEnorm p v st.1,
          intrinsicGeodesic (I := I) g hEnorm p v st.2)) (𝓝 ((0 : ℝ), (0 : ℝ)))
        (𝓝 (intrinsicGeodesic (I := I) g hEnorm p v 0,
          intrinsicGeodesic (I := I) g hEnorm p v 0)) := hcc.tendsto _
    rwa [hzero] at hpair
  have hpair := hmap.eventually
    (maxSliceLocus_pair (C := C) hEnorm hC (standardDiagonalInverseBranch (I := I) g hEnorm p))
  obtain ⟨J₁, J₂, hJ₁, h0J₁, hJ₂, h0J₂, hsub⟩ := mem_nhds_prod_iff'.1 (hchord.and hpair)
  have hJneg : ∀ᶠ s in 𝓝[>] (0 : ℝ), -s ∈ J₁ := by
    refine Eventually.filter_mono nhdsWithin_le_nhds ?_
    refine (hJ₁.preimage _root_.ContinuousNeg.continuous_neg).mem_nhds ?_
    simpa only [_root_.Set.mem_preimage, neg_zero] using h0J₁
  obtain ⟨ε, ⟨hεN, hεJ⟩, hε0⟩ := ((hback.and hJneg).and self_mem_nhdsWithin).exists
  have hεpos : (0 : ℝ) < ε := hε0
  filter_upwards [Eventually.filter_mono nhdsWithin_le_nhds (hJ₂.mem_nhds h0J₂),
    self_mem_nhdsWithin] with s hsJ hs0 hsN
  have hspos : (0 : ℝ) < s := hs0
  obtain ⟨hgood, hjoin⟩ := hsub (Set.mk_mem_prod hεJ hsJ)
  have hsum : (0 : ℝ) < s + ε := by linarith
  have ht0 : s / (s + ε) ∈ _root_.Set.Ioc (0 : ℝ) 1 :=
    ⟨div_pos hspos hsum, (div_le_one hsum).2 (by linarith)⟩
  have hpN : minJoin (I := I) g hEnorm (intrinsicGeodesic (I := I) g hEnorm p v s)
      (intrinsicGeodesic (I := I) g hEnorm p v (-ε)) (s / (s + ε)) ∈ maxSliceLocus I C :=
    hjoin hεN (maxSliceLocus_subset hsN) _ ht0
  rw [hgood (s / (s + ε))] at hpN
  have hsumne : s + ε ≠ 0 := ne_of_gt hsum
  have hkey : s / (s + ε) * (s + ε) = s := by field_simp
  have harg : s / (s + ε) * (-ε - s) + s = 0 := by linear_combination -hkey
  rw [harg, hzero] at hpN
  exact hp.2 hpN

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.eventually_not_mem_maxSliceLocus_of_back then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.eventually_not_mem_maxSliceLocus_of_back"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.eventually_not_mem_maxSliceLocus_of_back ``Submission.DifferentialGeometry.Geometry.Topology.eventually_not_mem_maxSliceLocus_of_back



theorem eventually_not_mem_maxSliceLocus_of_inner_neg
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    {p q : M} (hp : p ∈ relBoundary I C) {l : ℝ} (hl : 0 < l)
    {u v : TangentSpace I p} (hu : g.inner p u u = 1) (hv : g.inner p v v = 1)
    (hq : intrinsicGeodesic (I := I) g hEnorm p u l = q) (hpq : _root_.Dist.dist p q = l)
    (hdist : l ≤ Metric.infDist q (relBoundary I C))
    (huv : g.inner p u v < 0)
    (hback : ∀ᶠ s in 𝓝[>] (0 : ℝ), intrinsicGeodesic (I := I) g hEnorm p v (-s) ∈ C) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      intrinsicGeodesic (I := I) g hEnorm p v s ∉ maxSliceLocus I C := by
  have hnegv : g.inner p (-v) (-v) = 1 := by
    rw [← neg_one_smul ℝ v, gInner_smul_self (I := I) g p (-1) v, hv]
    norm_num
  have hnegu : 0 < g.inner p u (-v) := by
    have hmapneg : g.inner p u (-v) = -g.inner p u v := by
      rw [← neg_one_smul ℝ v, ContinuousLinearMap.map_smul, smul_eq_mul, neg_one_mul]
    rw [hmapneg]
    linarith
  have hCmem : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      intrinsicGeodesic (I := I) g hEnorm p (-v) s ∈ C := by
    filter_upwards [hback] with s hs
    rwa [intrinsicGeodesic_neg]
  have hinner := eventually_mem_maxSliceLocus_of_inner_pos (C := C) g hEnorm hsec hl hu hnegv
    hq hpq hdist hnegu hCmem
  refine eventually_not_mem_maxSliceLocus_of_back hEnorm hC hp ?_
  filter_upwards [hinner] with s hs
  rwa [intrinsicGeodesic_neg] at hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.eventually_not_mem_maxSliceLocus_of_inner_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.eventually_not_mem_maxSliceLocus_of_inner_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.eventually_not_mem_maxSliceLocus_of_inner_neg ``Submission.DifferentialGeometry.Geometry.Topology.eventually_not_mem_maxSliceLocus_of_inner_neg

theorem not_isInnerDirection_of_inner_neg
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    {p q : M} (hp : p ∈ relBoundary I C) {l : ℝ} (hl : 0 < l)
    {u v : TangentSpace I p} (hu : g.inner p u u = 1) (hv : g.inner p v v = 1)
    (hq : intrinsicGeodesic (I := I) g hEnorm p u l = q) (hpq : _root_.Dist.dist p q = l)
    (hdist : l ≤ Metric.infDist q (relBoundary I C))
    (huv : g.inner p u v < 0)
    (hback : ∀ᶠ s in 𝓝[>] (0 : ℝ), intrinsicGeodesic (I := I) g hEnorm p v (-s) ∈ C) :
    ¬ IsInnerDirection (I := I) g hEnorm C p v := by
  intro hmem
  rw [isInnerDirection_iff] at hmem
  have hout := eventually_not_mem_maxSliceLocus_of_inner_neg g hEnorm hsec hC hp hl hu hv
    hq hpq hdist huv hback
  obtain ⟨s, hs, hns⟩ := (hmem.and hout).exists
  exact hns hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.not_isInnerDirection_of_inner_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.not_isInnerDirection_of_inner_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.not_isInnerDirection_of_inner_neg ``Submission.DifferentialGeometry.Geometry.Topology.not_isInnerDirection_of_inner_neg

end DifferentialGeometry.Geometry.Topology
