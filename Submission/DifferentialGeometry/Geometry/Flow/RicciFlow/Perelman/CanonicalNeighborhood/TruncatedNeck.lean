import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StrongNeckRestriction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonComposition
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapComparisonTransport
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ClosedWindowMetricFields
import Submission.DifferentialGeometry.Analysis.Calculus.IteratedDerivative.WithinTower

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology _root_.Submission.DifferentialGeometry.Tensor0SBundle

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]

structure TruncatedNeck {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D)
    (eps depth : ℝ) (x : M) (t : ℝ) where
  eps_pos : 0 < eps
  eps_small : eps < 1 / 11
  depth_pos : 0 < depth
  depth_le_one : depth ≤ 1
  Q_pos : 0 < S.scalar t x
  cylinder : CylinderReference
  map : PartialDiffeomorph IC I3 Cylinder M ∞
  center : Sphere 2
  center_eq : map (center, 0) = x
  domain : _root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹ ⊆ map.source
  time_domain : _root_.Set.Icc (t - depth * (S.scalar t x)⁻¹) t ⊆ D.carrier
  comparison : MetricComparisonOn cylinder.metric
    (rescaledMetric S t (S.scalar t x) Q_pos) map
    (_root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹) (_root_.Set.Icc (-depth) 0) (⌈eps⁻¹⌉₊) eps

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TruncatedNeck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TruncatedNeck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TruncatedNeck ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TruncatedNeck

variable [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}
  {S : SolutionOn (I := I3) (M := M) D} {eps depth t : ℝ}

def TruncatedNeck.mono {x : M} (neck : TruncatedNeck S eps depth x t) {eps' : ℝ}
    (heps : eps ≤ eps') (hsmall : eps' < 1 / 11) : TruncatedNeck S eps' depth x t where
  eps_pos := lt_of_lt_of_le neck.eps_pos heps
  eps_small := hsmall
  depth_pos := neck.depth_pos
  depth_le_one := neck.depth_le_one
  Q_pos := neck.Q_pos
  cylinder := neck.cylinder
  map := neck.map
  center := neck.center
  center_eq := neck.center_eq
  domain := by
    have hle : eps'⁻¹ ≤ eps⁻¹ := inv_anti₀ neck.eps_pos heps
    exact fun y hy => neck.domain (_root_.Set.prod_mono (subset_refl _)
      (_root_.Set.Ioo_subset_Ioo (neg_le_neg hle) hle) hy)
  time_domain := neck.time_domain
  comparison := by
    have hle : eps'⁻¹ ≤ eps⁻¹ := inv_anti₀ neck.eps_pos heps
    exact neck.comparison.mono (_root_.Set.prod_mono (subset_refl _)
      (_root_.Set.Ioo_subset_Ioo (neg_le_neg hle) hle)) (Nat.ceil_mono hle) heps

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TruncatedNeck
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TruncatedNeck.mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TruncatedNeck.mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TruncatedNeck.mono ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TruncatedNeck.mono

def TruncatedNeck.restrictOpen {U : TopologicalSpace.Opens M}
    {S' : SolutionOn (I := I3) (M := U) D} {x : U} (nk : TruncatedNeck S eps depth (x : M) t)
    (hS : ∀ τ, S'.base.metric τ = (S.base.metric τ).restrictOpen U)
    (hmap : nk.map '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹) ⊆ U) :
    TruncatedNeck S' eps depth x t := by
  let i := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3) U ⟨x⟩
  have hitarget : i.target = (U : Set M) := U.openPartialHomeomorphSubtypeCoe_target ⟨x⟩
  let F := nk.map.trans i.symm
  have hdom : _root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹ ⊆ F.source := by
    intro y hy
    change y ∈ (nk.map.trans i.symm).source
    rw [PartialDiffeomorph.trans_source]
    refine ⟨nk.domain hy, ?_⟩
    change nk.map y ∈ i.target
    rw [hitarget]
    exact hmap ⟨y, hy, rfl⟩
  have hval (y : Cylinder) (hy : y ∈ _root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹) :
      (F y : M) = nk.map y := by
    change (((nk.map.trans i.symm) y) : M) = nk.map y
    rw [PartialDiffeomorph.trans_apply]
    apply i.right_inv'
    rw [hitarget]
    exact hmap ⟨y, hy, rfl⟩
  have hdf (y : Cylinder) (hy : y ∈ _root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹) :
      mfderiv IC I3 F y = mfderiv IC I3 nk.map y := by
    have hlocal : (fun z => (F z : M)) =ᶠ[𝓝 y] nk.map :=
      Filter.eventuallyEq_of_mem ((isOpen_univ.prod isOpen_Ioo).mem_nhds hy) hval
    have hFd := (F.contMDiffOn_toFun.contMDiffAt
      (F.open_source.mem_nhds (hdom hy))).mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hcomp := mfderiv_comp y (hasMFDerivAt_subtype_val (I := I3) U (F y)).mdifferentiableAt hFd
    rw [mfderiv_subtype_val] at hcomp
    have heq : mfderiv IC I3 (fun z => (F z : M)) y = mfderiv IC I3 nk.map y :=
      hlocal.mfderiv_eq
    ext v
    have hc : mfderiv IC I3 (fun z => (F z : M)) y v = mfderiv IC I3 F y v :=
      DFunLike.congr_fun hcomp v
    exact hc.symm.trans (DFunLike.congr_fun heq v)
  have hR : S'.scalar t x = S.scalar t (x : M) := by
    change metricScalarAt (S'.base.metric t) x = metricScalarAt (S.base.metric t) (x : M)
    rw [hS t]
    exact metricScalarAt_restrictOpen _ U x
  have hQ : 0 < S'.scalar t x := hR.symm ▸ nk.Q_pos
  refine
    { eps_pos := nk.eps_pos
      eps_small := nk.eps_small
      depth_pos := nk.depth_pos
      depth_le_one := nk.depth_le_one
      Q_pos := hQ
      cylinder := nk.cylinder
      map := F
      center := nk.center
      center_eq := ?_
      domain := hdom
      time_domain := by rw [hR]; exact nk.time_domain
      comparison := ?_ }
  · apply Subtype.ext
    exact (hval (nk.center, 0) ⟨mem_univ _, neg_lt_zero.mpr (inv_pos.mpr nk.eps_pos),
      inv_pos.mpr nk.eps_pos⟩).trans nk.center_eq
  · refine
      { pullback := nk.comparison.pullback
        pullback_eq := ?_
        jet := nk.comparison.jet
        jet_zero := nk.comparison.jet_zero
        jet_succ := nk.comparison.jet_succ
        equivalence := nk.comparison.equivalence
        close := nk.comparison.close }
    intro τ y hy v
    rw [nk.comparison.pullback_eq τ y hy v]
    simp only [rescaledMetric, scaleMetric_inner, hS, SmoothRiemannianMetric.restrictOpen_inner,
      hR, hdf y hy]
    exact congrArg (fun w => S.scalar t (x : M) * ((S.base.metric (parabolicTime t
      (S.scalar t (x : M)) τ)).inner w) _ _) (hval y hy).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TruncatedNeck.restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TruncatedNeck.restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TruncatedNeck.restrictOpen ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TruncatedNeck.restrictOpen

private local instance truncatedNeckC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.truncatedNeckC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.truncatedNeckC1 target :: scope.openDecls } }

theorem StrongNeck.comparison_jet_differentiableWithinAt_of_lt_one {x : M}
    (hS : IsSolutionOn S) (nk : StrongNeck S eps x t) {d : ℝ} (hd : d < 1)
    (hreg : _root_.Set.Ioo (t - (S.scalar t x)⁻¹) t ⊆ D.regular)
    (q : ℕ) {s : ℝ} (hs : s ∈ _root_.Set.Icc (-d) 0)
    (y : Cylinder) (hy : y ∈ _root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹)
    (v : Fin 2 → TangentSpace IC y) :
    DifferentiableWithinAt ℝ (fun r => nk.comparison.jet q r y v) (_root_.Set.Icc (-1 : ℝ) 0) s := by
  let Q : ℝ := S.scalar t x
  have hQ : 0 < Q := nk.Q_pos
  have hd0 : 0 ≤ d := by linarith [hs.1, hs.2]
  set e : ℝ := (1 + d) / 2 with he
  have hde : d < e := by rw [he]; linarith
  have he1 : e < 1 := by rw [he]; linarith
  have he0 : 0 < e := by rw [he]; linarith
  have hQi : 0 < Q⁻¹ := inv_pos.mpr hQ
  have hac : t - Q⁻¹ < t - e * Q⁻¹ := by nlinarith
  have hct : t - e * Q⁻¹ < t := by nlinarith
  have hslab : _root_.Set.Icc (t - Q⁻¹) t ⊆ D.carrier := nk.time_domain
  let w : Fin 2 → TangentSpace I3 (nk.map y) := fun j => mfderiv IC I3 nk.map y (v j)
  have hsource0 := (tensor0SEvalCLM (I := I3) (x := nk.map y) w).contDiff.comp_contDiffOn
    (metricTensor_contDiffOn_time S hS hac hct hslab hreg (nk.map y))
  have htime : ContDiff ℝ ∞ (parabolicTime t Q) :=
    contDiff_const.add (contDiff_id.div_const Q)
  have hmap : _root_.Set.MapsTo (parabolicTime t Q) (_root_.Set.Icc (-e) 0) (_root_.Set.Icc (t - e * Q⁻¹) t) := by
    intro r hr
    have h1 : (-e) / Q ≤ r / Q := div_le_div_of_nonneg_right hr.1 hQ.le
    have h2 : r / Q ≤ 0 := div_nonpos_of_nonpos_of_nonneg hr.2 hQ.le
    constructor
    · change t - e * Q⁻¹ ≤ t + r / Q
      rw [neg_div, div_eq_mul_inv] at h1
      linarith
    · change t + r / Q ≤ t
      linarith
  have hsource : ContDiffOn ℝ ∞
      (fun r => (S.base.metric (parabolicTime t Q r)).inner (nk.map y) (w 0) (w 1))
      (_root_.Set.Icc (-e) 0) := by
    have hh := hsource0.comp htime.contDiffOn hmap
    change ContDiffOn ℝ ∞
      (fun r => metricTensorField (S.base.metric (parabolicTime t Q r)) (nk.map y) w)
      (_root_.Set.Icc (-e) 0) at hh
    simpa only [metricTensorField_apply] using hh
  have hscaled : ContDiffOn ℝ ∞
      (fun r => (rescaledMetric S t (S.scalar t x) nk.Q_pos r).inner
        (nk.map y) (w 0) (w 1)) (_root_.Set.Icc (-e) 0) := by
    simpa only [rescaledMetric, scaleMetric_inner, SolutionOn.family,
      Function.comp_def, smul_eq_mul, Q] using hsource.const_smul Q
  have hpull : ContDiffOn ℝ ∞ (fun r => nk.comparison.pullback r y v) (_root_.Set.Icc (-e) 0) :=
    hscaled.congr (fun r _ => nk.comparison.pullback_eq r y hy v)
  have hcylinder : ContDiffOn ℝ ∞
      (fun r => (nk.cylinder.metric r).inner y (v 0) (v 1)) (_root_.Set.Icc (-e) 0) := by
    have hh : ContDiff ℝ ∞ (fun r : ℝ =>
        2 * (1 - r) * _root_.Inner.inner ℝ
          (show ThreeSpace from mfderiv I2 I3 (fun z : Sphere 2 => (z : ThreeSpace)) y.1 (v 0).1)
          (show ThreeSpace from mfderiv I2 I3 (fun z : Sphere 2 => (z : ThreeSpace)) y.1 (v 1).1) +
            (v 0).2 * (v 1).2) := by fun_prop
    exact hh.contDiffOn.congr (fun r hr => nk.cylinder.inner_eq r hr.2 y (v 0) (v 1))
  have hzero : ContDiffOn ℝ ∞ (fun r => nk.comparison.jet 0 r y v) (_root_.Set.Icc (-e) 0) :=
    (hpull.sub hcylinder).congr (fun r _ => nk.comparison.jet_zero r y v)
  have hse : s ∈ _root_.Set.Icc (-e) 0 := ⟨by linarith [hs.1], hs.2⟩
  have hnhds : _root_.Set.Icc (-e) 0 ∈ 𝓝[_root_.Set.Icc (-1 : ℝ) 0] s := by
    refine mem_nhdsWithin.mpr ⟨Ioi (-e), isOpen_Ioi, show -e < s by linarith [hs.1], ?_⟩
    rintro r ⟨hr1, hr2⟩
    exact ⟨le_of_lt hr1, hr2.2⟩
  have hzeroAt : ContDiffWithinAt ℝ ∞ (fun r => nk.comparison.jet 0 r y v) (_root_.Set.Icc (-1 : ℝ) 0) s := by
    rw [← contDiffWithinAt_inter' hnhds]
    exact (hzero s hse).mono _root_.Set.inter_subset_right
  have hs1 : s ∈ _root_.Set.Icc (-1 : ℝ) 0 := ⟨by linarith [hs.1], hs.2⟩
  exact (DifferentialGeometry.Analysis.contDiffWithinAt_derivWithin_tower
    (f := fun b r => nk.comparison.jet b r y v)
    (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 0)) hs1 hzeroAt
    (fun b r hr => nk.comparison.jet_succ b r hr y hy v) q).differentiableWithinAt (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.comparison_jet_differentiableWithinAt_of_lt_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.comparison_jet_differentiableWithinAt_of_lt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.comparison_jet_differentiableWithinAt_of_lt_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.comparison_jet_differentiableWithinAt_of_lt_one

def TruncatedNeck.ofStrongNeck {x : M} (nk : StrongNeck S eps x t) (hd : 0 < depth)
    (hd1 : depth ≤ 1)
    (hdiff : ∀ b, ∀ s ∈ _root_.Set.Icc (-depth) 0, ∀ y ∈ _root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹,
      ∀ v : Fin 2 → TangentSpace IC y,
        DifferentiableWithinAt ℝ (fun a => nk.comparison.jet b a y v) (_root_.Set.Icc (-1 : ℝ) 0) s) :
    TruncatedNeck S eps depth x t where
  eps_pos := nk.eps_pos
  eps_small := nk.eps_small
  depth_pos := hd
  depth_le_one := hd1
  Q_pos := nk.Q_pos
  cylinder := nk.cylinder
  map := nk.map
  center := nk.center
  center_eq := nk.center_eq
  domain := nk.domain
  time_domain := fun _ hr => nk.time_domain
    ⟨le_trans (sub_le_sub_left (mul_le_of_le_one_left (inv_nonneg.mpr nk.Q_pos.le) hd1) t) hr.1,
      hr.2⟩
  comparison := nk.comparison.restrictTimes (_root_.Set.Icc_subset_Icc (neg_le_neg hd1) le_rfl)
    (uniqueDiffOn_Icc (neg_lt_zero.mpr hd)) hdiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TruncatedNeck.ofStrongNeck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TruncatedNeck.ofStrongNeck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TruncatedNeck.ofStrongNeck ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TruncatedNeck.ofStrongNeck

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
