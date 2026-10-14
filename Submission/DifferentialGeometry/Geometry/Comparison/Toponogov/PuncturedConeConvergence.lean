import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.PuncturedConeMetric
import Submission.DifferentialGeometry.Topology.MetricSpace.CompactApproximation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter _root_.Metric _root_.Submission.Metric
open scoped _root_.Topology
namespace DifferentialGeometry.Toponogov

variable {M X : Type*} [MetricSpace M] [MetricSpace X]
  {q : UniformSpace.Completion M} {d : ℝ}

theorem PuncturedConeApproximation.exists_local_isometry_of_rescaled_convergence
    (C : PuncturedConeApproximation q d)
    (p : X) (x : ℕ → M) (f : ℕ → X → M) (rho : ℕ → ℝ)
    (hrho : ∀ i, 0 < rho i) (hrho0 : _root_.Filter.Tendsto rho _root_.Filter.atTop (𝓝 0))
    (hbase : ∀ i, f i p = x i)
    {R lower B : ℝ} (hR : 0 < R) (hlower : 0 < lower)
    (hcompact : IsCompact (_root_.Metric.closedBall p R))
    (hcenter : ∀ᶠ i in _root_.Filter.atTop, _root_.Dist.dist (x i : UniformSpace.Completion M) q / rho i ∈ _root_.Set.Icc lower B)
    (hcover : ∀ᶠ i in _root_.Filter.atTop, _root_.Metric.closedBall (x i) (R / 4 * rho i) ⊆ f i '' _root_.Metric.closedBall p R)
    (hdist : ∀ eps : ℝ, 0 < eps → ∀ᶠ i in _root_.Filter.atTop,
      ∀ a ∈ _root_.Metric.closedBall p R, ∀ b ∈ _root_.Metric.closedBall p R,
        |dist (f i a) (f i b) / rho i - _root_.Dist.dist a b| < eps) :
    let _ := C.angles.metricSpace
    let _ : MetricSpace (ConeAnnulus (lower / 2) (B + lower)
      (UniformSpace.Completion (Quotient C.angles.setoid))) :=
      C.annulusMetricSpace (by positivity : 0 < lower / 2)
    ∃ r : ℝ, ∃ hr : 0 < r, r < R ∧
      ∃ F : _root_.Metric.closedBall p r → ConeAnnulus (lower / 2) (B + lower)
        (UniformSpace.Completion (Quotient C.angles.setoid)),
        Isometry F ∧
        ((F ⟨p, _root_.Metric.mem_closedBall_self hr.le⟩).1 : ℝ) ∈ _root_.Set.Icc (3 * lower / 4) (B + lower / 4) ∧
        ball (F ⟨p, _root_.Metric.mem_closedBall_self hr.le⟩) (r / 16) ⊆ _root_.Set.range F := by
  let _ := C.angles.metricSpace
  let _ : CompactSpace (UniformSpace.Completion (Quotient C.angles.setoid)) := C.compact_directions
  let _ : MetricSpace (ConeAnnulus (lower / 2) (B + lower)
    (UniformSpace.Completion (Quotient C.angles.setoid))) :=
    C.annulusMetricSpace (by positivity : 0 < lower / 2)
  dsimp only
  let Y := ConeAnnulus (lower / 2) (B + lower) (UniformSpace.Completion (Quotient C.angles.setoid))
  let r := _root_.Min.min (R / 8) (lower / 8)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrR : r ≤ R / 8 := min_le_left _ _
  have hr8 : r ≤ lower / 8 := min_le_right _ _
  have hsmall : r < R := by linarith
  let K := _root_.Metric.closedBall p r
  have hK : IsCompact K := hcompact.of_isClosed_subset _root_.Metric.isClosed_closedBall
    (_root_.Metric.closedBall_subset_closedBall hsmall.le)
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let p0 : K := ⟨p, _root_.Metric.mem_closedBall_self hr.le⟩
  have hKR : K ⊆ _root_.Metric.closedBall p R := _root_.Metric.closedBall_subset_closedBall hsmall.le
  have hpR : p ∈ _root_.Metric.closedBall p R := _root_.Metric.mem_closedBall_self hR.le
  have hwithin : _root_.Filter.Tendsto rho _root_.Filter.atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hrho0, Eventually.of_forall hrho⟩
  have hB : lower ≤ B := by
    obtain ⟨i, hi⟩ := hcenter.exists
    exact hi.1.trans hi.2
  have happrox (eps : ℝ) (heps : 0 < eps) (hepsr : eps ≤ r / 100) :
      ∃ A : K → Y,
        (∀ a b, |_root_.Dist.dist (A a) (A b) - _root_.Dist.dist a b| < 2 * eps) ∧
        (∀ z ∈ _root_.Metric.ball (A p0) (r / 16), ∃ a, _root_.Dist.dist z (A a) < eps) ∧
        ((A p0).1 : ℝ) ∈ _root_.Set.Icc (3 * lower / 4) (B + lower / 4) := by
    obtain ⟨i, ⟨hci, hcovi⟩, hdi, A, hA, hAcov, hArad⟩ :=
      ((hcenter.and hcover).and ((hdist eps heps).and
        (hwithin (C.exists_annulus_approximation (by positivity : 0 < lower / 2)
          (by linarith : lower / 2 ≤ B + lower) heps)))).exists
    have hin (a : K) : _root_.Dist.dist (f i a : UniformSpace.Completion M) q / rho i ∈ _root_.Set.Icc (lower / 2) (B + lower) := by
      have hpair := (abs_lt.mp (hdi a (hKR a.property) p hpR)).2
      rw [hbase] at hpair
      have ha : _root_.Dist.dist (a : X) p ≤ r := a.property
      have hrad := div_le_div_of_nonneg_right
        (abs_dist_sub_le (f i a : UniformSpace.Completion M) (x i : UniformSpace.Completion M) q)
        (hrho i).le
      have hrad' : |_root_.Dist.dist (f i a : UniformSpace.Completion M) q / rho i -
          dist (x i : UniformSpace.Completion M) q / rho i| ≤ _root_.Dist.dist (f i a) (x i) / rho i := by
        simpa only [← sub_div, abs_div, abs_of_pos (hrho i), UniformSpace.Completion.dist_eq] using hrad
      have habs := abs_le.mp hrad'
      exact ⟨by linarith only [hpair, ha, habs.1, hci.1, hepsr, hr8, hlower],
        by linarith only [hpair, ha, habs.2, hci.2, hepsr, hr8, hlower]⟩
    let j : K → {a : M // _root_.Dist.dist (a : UniformSpace.Completion M) q / rho i ∈ _root_.Set.Icc (lower / 2) (B + lower)} :=
      fun a => ⟨f i a, hin a⟩
    let F := A ∘ j
    refine ⟨F, ?_, ?_, ?_⟩
    · intro a b
      have h1 := abs_lt.mp (hA (j a) (j b))
      have h2 := abs_lt.mp (hdi a (hKR a.property) b (hKR b.property))
      change |_root_.Dist.dist (A (j a)) (A (j b)) - _root_.Dist.dist (a : X) (b : X)| < 2 * eps
      exact abs_lt.mpr ⟨by linarith only [h1.1, h2.1], by linarith only [h1.2, h2.2]⟩
    · intro z hz
      obtain ⟨y, hy⟩ := hAcov z
      have hz' : _root_.Dist.dist z (A (j p0)) < r / 16 := hz
      have hpair := (abs_lt.mp (hA y (j p0))).1
      change -eps < _root_.Dist.dist (A y) (A (j p0)) - _root_.Dist.dist (y : M) (f i p) / rho i at hpair
      rw [hbase] at hpair
      have htri := dist_triangle (A y) z (A (j p0))
      rw [dist_comm (A y) z] at htri
      have hnear : _root_.Dist.dist (y : M) (x i) / rho i < r / 8 := by
        linarith only [hpair, htri, hy, hz', hepsr, hr]
      have hyball : (y : M) ∈ _root_.Metric.closedBall (x i) (R / 4 * rho i) :=
        ((div_lt_iff₀ (hrho i)).mp (hnear.trans_le (by linarith))).le
      obtain ⟨a, ha, hay⟩ := hcovi hyball
      have hpair' := (abs_lt.mp (hdi a ha p hpR)).1
      rw [hay, hbase] at hpair'
      have har : a ∈ K := by
        change _root_.Dist.dist a p ≤ r
        linarith only [hpair', hnear, hepsr, hr]
      refine ⟨⟨a, har⟩, ?_⟩
      have hj : j ⟨a, har⟩ = y := Subtype.ext hay
      change _root_.Dist.dist z (A (j ⟨a, har⟩)) < eps
      rw [hj]
      exact hy
    · change ((A (j p0)).1 : ℝ) ∈ _root_.Set.Icc (3 * lower / 4) (B + lower / 4)
      have hrad := abs_lt.mp (hArad (j p0))
      change -eps < ((A (j p0)).1 : ℝ) - _root_.Dist.dist (f i p : UniformSpace.Completion M) q / rho i ∧
        ((A (j p0)).1 : ℝ) - _root_.Dist.dist (f i p : UniformSpace.Completion M) q / rho i < eps at hrad
      rw [hbase] at hrad
      exact ⟨by linarith only [hrad.1, hci.1, hepsr, hr8, hlower],
        by linarith only [hrad.2, hci.2, hepsr, hr8, hlower]⟩
  let eps := fun n : ℕ => _root_.Min.min (1 / ((n : ℝ) + 1)) (r / 100)
  have heps (n : ℕ) : 0 < eps n := lt_min (by positivity) (by positivity)
  have hepsr (n : ℕ) : eps n ≤ r / 100 := min_le_right _ _
  have heps0 : _root_.Filter.Tendsto eps _root_.Filter.atTop (𝓝 0) :=
    squeeze_zero (fun n => (heps n).le) (fun n => min_le_left _ _)
      tendsto_one_div_add_atTop_nhds_zero_nat
  choose A hA hcoverA hcenterA using fun n => happrox (eps n) (heps n) (hepsr n)
  obtain ⟨F, hF, hcluster, hcoverF⟩ := Metric.exists_isometry_mapClusterPt_of_compact_approximation
    A (by simpa using heps0.const_mul 2)
    (Eventually.of_forall fun n a b => (hA n a b).le) p0 (r / 16)
    (Eventually.of_forall fun n z hz => by
      obtain ⟨a, ha⟩ := hcoverA n z hz
      exact ⟨a, ha.le.trans (by linarith only [heps n])⟩)
  have hclosed : IsClosed {F : K → Y | ((F p0).1 : ℝ) ∈ _root_.Set.Icc (3 * lower / 4) (B + lower / 4)} :=
    isClosed_Icc.preimage (continuous_subtype_val.comp (continuous_fst.comp (continuous_apply p0)))
  exact ⟨r, hr, hsmall, F, hF,
    hclosed.mem_of_mapClusterPt hcluster (Eventually.of_forall hcenterA), hcoverF⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.PuncturedConeApproximation.exists_local_isometry_of_rescaled_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.PuncturedConeApproximation.exists_local_isometry_of_rescaled_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.PuncturedConeApproximation.exists_local_isometry_of_rescaled_convergence ``Submission.DifferentialGeometry.Toponogov.PuncturedConeApproximation.exists_local_isometry_of_rescaled_convergence

private theorem exists_cone_coordinates_of_local_isometry
    (C : PuncturedConeApproximation q d) (p : X) {r lower B : ℝ} (hr : 0 < r) (hlower : 0 < lower) :
    let _ := C.angles.metricSpace
    let _ : MetricSpace (ConeAnnulus (lower / 2) (B + lower)
      (UniformSpace.Completion (Quotient C.angles.setoid))) :=
      C.annulusMetricSpace (by positivity : 0 < lower / 2)
    ∀ F : _root_.Metric.closedBall p r → ConeAnnulus (lower / 2) (B + lower)
      (UniformSpace.Completion (Quotient C.angles.setoid)),
      Isometry F →
      ((F ⟨p, _root_.Metric.mem_closedBall_self hr.le⟩).1 : ℝ) ∈ _root_.Set.Icc (3 * lower / 4) (B + lower / 4) →
      _root_.Metric.ball (F ⟨p, _root_.Metric.mem_closedBall_self hr.le⟩) (r / 16) ⊆ _root_.Set.range F →
      ∃ e : OpenPartialHomeomorph X (ℝ × UniformSpace.Completion (Quotient C.angles.setoid)),
        p ∈ e.source ∧ (∀ z ∈ e.target, 0 < z.1) ∧
        ∀ a ∈ e.source, ∀ b ∈ e.source, _root_.Dist.dist a b = Metric.coneDistance (e a) (e b) := by
  let _ := C.angles.metricSpace
  let _ : MetricSpace (ConeAnnulus (lower / 2) (B + lower)
    (UniformSpace.Completion (Quotient C.angles.setoid))) :=
    C.annulusMetricSpace (by positivity : 0 < lower / 2)
  dsimp only
  intro F hF hcenter hcover
  let Y := UniformSpace.Completion (Quotient C.angles.setoid)
  let A := ConeAnnulus (lower / 2) (B + lower) Y
  let p0 : _root_.Metric.closedBall p r := ⟨p, _root_.Metric.mem_closedBall_self hr.le⟩
  let delta := _root_.Min.min (r / 32) (lower / 16)
  have hd : 0 < delta := lt_min (by positivity) (by positivity)
  have hdr : delta < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hd16 : delta < r / 16 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hdsmall : delta ≤ lower / 16 := min_le_right _ _
  let U : TopologicalSpace.Opens X := ⟨ball p delta, isOpen_ball⟩
  have hp : p ∈ U := _root_.Metric.mem_ball_self hd
  let j : U → _root_.Metric.closedBall p r := fun a => ⟨a, a.property.le.trans hdr.le⟩
  have hj : Isometry j := Isometry.of_dist_eq fun _ _ => rfl
  let G := F ∘ j
  have hG : Isometry G := hF.comp hj
  have hGp (a : U) : _root_.Dist.dist (G a) (F p0) = _root_.Dist.dist (a : X) p := hF.dist_eq (j a) p0
  have hGrange : _root_.Set.range G = _root_.Metric.ball (F p0) delta := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      change _root_.Dist.dist (G a) (F p0) < delta
      rw [hGp]
      exact a.property
    · intro hz
      obtain ⟨a, ha⟩ := hcover ((_root_.Metric.ball_subset_ball hd16.le) hz)
      have haU : (a : X) ∈ U := by
        change _root_.Dist.dist a p0 < delta
        rw [← hF.dist_eq a p0, ha]
        exact hz
      refine ⟨⟨a, haU⟩, ?_⟩
      change F (j ⟨a, haU⟩) = z
      have hja : j ⟨a, haU⟩ = a := Subtype.ext rfl
      rw [hja]
      exact ha
  let J : A → ℝ × Y := fun z => ((z.1 : ℝ), z.2)
  have hJ : Topology.IsEmbedding J := Topology.IsEmbedding.subtypeVal.prodMap Topology.IsEmbedding.id
  have hinterior (z : A) (hz : z ∈ _root_.Metric.ball (F p0) delta) : (J z).1 ∈ _root_.Set.Ioo (lower / 2) (B + lower) := by
    have hrad := Metric.abs_radius_sub_le_coneDistance
      (x := J z) (y := J (F p0))
      (show 0 ≤ (J z).1 from le_trans (by positivity) z.1.property.1)
      (show 0 ≤ (J (F p0)).1 from le_trans (by positivity) (F p0).1.property.1)
    change |(z.1 : ℝ) - ((F p0).1 : ℝ)| ≤ _root_.Dist.dist z (F p0) at hrad
    have hz' : _root_.Dist.dist z (F p0) < delta := hz
    have hh := abs_le.mp hrad
    exact ⟨by linarith only [hh.1, hz', hdsmall, hcenter.1, hlower],
      by linarith only [hh.2, hz', hdsmall, hcenter.2, hlower]⟩
  have hopen : IsOpen (J '' _root_.Metric.ball (F p0) delta) := by
    obtain ⟨V, hV, hpre⟩ := (hJ.isInducing.isOpen_iff (s := _root_.Metric.ball (F p0) delta)).mp _root_.Metric.isOpen_ball
    have heq : J '' _root_.Metric.ball (F p0) delta = V ∩ (_root_.Set.Ioo (lower / 2) (B + lower) ×ˢ _root_.Set.univ) := by
      ext z
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨show J a ∈ V from (show a ∈ J ⁻¹' V by rwa [hpre]), hinterior a ha, _root_.Set.mem_univ _⟩
      · rintro ⟨hzV, hzrad, _⟩
        let a : A := (⟨z.1, hzrad.1.le, hzrad.2.le⟩, z.2)
        have ha : a ∈ _root_.Metric.ball (F p0) delta := by
          rw [← hpre]
          exact hzV
        exact ⟨a, ha, rfl⟩
    rw [heq]
    exact hV.inter (isOpen_Ioo.prod isOpen_univ)
  let H := J ∘ G
  have hH : Topology.IsOpenEmbedding H := by
    refine ⟨hJ.comp hG.isEmbedding, ?_⟩
    change IsOpen (_root_.Set.range (J ∘ G))
    rw [_root_.Set.range_comp, hGrange]
    exact hopen
  let _ : Nonempty U := ⟨⟨p, hp⟩⟩
  let inc := U.openPartialHomeomorphSubtypeCoe ⟨⟨p, hp⟩⟩
  let E := hH.toOpenPartialHomeomorph H
  let e := inc.symm.trans E
  have hsource : e.source = (U : Set X) := by
    simp [e, inc, E]
  have hinv (a : X) (ha : a ∈ (U : Set X)) : ((inc.symm a : U) : X) = a :=
    inc.right_inv (by simpa only [inc, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using ha)
  have heval (a : X) : e a = J (G (inc.symm a)) := rfl
  refine ⟨e, by rwa [hsource], ?_, ?_⟩
  · intro z hz
    rw [← e.right_inv hz, heval]
    exact lt_of_lt_of_le (by positivity : (0 : ℝ) < lower / 2) (G (inc.symm (e.symm z))).1.property.1
  · intro a ha b hb
    rw [heval, heval]
    change _root_.Dist.dist a b = _root_.Dist.dist (G (inc.symm a)) (G (inc.symm b))
    rw [hG.dist_eq]
    change _root_.Dist.dist a b = _root_.Dist.dist ((inc.symm a : U) : X) ((inc.symm b : U) : X)
    rw [hinv a (hsource ▸ ha), hinv b (hsource ▸ hb)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Toponogov.exists_cone_coordinates_of_local_isometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Toponogov.exists_cone_coordinates_of_local_isometry target :: scope.openDecls } }

theorem PuncturedConeApproximation.exists_cone_coordinates_of_rescaled_convergence
    (C : PuncturedConeApproximation q d)
    (p : X) (x : ℕ → M) (f : ℕ → X → M) (rho : ℕ → ℝ)
    (hrho : ∀ i, 0 < rho i) (hrho0 : _root_.Filter.Tendsto rho _root_.Filter.atTop (𝓝 0))
    (hbase : ∀ i, f i p = x i)
    {R lower B : ℝ} (hR : 0 < R) (hlower : 0 < lower)
    (hcompact : IsCompact (_root_.Metric.closedBall p R))
    (hcenter : ∀ᶠ i in _root_.Filter.atTop, _root_.Dist.dist (x i : UniformSpace.Completion M) q / rho i ∈ _root_.Set.Icc lower B)
    (hcover : ∀ᶠ i in _root_.Filter.atTop, _root_.Metric.closedBall (x i) (R / 4 * rho i) ⊆ f i '' _root_.Metric.closedBall p R)
    (hdist : ∀ eps : ℝ, 0 < eps → ∀ᶠ i in _root_.Filter.atTop,
      ∀ a ∈ _root_.Metric.closedBall p R, ∀ b ∈ _root_.Metric.closedBall p R,
        |dist (f i a) (f i b) / rho i - _root_.Dist.dist a b| < eps) :
    let _ := C.angles.metricSpace
    ∃ e : OpenPartialHomeomorph X (ℝ × UniformSpace.Completion (Quotient C.angles.setoid)),
      p ∈ e.source ∧ (∀ z ∈ e.target, 0 < z.1) ∧
      ∀ a ∈ e.source, ∀ b ∈ e.source, _root_.Dist.dist a b = Metric.coneDistance (e a) (e b) := by
  let _ := C.angles.metricSpace
  dsimp only
  let _ : MetricSpace (ConeAnnulus (lower / 2) (B + lower)
    (UniformSpace.Completion (Quotient C.angles.setoid))) :=
    C.annulusMetricSpace (by positivity : 0 < lower / 2)
  obtain ⟨r, hr, _, F, hF, hcenterF, hcoverF⟩ :=
    C.exists_local_isometry_of_rescaled_convergence p x f rho hrho hrho0 hbase
      hR hlower hcompact hcenter hcover hdist
  exact exists_cone_coordinates_of_local_isometry C p hr hlower F hF hcenterF hcoverF

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.PuncturedConeApproximation.exists_cone_coordinates_of_rescaled_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.PuncturedConeApproximation.exists_cone_coordinates_of_rescaled_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.PuncturedConeApproximation.exists_cone_coordinates_of_rescaled_convergence ``Submission.DifferentialGeometry.Toponogov.PuncturedConeApproximation.exists_cone_coordinates_of_rescaled_convergence

end DifferentialGeometry.Toponogov
