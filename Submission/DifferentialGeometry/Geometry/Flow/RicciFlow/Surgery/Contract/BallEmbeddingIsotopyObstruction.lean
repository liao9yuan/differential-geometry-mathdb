import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.BallEmbeddingIsotopy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Metric _root_.Submission.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {U : Type u} [TopologicalSpace U] [ChartedSpace ThreeSpace U]
  [IsManifold ThreeModel ∞ U] {o : ManifoldOrientation ThreeModel U 3}

theorem not_supportedBallEmbeddingIsotopy_swap {ι : Type u} [Fintype ι] [DecidableEq ι]
    (e : ι → OrientedBallEmbedding U o) (i j : ι) (hij : i ≠ j)
    (hne : (e i).chart (0 : ThreeSpace) ≠ (e j).chart (0 : ThreeSpace)) :
    ¬ SupportedBallEmbeddingIsotopy ι U o e
      (fun k => if k = i then e j else if k = j then e i else e k) := by
  rintro ⟨J, V, r, -, -, -, -, -, hVfix, hr, -, hJ1, havoid⟩
  have hmem : (0 : ThreeSpace) ∈ Metric.closedBall (0 : ThreeSpace) r :=
    Metric.mem_closedBall_self hr.le
  have havoid' : (e i).chart (0 : ThreeSpace) ∉ V j := havoid i j hij (0 : ThreeSpace) hmem
  have hfix : J j 1 ((e i).chart (0 : ThreeSpace)) = (e i).chart (0 : ThreeSpace) :=
    hVfix j 1 havoid'
  have hJ1' : J j 1 ((e j).chart (0 : ThreeSpace)) = (e i).chart (0 : ThreeSpace) := by
    have h := hJ1 j (0 : ThreeSpace) hmem
    simpa [hij.symm] using h
  have hEq : J j 1 ((e j).chart (0 : ThreeSpace)) = J j 1 ((e i).chart (0 : ThreeSpace)) := by
    rw [hJ1', hfix]
  have hval : (e j).chart (0 : ThreeSpace) = (e i).chart (0 : ThreeSpace) := by
    have h := congrArg (fun x : U => (J j 1).symm x) hEq
    simpa using h
  exact hne hval.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_supportedBallEmbeddingIsotopy_swap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_supportedBallEmbeddingIsotopy_swap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_supportedBallEmbeddingIsotopy_swap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_supportedBallEmbeddingIsotopy_swap

theorem disjoint_chart_image_closedBall_affine
    {M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3}
    (c : DifferentialGeometry.Topology.OrientedBallChart M)
    (s : ThreeSpace) (r : ℝ) (hr : 0 < r) (hs : ‖s‖ + 2 * r ≤ 2) (hbig : 1 + r < ‖s‖) :
    Disjoint (c.chart '' Metric.closedBall (0 : ThreeSpace) 1)
      ((c.affine s r hr hs).chart '' Metric.closedBall (0 : ThreeSpace) 1) := by
  rw [Set.disjoint_left]
  rintro y ⟨x, hx, rfl⟩ ⟨x', hx', hxx'⟩
  have hx1 : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  have hx'1 : ‖x'‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx'
  have hxs : x ∈ c.chart.source :=
    c.closedBall_subset_source (by
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith)
  have hsx's : s + r • x' ∈ c.chart.source :=
    c.closedBall_subset_source (by
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖s + r • x'‖ ≤ ‖s‖ + ‖r • x'‖ := norm_add_le _ _
        _ = ‖s‖ + r * ‖x'‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
        _ ≤ ‖s‖ + r * 1 := by nlinarith [norm_nonneg s]
        _ ≤ 2 := by nlinarith)
  have hkey : (c.affine s r hr hs).chart x' = c.chart (s + r • x') :=
    DifferentialGeometry.Topology.OrientedBallChart.affine_apply c s r hr hs x'
  have hinj : x = s + r • x' :=
    c.chart.toPartialEquiv.injOn hxs hsx's (hxx'.symm.trans hkey)
  have hsub : x - r • x' = s := by rw [hinj]; simp
  have hnorm : ‖s‖ = ‖x - r • x'‖ := by rw [hsub]
  have hle : ‖x - r • x'‖ ≤ 1 + r := by
    calc ‖x - r • x'‖ ≤ ‖x‖ + ‖r • x'‖ := norm_sub_le _ _
      _ = ‖x‖ + r * ‖x'‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      _ ≤ 1 + r * 1 := by nlinarith [norm_nonneg x, norm_nonneg x']
      _ = 1 + r := by ring
  have : ‖s‖ ≤ 1 + r := by rw [hnorm]; exact hle
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.disjoint_chart_image_closedBall_affine then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.disjoint_chart_image_closedBall_affine"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.disjoint_chart_image_closedBall_affine ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.disjoint_chart_image_closedBall_affine

theorem not_supportedBallEmbeddingIsotopy_standardThreeSphere :
    ∃ (e e' : Fin 2 → OrientedBallEmbedding
        (DifferentialGeometry.Topology.standardThreeSphereLift.{0}).Carrier
        (DifferentialGeometry.Topology.standardThreeSphereLift.{0}).orientation),
      (Pairwise fun i j => Disjoint ((e i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((e j).chart '' Metric.closedBall (0 : ThreeSpace) 1)) ∧
      (Pairwise fun i j => Disjoint ((e' i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((e' j).chart '' Metric.closedBall (0 : ThreeSpace) 1)) ∧
      ¬ SupportedBallEmbeddingIsotopy (Fin 2)
        (DifferentialGeometry.Topology.standardThreeSphereLift.{0}).Carrier
        (DifferentialGeometry.Topology.standardThreeSphereLift.{0}).orientation e e' := by
  let M : DifferentialGeometry.Topology.ClosedOrientedManifold.{0} 3 :=
    DifferentialGeometry.Topology.standardThreeSphereLift.{0}.toClosedOrientedManifold
  let c : DifferentialGeometry.Topology.OrientedBallChart M :=
    DifferentialGeometry.Topology.orientedBallChart
      DifferentialGeometry.Topology.standardThreeSphereLift.{0}
  set s : ThreeSpace := (3 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) with hsdef
  have hnorm : ‖s‖ = 3 / 2 := by
    rw [hsdef, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    simp
  have hs : ‖s‖ + 2 * (1 / 8 : ℝ) ≤ 2 := by rw [hnorm]; norm_num
  have hbig : 1 + (1 / 8 : ℝ) < ‖s‖ := by rw [hnorm]; norm_num
  have hs0 : s ≠ 0 := by
    intro h0
    have h1 : ‖s‖ = 0 := by rw [h0, norm_zero]
    rw [hnorm] at h1
    norm_num at h1
  let d : DifferentialGeometry.Topology.OrientedBallChart M :=
    c.affine s (1 / 8) (by norm_num) hs
  have hdisj : Disjoint (c.chart '' Metric.closedBall (0 : ThreeSpace) 1)
      (d.chart '' Metric.closedBall (0 : ThreeSpace) 1) :=
    disjoint_chart_image_closedBall_affine c s (1 / 8) (by norm_num) hs hbig
  have hne : d.chart (0 : ThreeSpace) ≠ c.chart (0 : ThreeSpace) :=
    DifferentialGeometry.Topology.affine_chart_zero_ne c s (1 / 8)
      (by norm_num) hs hs0
  let e : Fin 2 → OrientedBallEmbedding M.Carrier M.orientation :=
    fun i => if i = 0 then OrientedBallEmbedding.ofOrientedBallChart c
      else OrientedBallEmbedding.ofOrientedBallChart d
  let e' : Fin 2 → OrientedBallEmbedding M.Carrier M.orientation :=
    fun i => if i = 0 then OrientedBallEmbedding.ofOrientedBallChart d
      else OrientedBallEmbedding.ofOrientedBallChart c
  have h0 : e 0 = OrientedBallEmbedding.ofOrientedBallChart c := by simp [e]
  have h1 : e 1 = OrientedBallEmbedding.ofOrientedBallChart d := by simp [e]
  have h1' : e' 1 = OrientedBallEmbedding.ofOrientedBallChart c := by simp [e']
  have h0' : e' 0 = OrientedBallEmbedding.ofOrientedBallChart d := by simp [e']
  have hchartc : (OrientedBallEmbedding.ofOrientedBallChart c).chart = c.chart := rfl
  have hchartd : (OrientedBallEmbedding.ofOrientedBallChart d).chart = d.chart := rfl
  have hswap : (fun k : Fin 2 =>
      if k = 0 then e 1 else if k = 1 then e 0 else e k) = e' := by
    funext k
    fin_cases k <;> simp [h0, h1, h0', h1']
  have hdisj_e : Pairwise fun i j : Fin 2 =>
      Disjoint ((e i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((e j).chart '' Metric.closedBall (0 : ThreeSpace) 1) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa [h0, h1, hchartc, hchartd] using hdisj
    · simpa [h0, h1, hchartc, hchartd] using hdisj.symm
    · exact absurd rfl hij
  have hdisj_e' : Pairwise fun i j : Fin 2 =>
      Disjoint ((e' i).chart '' Metric.closedBall (0 : ThreeSpace) 1)
        ((e' j).chart '' Metric.closedBall (0 : ThreeSpace) 1) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa [h0', h1', hchartc, hchartd] using hdisj.symm
    · simpa [h0', h1', hchartc, hchartd] using hdisj
    · exact absurd rfl hij
  refine ⟨e, e', ?_, ?_, ?_⟩
  · exact hdisj_e
  · exact hdisj_e'
  · rw [← hswap]
    refine not_supportedBallEmbeddingIsotopy_swap e 0 1 (by decide) ?_
    simpa [h0, h1, hchartc, hchartd] using hne.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_supportedBallEmbeddingIsotopy_standardThreeSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_supportedBallEmbeddingIsotopy_standardThreeSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_supportedBallEmbeddingIsotopy_standardThreeSphere ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_supportedBallEmbeddingIsotopy_standardThreeSphere

theorem not_forall_supportedBallEmbeddingIsotopy :
    ¬ (∀ (ι : Type) [Fintype ι] (U : Type) [TopologicalSpace U]
        [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
        (o : ManifoldOrientation ThreeModel U 3) (e e' : ι → OrientedBallEmbedding U o),
        SupportedBallEmbeddingIsotopy ι U o e e') := by
  rintro h
  obtain ⟨e, e', -, -, hbad⟩ := not_supportedBallEmbeddingIsotopy_standardThreeSphere
  exact hbad (h (Fin 2) _ _ e e')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_forall_supportedBallEmbeddingIsotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_forall_supportedBallEmbeddingIsotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_forall_supportedBallEmbeddingIsotopy ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_forall_supportedBallEmbeddingIsotopy

theorem not_forall_supportedBallEmbeddingIsotopy_universal :
    ¬ (∀ (ι : Type u) [Fintype ι] (U : Type u) [TopologicalSpace U]
        [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U] [T2Space U] [ConnectedSpace U]
        (o : ManifoldOrientation ThreeModel U 3) (e e' : ι → OrientedBallEmbedding U o),
        SupportedBallEmbeddingIsotopy ι U o e e') := by
  rintro h
  let M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3 :=
    DifferentialGeometry.Topology.standardThreeSphereLift.{u}.toClosedOrientedManifold
  let c : DifferentialGeometry.Topology.OrientedBallChart M :=
    DifferentialGeometry.Topology.orientedBallChart
      DifferentialGeometry.Topology.standardThreeSphereLift.{u}
  set s : ThreeSpace := (3 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) with hsdef
  have hnorm : ‖s‖ = 3 / 2 := by
    rw [hsdef, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    simp
  have hs : ‖s‖ + 2 * (1 / 8 : ℝ) ≤ 2 := by rw [hnorm]; norm_num
  have hbig : 1 + (1 / 8 : ℝ) < ‖s‖ := by rw [hnorm]; norm_num
  have hs0 : s ≠ 0 := by
    intro h0
    have h1 : ‖s‖ = 0 := by rw [h0, norm_zero]
    rw [hnorm] at h1
    norm_num at h1
  let d : DifferentialGeometry.Topology.OrientedBallChart M :=
    c.affine s (1 / 8) (by norm_num) hs
  have hne : d.chart (0 : ThreeSpace) ≠ c.chart (0 : ThreeSpace) :=
    DifferentialGeometry.Topology.affine_chart_zero_ne c s (1 / 8) (by norm_num) hs hs0
  let e : ULift.{u, 0} (Fin 2) → OrientedBallEmbedding M.Carrier M.orientation :=
    fun i => if i.down = 0 then OrientedBallEmbedding.ofOrientedBallChart c
      else OrientedBallEmbedding.ofOrientedBallChart d
  let e' : ULift.{u, 0} (Fin 2) → OrientedBallEmbedding M.Carrier M.orientation :=
    fun i => if i.down = 0 then OrientedBallEmbedding.ofOrientedBallChart d
      else OrientedBallEmbedding.ofOrientedBallChart c
  have hswap : (fun k : ULift.{u, 0} (Fin 2) => if k = ULift.up 0 then e (ULift.up 1)
      else if k = ULift.up 1 then e (ULift.up 0) else e k) = e' := by
    funext k
    obtain ⟨n⟩ := k
    fin_cases n <;> simp [e, e']
  have hfrontier := h (ULift.{u, 0} (Fin 2)) M.Carrier M.orientation e e'
  rw [← hswap] at hfrontier
  refine not_supportedBallEmbeddingIsotopy_swap e (ULift.up 0) (ULift.up 1) (by simp) ?_ hfrontier
  have h0 : e (ULift.up 0) = OrientedBallEmbedding.ofOrientedBallChart c := by simp [e]
  have h1 : e (ULift.up 1) = OrientedBallEmbedding.ofOrientedBallChart d := by simp [e]
  have hchartc : (OrientedBallEmbedding.ofOrientedBallChart c).chart = c.chart := rfl
  have hchartd : (OrientedBallEmbedding.ofOrientedBallChart d).chart = d.chart := rfl
  simpa [h0, h1, hchartc, hchartd] using hne.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_forall_supportedBallEmbeddingIsotopy_universal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_forall_supportedBallEmbeddingIsotopy_universal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_forall_supportedBallEmbeddingIsotopy_universal ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_forall_supportedBallEmbeddingIsotopy_universal

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
