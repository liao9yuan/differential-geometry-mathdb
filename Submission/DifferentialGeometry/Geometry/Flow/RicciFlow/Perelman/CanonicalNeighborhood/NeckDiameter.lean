import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointNeckArmFrontier
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CollarDiameter

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Submission.Set
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem collar_edist_comm (g : SmoothRiemannianMetric I3 M) (x y : M) :
    riemannianEDistOf (I := I3) g x y = riemannianEDistOf (I := I3) g y x := by
  let : Bundle.RiemannianBundle (TangentSpace I3 : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_comm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_edist_comm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_edist_comm target :: scope.openDecls } }

omit [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem collar_edist_triangle (g : SmoothRiemannianMetric I3 M) (x y z : M) :
    riemannianEDistOf (I := I3) g x z ≤
      riemannianEDistOf (I := I3) g x y + riemannianEDistOf (I := I3) g y z := by
  let : Bundle.RiemannianBundle (TangentSpace I3 : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_triangle

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_edist_triangle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_edist_triangle target :: scope.openDecls } }

theorem collarSectionDiameter_exists :
    ∃ D : ℝ, 0 < D ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (C : CylinderReference) (h : ℝ → SmoothRiemannianMetric IC Cylinder)
        (g : ℝ → SmoothRiemannianMetric I3 M) (F : PartialDiffeomorph IC I3 Cylinder M ∞)
        (U : Set Cylinder) (times : Set ℝ) (order : ℕ) (eps z : ℝ),
        MetricComparisonOn h g F U times order eps → h 0 = C.metric 0 → 0 ≤ eps →
        eps ≤ 1 → 0 ∈ times → U ⊆ F.source → (∀ y : Sphere 2, (y, z) ∈ U) →
          ∀ x y : Sphere 2,
          riemannianEDistOf (g 0) (F (x, z)) (F (y, z)) ≤ ENNReal.ofReal D := by
  obtain ⟨B, hB, hpaths⟩ := exists_roundSphere_path_length_bound
  refine ⟨2 * B, by positivity, ?_⟩
  intro M _ _ _ _ _ C h g F U times order eps z cmp hmetric heps heps1 hzero hsource hlevel x y
  obtain ⟨gamma, hstart, hend, hgamma, hlen⟩ := hpaths x y
  have hcyl : ContMDiffOn 𝓘(ℝ, ℝ) IC 1 (fun s : ℝ => (gamma s, z)) (Set.Icc 0 1) :=
    hgamma.prodMk contMDiffOn_const
  have hinside : ∀ s ∈ Set.Icc (0 : ℝ) 1, (gamma s, z) ∈ U := fun s _ => hlevel (gamma s)
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) I3 1
      ((F : Cylinder → M) ∘ (fun s : ℝ => (gamma s, z))) (Set.Icc 0 1) :=
    (F.contMDiffOn_toFun.of_le (by simp)).comp hcyl fun s hs => hsource (hinside s hs)
  have hdist := edistOf_le_metricPathELength (g 0) (by norm_num : (0 : ℝ) ≤ 1) hcomp
  simp only [Function.comp_apply, hstart, hend] at hdist
  have hlen' := (collar_pathELength_bounds C g F cmp hmetric heps heps1 hzero hsource
    hcyl hinside).2
  have htrans := C.transverse_length_le z hgamma
  have hsqrt : ENNReal.ofReal (Real.sqrt (1 + eps)) ≤ ENNReal.ofReal (Real.sqrt 2) :=
    ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (by linarith))
  calc riemannianEDistOf (g 0) (F (x, z)) (F (y, z))
      ≤ metricPathELength (g 0) ((F : Cylinder → M) ∘
          (fun s : ℝ => (gamma s, z))) 0 1 := hdist
    _ ≤ ENNReal.ofReal (Real.sqrt (1 + eps)) *
          metricPathELength (C.metric 0) (fun s : ℝ => (gamma s, z)) 0 1 := hlen'
    _ ≤ ENNReal.ofReal (Real.sqrt 2) *
          (ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal B) :=
          mul_le_mul' hsqrt (htrans.trans (mul_le_mul' le_rfl hlen.le))
    _ = ENNReal.ofReal (2 * B) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← pow_two,
            Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), ← ENNReal.ofReal_mul (by norm_num)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collarSectionDiameter_exists then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collarSectionDiameter_exists"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collarSectionDiameter_exists ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collarSectionDiameter_exists

theorem collarAxialBound_exists :
    ∃ V : ℝ, 0 < V ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (C : CylinderReference) (g : ℝ → SmoothRiemannianMetric I3 M)
        (F : PartialDiffeomorph IC I3 Cylinder M ∞) (U : Set Cylinder) (times : Set ℝ)
        (order : ℕ) (eps : ℝ) (h : ℝ → SmoothRiemannianMetric IC Cylinder),
        MetricComparisonOn h g F U times order eps → h 0 = C.metric 0 → 0 ≤ eps →
        eps ≤ 1 → 0 ∈ times → U ⊆ F.source →
        Set.univ ×ˢ Set.Icc (-10 : ℝ) 10 ⊆ U →
          ∀ (p : Sphere 2) (k : ℝ), |k| ≤ 10 →
            riemannianEDistOf (g 0) (F (p, k)) (F (p, 0)) ≤ ENNReal.ofReal V := by
  refine ⟨Real.sqrt 2 * 10, by positivity, ?_⟩
  intro M _ _ _ _ _ C g F U times order eps h cmp hmetric heps heps1 hzero hsource hslab p k hk
  refine (collar_axial_edist_le (M := M) C g F cmp hmetric heps hzero hsource hslab p
    (Set.mem_Icc.mpr (abs_le.mp hk))).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  calc Real.sqrt (1 + eps) * |k| ≤ Real.sqrt 2 * |k| :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) (abs_nonneg k)
    _ ≤ Real.sqrt 2 * 10 := mul_le_mul_of_nonneg_left hk (Real.sqrt_nonneg 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collarAxialBound_exists then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collarAxialBound_exists"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collarAxialBound_exists ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collarAxialBound_exists

theorem neckAxialBound_holds : NeckAxialBound.{u} := by
  obtain ⟨V, hV, hax⟩ := collarAxialBound_exists
  refine ⟨V, hV, ?_⟩
  intro M _ _ _ _ _ J S eps x t neck p k hk
  have heps1 : eps ≤ 1 := by linarith [neck.eps_small]
  have h11 : (11 : ℝ) < eps⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ neck.eps_pos]
    linarith [neck.eps_small]
  have hslab : Set.univ ×ˢ Set.Icc (-10 : ℝ) 10 ⊆
      (Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹ : Set Cylinder) := by
    rintro ⟨u, v⟩ ⟨-, hv⟩
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hv
    exact ⟨mem_univ _, by constructor <;> linarith⟩
  exact hax M neck.cylinder (rescaledMetric S t (S.scalar t x) neck.Q_pos) neck.map
    (Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹) (Set.Icc (-1) 0) ⌈eps⁻¹⌉₊ eps
    neck.cylinder.metric neck.comparison rfl neck.eps_pos.le heps1 (by simp) neck.domain
    hslab p k hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckAxialBound_holds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckAxialBound_holds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckAxialBound_holds ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckAxialBound_holds

theorem neckCoreDiameterBound_holds : NeckCoreDiameterBound.{u} := by
  obtain ⟨D, hD, hsec⟩ := collarSectionDiameter_exists
  obtain ⟨V, hV, hax⟩ := collarAxialBound_exists
  refine ⟨D + 2 * V, by positivity, ?_⟩
  intro M _ _ _ _ _ J S eps x t neck y hy z hz
  obtain ⟨vx, hvx, rfl⟩ := hy
  obtain ⟨wx, hwx, rfl⟩ := hz
  have heps1 : eps ≤ 1 := by linarith [neck.eps_small]
  have h11 : (11 : ℝ) < eps⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ neck.eps_pos]
    linarith [neck.eps_small]
  have hU : Set.univ ×ˢ Set.Icc (-10 : ℝ) 10 ⊆
      (Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹ : Set Cylinder) := by
    rintro ⟨u, v⟩ ⟨-, hv⟩
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hv
    exact ⟨mem_univ _, by constructor <;> linarith⟩
  have hzero : (0 : ℝ) ∈ Set.Ioo (-eps⁻¹) eps⁻¹ := by constructor <;> linarith
  have hlevel : ∀ w : Sphere 2,
      (w, (0 : ℝ)) ∈ (Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹ : Set Cylinder) :=
    fun w => ⟨mem_univ _, hzero⟩
  have hvV := hax M neck.cylinder (rescaledMetric S t (S.scalar t x) neck.Q_pos) neck.map
    (Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹) (Set.Icc (-1) 0) ⌈eps⁻¹⌉₊ eps
    neck.cylinder.metric neck.comparison rfl neck.eps_pos.le heps1 (by simp) neck.domain hU
    vx.1 vx.2
    (abs_le.mpr hvx.2)
  have hwV : riemannianEDistOf (rescaledMetric S t (S.scalar t x) neck.Q_pos 0)
      (neck.map (wx.1, 0)) (neck.map wx) ≤ ENNReal.ofReal V :=
    (collar_edist_comm (rescaledMetric S t (S.scalar t x) neck.Q_pos 0) (neck.map (wx.1, 0))
      (neck.map wx)).trans_le
      (hax M neck.cylinder (rescaledMetric S t (S.scalar t x) neck.Q_pos) neck.map
        (Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹) (Set.Icc (-1) 0) ⌈eps⁻¹⌉₊ eps
        neck.cylinder.metric neck.comparison rfl neck.eps_pos.le heps1 (by simp) neck.domain
        hU wx.1 wx.2 (abs_le.mpr hwx.2))
  have hsection := hsec M neck.cylinder neck.cylinder.metric
    (rescaledMetric S t (S.scalar t x) neck.Q_pos) neck.map
    (Set.univ ×ˢ Set.Ioo (-eps⁻¹) eps⁻¹) (Set.Icc (-1) 0) ⌈eps⁻¹⌉₊ eps 0
    neck.comparison rfl neck.eps_pos.le heps1 (by simp) neck.domain hlevel vx.1 wx.1
  have htri := collar_edist_triangle (rescaledMetric S t (S.scalar t x) neck.Q_pos 0)
    (neck.map vx) (neck.map (vx.1, 0)) (neck.map wx)
  have htri' := collar_edist_triangle (rescaledMetric S t (S.scalar t x) neck.Q_pos 0)
    (neck.map (vx.1, 0)) (neck.map (wx.1, 0)) (neck.map wx)
  have hsum : ENNReal.ofReal V + (ENNReal.ofReal D + ENNReal.ofReal V) =
      ENNReal.ofReal (D + 2 * V) := by
    rw [← add_assoc, ← ENNReal.ofReal_add hV.le hD.le,
      ← ENNReal.ofReal_add (by linarith : (0 : ℝ) ≤ V + D) hV.le]
    congr 1
    ring
  refine htri.trans ((add_le_add hvV (htri'.trans (add_le_add hsection hwV))).trans hsum.le)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckCoreDiameterBound_holds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckCoreDiameterBound_holds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckCoreDiameterBound_holds ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neckCoreDiameterBound_holds


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
