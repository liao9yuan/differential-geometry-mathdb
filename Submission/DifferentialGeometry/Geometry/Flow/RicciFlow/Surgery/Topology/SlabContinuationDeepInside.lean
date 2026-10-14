import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabPointPicking
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformKappaCanonicalThreshold

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem exists_bad_point_with_good_above_double {Good : P.Carrier → ℝ → Prop} {q T η : ℝ}
    (hq : 0 ≤ q) (hT : a ≤ T)
    (hbad : ∃ (x : P.Carrier) (t : ℝ), T ≤ t ∧ t < T + η ∧ t < s ∧ q < G.flow.scalar t x ∧
      ¬ Good x t) :
    ∃ (x' : P.Carrier) (t' : ℝ), T ≤ t' ∧ t' < T + η ∧ t' < s ∧ q < G.flow.scalar t' x' ∧
      ¬ Good x' t' ∧
      ∀ (y : P.Carrier) (t : ℝ), T ≤ t → t ≤ t' →
        2 * G.flow.scalar t' x' ≤ G.flow.scalar t y → Good y t := by
  obtain ⟨x₀, t₀, hT₀, hη₀, hs₀, hq₀, hbad₀⟩ := hbad
  obtain ⟨K, hK⟩ := G.exists_forall_Icc_scalar_le hs₀
  set B : Set ℝ := {r | ∃ (x : P.Carrier) (t : ℝ), T ≤ t ∧ t ≤ t₀ ∧ q < G.flow.scalar t x ∧
      ¬ Good x t ∧ G.flow.scalar t x = r} with hB
  have hmem : G.flow.scalar t₀ x₀ ∈ B := by
    rw [hB]
    exact ⟨x₀, t₀, hT₀, le_rfl, hq₀, hbad₀, rfl⟩
  have hbdd : BddAbove B := by
    refine ⟨K, fun r hr => ?_⟩
    rw [hB] at hr
    obtain ⟨x, t, hTt, htt₀, -, -, rfl⟩ := hr
    exact hK t ⟨hT.trans hTt, htt₀⟩ x
  have hle : G.flow.scalar t₀ x₀ ≤ _root_.SupSet.sSup B := le_csSup hbdd hmem
  have hhalf : _root_.SupSet.sSup B / 2 < _root_.SupSet.sSup B := by linarith
  obtain ⟨r, hrB, hr⟩ := exists_lt_of_lt_csSup ⟨_, hmem⟩ hhalf
  rw [hB] at hrB
  obtain ⟨x', t', hTt', ht't₀, hq', hbad', rfl⟩ := hrB
  refine ⟨x', t', hTt', ht't₀.trans_lt hη₀, ht't₀.trans_lt hs₀, hq', hbad', ?_⟩
  intro y t hTt htt' hdouble
  by_contra hnc
  have hyB : G.flow.scalar t y ∈ B := by
    rw [hB]
    exact ⟨y, t, hTt, htt'.trans ht't₀, by linarith, hnc, rfl⟩
  have hyle := le_csSup hbdd hyB
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_bad_point_with_good_above_double then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_bad_point_with_good_above_double"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_bad_point_with_good_above_double ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_bad_point_with_good_above_double

theorem exists_bad_point_scaled_elapsed_lt_with_good_above_double
    {Good : P.Carrier → ℝ → Prop} {q T β η : ℝ} (hq : 0 ≤ q) (hT : a ≤ T) (hTs : T < s)
    (hβ : 0 < β) (hη : 0 < η)
    (hbad : ∀ η' : ℝ, 0 < η' → ∃ (x : P.Carrier) (t : ℝ), T ≤ t ∧ t < T + η' ∧ t < s ∧
      q < G.flow.scalar t x ∧ ¬ Good x t) :
    ∃ (x' : P.Carrier) (t' : ℝ), T ≤ t' ∧ t' < T + η ∧ t' < s ∧ q < G.flow.scalar t' x' ∧
      ¬ Good x' t' ∧ G.flow.scalar t' x' * (t' - T) < β ∧
      ∀ (y : P.Carrier) (t : ℝ), T ≤ t → t ≤ t' →
        2 * G.flow.scalar t' x' ≤ G.flow.scalar t y → Good y t := by
  have hb : (T + s) / 2 < s := by linarith
  obtain ⟨K, hK⟩ := G.exists_forall_Icc_scalar_le hb
  have hK' : 0 < _root_.Max.max K 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hη' : 0 < _root_.Min.min η (_root_.Min.min ((T + s) / 2 - T) (β / _root_.Max.max K 1)) :=
    lt_min hη (lt_min (by linarith) (div_pos hβ hK'))
  obtain ⟨x', t', hTt', ht', hs', hq', hbad', habove⟩ :=
    G.exists_bad_point_with_good_above_double hq hT (hbad _ hη')
  have h1 := min_le_left η (_root_.Min.min ((T + s) / 2 - T) (β / _root_.Max.max K 1))
  have h2 := min_le_right η (_root_.Min.min ((T + s) / 2 - T) (β / _root_.Max.max K 1))
  have h3 := min_le_left ((T + s) / 2 - T) (β / _root_.Max.max K 1)
  have h4 := min_le_right ((T + s) / 2 - T) (β / _root_.Max.max K 1)
  have hR : G.flow.scalar t' x' ≤ _root_.Max.max K 1 :=
    (hK t' ⟨hT.trans hTt', by linarith⟩ x').trans (le_max_left _ _)
  refine ⟨x', t', hTt', by linarith, hs', hq', hbad', ?_, habove⟩
  calc G.flow.scalar t' x' * (t' - T) ≤ _root_.Max.max K 1 * (t' - T) :=
        mul_le_mul_of_nonneg_right hR (sub_nonneg.2 hTt')
    _ < _root_.Max.max K 1 * (β / _root_.Max.max K 1) := mul_lt_mul_of_pos_left (by linarith) hK'
    _ = β := mul_div_cancel₀ β hK'.ne'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_bad_point_scaled_elapsed_lt_with_good_above_double then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_bad_point_scaled_elapsed_lt_with_good_above_double"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_bad_point_scaled_elapsed_lt_with_good_above_double ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_bad_point_scaled_elapsed_lt_with_good_above_double

theorem exists_noncanonical_point_scaled_elapsed_lt {ε C1 C2 q T β η : ℝ} (hq : 0 ≤ q)
    (hT : a ≤ T) (hTs : T < s) (hβ : 0 < β) (hη : 0 < η)
    (hbad : ∀ η' : ℝ, 0 < η' → ∃ (x : P.Carrier) (t : ℝ), T ≤ t ∧ t < T + η' ∧ t < s ∧
      q < G.flow.scalar t x ∧ ¬ ∃ W : CanonicalWitness G.flow ε C1 C2 x t,
        W.capTubeHasNeckChart ε) :
    ∃ (x' : P.Carrier) (t' : ℝ), T ≤ t' ∧ t' < T + η ∧ t' < s ∧ q < G.flow.scalar t' x' ∧
      (¬ ∃ W : CanonicalWitness G.flow ε C1 C2 x' t', W.capTubeHasNeckChart ε) ∧
      G.flow.scalar t' x' * (t' - T) < β ∧
      ∀ (y : P.Carrier) (t : ℝ), T ≤ t → t ≤ t' →
        2 * G.flow.scalar t' x' ≤ G.flow.scalar t y →
          ∃ W : CanonicalWitness G.flow ε C1 C2 y t, W.capTubeHasNeckChart ε :=
  G.exists_bad_point_scaled_elapsed_lt_with_good_above_double
    (Good := fun x t => ∃ W : CanonicalWitness G.flow ε C1 C2 x t, W.capTubeHasNeckChart ε)
    hq hT hTs hβ hη hbad

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_noncanonical_point_scaled_elapsed_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_noncanonical_point_scaled_elapsed_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_noncanonical_point_scaled_elapsed_lt ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_noncanonical_point_scaled_elapsed_lt

theorem exists_aged_noncanonical_point_scaled_elapsed_lt {ε C1 C2 q τmin T β η : ℝ}
    (hq : 0 ≤ q) (hT : a ≤ T) (hTs : T < s) (hβ : 0 < β) (hη : 0 < η)
    (hbad : ∀ η' : ℝ, 0 < η' → ∃ (x : P.Carrier) (t : ℝ), T ≤ t ∧ t < T + η' ∧ t < s ∧
      q < G.flow.scalar t x ∧ τmin ≤ G.flow.scalar t x * (t - a) ∧
      ¬ ∃ W : CanonicalWitness G.flow ε C1 C2 x t, W.capTubeHasNeckChart ε) :
    ∃ (x' : P.Carrier) (t' : ℝ), T ≤ t' ∧ t' < T + η ∧ t' < s ∧ q < G.flow.scalar t' x' ∧
      τmin ≤ G.flow.scalar t' x' * (t' - a) ∧
      (¬ ∃ W : CanonicalWitness G.flow ε C1 C2 x' t', W.capTubeHasNeckChart ε) ∧
      G.flow.scalar t' x' * (t' - T) < β ∧
      ∀ (y : P.Carrier) (t : ℝ), T ≤ t → t ≤ t' →
        2 * G.flow.scalar t' x' ≤ G.flow.scalar t y → τmin ≤ G.flow.scalar t y * (t - a) →
          ∃ W : CanonicalWitness G.flow ε C1 C2 y t, W.capTubeHasNeckChart ε := by
  obtain ⟨x', t', hTt', ht', hs', hq', hbad', hβ', habove⟩ :=
    G.exists_bad_point_scaled_elapsed_lt_with_good_above_double
      (Good := fun x t => τmin ≤ G.flow.scalar t x * (t - a) →
        ∃ W : CanonicalWitness G.flow ε C1 C2 x t, W.capTubeHasNeckChart ε)
      hq hT hTs hβ hη (fun η' hη' => by
        obtain ⟨x, t, h1, h2, h3, h4, h5, h6⟩ := hbad η' hη'
        exact ⟨x, t, h1, h2, h3, h4, fun h => h6 (h h5)⟩)
  have hage : τmin ≤ G.flow.scalar t' x' * (t' - a) := by
    by_contra h
    exact hbad' fun h' => absurd h' h
  exact ⟨x', t', hTt', ht', hs', hq', hage, fun h => hbad' fun _ => h, hβ', habove⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_aged_noncanonical_point_scaled_elapsed_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_aged_noncanonical_point_scaled_elapsed_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_aged_noncanonical_point_scaled_elapsed_lt ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_aged_noncanonical_point_scaled_elapsed_lt

theorem exists_uniform_canonicalOn_of_parabolically_noncollapsed {eps : ℝ} (heps : 0 < eps)
    (hsmall : eps < 1 / 11) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ kappa : ℝ, 0 < kappa → ∀ rho : ℝ, 0 < rho → ∀ Phi : ℝ → ℝ,
        Perelman.AdmissiblePinchingFunction Phi →
        ∃ Q₀ theta : ℝ, 0 < Q₀ ∧ 0 < theta ∧
          ∀ (P : OrientedThreeStage.{u}) (a s : ℝ) (G : P.IncomingSlab a s)
            (qcan τmin t₀ η : ℝ), Q₀ ≤ qcan →
            Perelman.PhiAlmostNonnegative G.flow (_root_.Set.Ico a s) Phi →
            (∀ (τ : (RealTimeInterval.closedOpen a s G.lt).FlowTime)
              (B : Perelman.FlowMetricBall G.flow τ), (τ : ℝ) < t₀ + η → B.radius ≤ rho →
                B.IsParabolicallyRmControlled → B.IsKappaNoncollapsed kappa) →
            (∀ (x : P.Carrier) (t : ℝ), t₀ ≤ t → t < t₀ + η → t < s →
              qcan < G.flow.scalar t x → τmin ≤ G.flow.scalar t x * (t - a) →
                a ≤ t - theta / G.flow.scalar t x) →
            G.CanonicalOn eps C C qcan τmin t₀ η := by
  obtain ⟨C, hC, -, hU⟩ :=
    exists_uniform_canonical_threshold_of_parabolically_noncollapsed.{u} heps hsmall
  refine ⟨C, hC, fun kappa hk rho hr Phi hPhi => ?_⟩
  obtain ⟨Q₀, theta, hQ, hθ, h⟩ := hU kappa hk rho hr Phi hPhi
  refine ⟨Q₀, theta, hQ, hθ, fun P a s G qcan τmin t₀ η hq hpinch hnc hwin => ?_⟩
  intro y t _ ht₀ htη hts hR hage
  have hw := hwin y t ht₀ htη hts hR hage
  exact h P a s G y t hts (hq.trans hR.le) hw
    (fun v hv z => hpinch v ⟨hw.trans hv.1, hv.2.trans_lt hts⟩ z)
    (fun τ B _ h2 h3 h4 => hnc τ B (h2.trans_lt htη) h3 h4)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_uniform_canonicalOn_of_parabolically_noncollapsed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_uniform_canonicalOn_of_parabolically_noncollapsed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_uniform_canonicalOn_of_parabolically_noncollapsed ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_uniform_canonicalOn_of_parabolically_noncollapsed

theorem exists_uniform_canonicalOn_of_parabolically_noncollapsed_of_le_age {eps : ℝ}
    (heps : 0 < eps) (hsmall : eps < 1 / 11) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ kappa : ℝ, 0 < kappa → ∀ rho : ℝ, 0 < rho → ∀ Phi : ℝ → ℝ,
        Perelman.AdmissiblePinchingFunction Phi →
        ∃ Q₀ theta : ℝ, 0 < Q₀ ∧ 0 < theta ∧
          ∀ (P : OrientedThreeStage.{u}) (a s : ℝ) (G : P.IncomingSlab a s)
            (qcan τmin t₀ η : ℝ), Q₀ ≤ qcan → theta ≤ τmin →
            Perelman.PhiAlmostNonnegative G.flow (_root_.Set.Ico a s) Phi →
            (∀ (τ : (RealTimeInterval.closedOpen a s G.lt).FlowTime)
              (B : Perelman.FlowMetricBall G.flow τ), (τ : ℝ) < t₀ + η → B.radius ≤ rho →
                B.IsParabolicallyRmControlled → B.IsKappaNoncollapsed kappa) →
            G.CanonicalOn eps C C qcan τmin t₀ η := by
  obtain ⟨C, hC, hmain⟩ := exists_uniform_canonicalOn_of_parabolically_noncollapsed.{u} heps hsmall
  refine ⟨C, hC, fun kappa hk rho hr Phi hPhi => ?_⟩
  obtain ⟨Q₀, theta, hQ, hθ, h⟩ := hmain kappa hk rho hr Phi hPhi
  refine ⟨Q₀, theta, hQ, hθ, fun P a s G qcan τmin t₀ η hq hθτ hpinch hnc => ?_⟩
  refine h P a s G qcan τmin t₀ η hq hpinch hnc fun x t _ _ _ hR hage => ?_
  have hRpos : 0 < G.flow.scalar t x := hQ.trans_le (hq.trans hR.le)
  have h1 : theta / G.flow.scalar t x ≤ τmin / G.flow.scalar t x :=
    div_le_div_of_nonneg_right hθτ hRpos.le
  have h2 : τmin / G.flow.scalar t x ≤ t - a := by
    rw [div_le_iff₀ hRpos]
    linarith
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_uniform_canonicalOn_of_parabolically_noncollapsed_of_le_age then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_uniform_canonicalOn_of_parabolically_noncollapsed_of_le_age"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_uniform_canonicalOn_of_parabolically_noncollapsed_of_le_age ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_uniform_canonicalOn_of_parabolically_noncollapsed_of_le_age

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
