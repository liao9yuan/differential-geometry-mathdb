-- Modified 2026-04-28: updated internal import paths for project namespace
-- Modified 2026-05-16: style-warning cleanup
import Submission.DifferentialGeometry.External.DeGiorgi.Oscillation.BMO

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Chapter 02: Campanato and Holder Theory

This module packages the Campanato seminorm machinery and the equivalence with
Holder regularity.
-/

noncomputable section


open _root_.MeasureTheory _root_.Metric _root_.Filter _root_.Topology
open scoped _root_.ENNReal _root_.NNReal

namespace DeGiorgi

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-! ## Campanato Characterization of Hölder Spaces -/

/-- Admissible sub-balls of `Metric.ball x₀ R` for the Campanato seminorm. -/
def CampanatoBall (x₀ : E) (R : ℝ) :=
  {p : E × ℝ // 0 < p.2 ∧ p.2 ≤ R ∧ Metric.ball p.1 p.2 ⊆ Metric.ball x₀ R}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.CampanatoBall then
    throwError "Refusing to shadow existing declaration DeGiorgi.CampanatoBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.CampanatoBall ``Submission.DeGiorgi.CampanatoBall

namespace CampanatoBall

def center {x₀ : E} {R : ℝ} (b : CampanatoBall x₀ R) : E := b.1.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.CampanatoBall.center then
    throwError "Refusing to shadow existing declaration DeGiorgi.CampanatoBall.center"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.CampanatoBall.center ``Submission.DeGiorgi.CampanatoBall.center

def radius {x₀ : E} {R : ℝ} (b : CampanatoBall x₀ R) : ℝ := b.1.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.CampanatoBall.radius then
    throwError "Refusing to shadow existing declaration DeGiorgi.CampanatoBall.radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.CampanatoBall.radius ``Submission.DeGiorgi.CampanatoBall.radius

lemma radius_pos {x₀ : E} {R : ℝ} (b : CampanatoBall x₀ R) : 0 < b.radius := b.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.CampanatoBall.radius_pos then
    throwError "Refusing to shadow existing declaration DeGiorgi.CampanatoBall.radius_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.CampanatoBall.radius_pos ``Submission.DeGiorgi.CampanatoBall.radius_pos

lemma radius_le {x₀ : E} {R : ℝ} (b : CampanatoBall x₀ R) : b.radius ≤ R := b.2.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.CampanatoBall.radius_le then
    throwError "Refusing to shadow existing declaration DeGiorgi.CampanatoBall.radius_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.CampanatoBall.radius_le ``Submission.DeGiorgi.CampanatoBall.radius_le

lemma subset_ball {x₀ : E} {R : ℝ} (b : CampanatoBall x₀ R) :
    Metric.ball b.center b.radius ⊆ Metric.ball x₀ R := b.2.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.CampanatoBall.subset_ball then
    throwError "Refusing to shadow existing declaration DeGiorgi.CampanatoBall.subset_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.CampanatoBall.subset_ball ``Submission.DeGiorgi.CampanatoBall.subset_ball

end CampanatoBall

/-- The Campanato seminorm on a ball B_R(x₀):
sup_{B ⊆ B_R} ⨍_B |u - (u)_B|. -/
noncomputable def campanatoBallValue
    (u : E → ℝ) (α : ℝ) {x₀ : E} {R : ℝ} (b : CampanatoBall x₀ R) : ℝ :=
  (CampanatoBall.radius b)⁻¹ ^ α *
    ⨍ x in Metric.ball (CampanatoBall.center b) (CampanatoBall.radius b),
      |u x - ⨍ z in Metric.ball (CampanatoBall.center b) (CampanatoBall.radius b), u z| ∂volume

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.campanatoBallValue then
    throwError "Refusing to shadow existing declaration DeGiorgi.campanatoBallValue"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.campanatoBallValue ``Submission.DeGiorgi.campanatoBallValue

noncomputable def campanatoSeminorm (u : E → ℝ) (x₀ : E) (R : ℝ) (α : ℝ) : ℝ :=
  sSup (Set.range (campanatoBallValue u α (x₀ := x₀) (R := R)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.campanatoSeminorm then
    throwError "Refusing to shadow existing declaration DeGiorgi.campanatoSeminorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.campanatoSeminorm ``Submission.DeGiorgi.campanatoSeminorm

lemma campanatoBallValue_nonneg
    {u : E → ℝ} {α : ℝ} {x₀ : E} {R : ℝ} (b : CampanatoBall x₀ R) :
    0 ≤ campanatoBallValue u α b := by
  rcases b with ⟨⟨x, r⟩, ⟨hr, hrR, hsub⟩⟩
  unfold campanatoBallValue
  have hAvg_nonneg :
      0 ≤ ⨍ y in Metric.ball x r,
          |u y - ⨍ z in Metric.ball x r, u z| ∂volume := by
    rw [MeasureTheory.setAverage_eq]
    refine mul_nonneg ?_ ?_
    · positivity
    · exact MeasureTheory.setIntegral_nonneg measurableSet_ball fun y hy ↦ abs_nonneg _
  exact mul_nonneg (Real.rpow_nonneg (inv_nonneg.mpr hr.le) _) hAvg_nonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.campanatoBallValue_nonneg then
    throwError "Refusing to shadow existing declaration DeGiorgi.campanatoBallValue_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.campanatoBallValue_nonneg ``Submission.DeGiorgi.campanatoBallValue_nonneg

/-- Expanded local form of a Campanato bound on `Metric.ball x₀ R`. -/
def HasCampanatoBound (u : E → ℝ) (x₀ : E) (R α C : ℝ) : Prop :=
  ∀ b : CampanatoBall x₀ R,
    _root_.MeasureTheory.IntegrableOn u (Metric.ball (CampanatoBall.center b) (CampanatoBall.radius b)) _root_.MeasureTheory.MeasureSpace.volume ∧
      campanatoBallValue u α b ≤ C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.HasCampanatoBound then
    throwError "Refusing to shadow existing declaration DeGiorgi.HasCampanatoBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.HasCampanatoBound ``Submission.DeGiorgi.HasCampanatoBound

noncomputable def dyadicBallAverage (u : E → ℝ) (x : E) (ρ : ℝ) (n : ℕ) : ℝ :=
  ⨍ z in Metric.ball x (ρ / (2 : ℝ) ^ n), u z ∂volume

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.dyadicBallAverage then
    throwError "Refusing to shadow existing declaration DeGiorgi.dyadicBallAverage"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.dyadicBallAverage ``Submission.DeGiorgi.dyadicBallAverage

lemma HasCampanatoBound.integrableOn
    {u : E → ℝ} {x₀ : E} {R α C : ℝ}
    (hcamp : HasCampanatoBound u x₀ R α C) (b : CampanatoBall x₀ R) :
    IntegrableOn u (Metric.ball (CampanatoBall.center b) (CampanatoBall.radius b)) volume :=
  (hcamp b).1

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DeGiorgi.HasCampanatoBound
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.HasCampanatoBound.integrableOn then
    throwError "Refusing to shadow existing declaration DeGiorgi.HasCampanatoBound.integrableOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.HasCampanatoBound.integrableOn ``Submission.DeGiorgi.HasCampanatoBound.integrableOn

lemma HasCampanatoBound.ballValue_le
    {u : E → ℝ} {x₀ : E} {R α C : ℝ}
    (hcamp : HasCampanatoBound u x₀ R α C) (b : CampanatoBall x₀ R) :
    campanatoBallValue u α b ≤ C :=
  (hcamp b).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.HasCampanatoBound.ballValue_le then
    throwError "Refusing to shadow existing declaration DeGiorgi.HasCampanatoBound.ballValue_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.HasCampanatoBound.ballValue_le ``Submission.DeGiorgi.HasCampanatoBound.ballValue_le

lemma HasCampanatoBound.campanatoSeminorm_le
    {u : E → ℝ} {x₀ : E} {R α C : ℝ}
    (hcamp : HasCampanatoBound u x₀ R α C) (hR : 0 < R) :
    campanatoSeminorm u x₀ R α ≤ C := by
  let f : CampanatoBall x₀ R → ℝ := campanatoBallValue u α
  have hS_bdd : BddAbove (Set.range f) := ⟨C, by
    rintro t ⟨b, rfl⟩
    exact hcamp.ballValue_le b⟩
  have hS_nonempty : (Set.range f).Nonempty := by
    have hhalf : 0 < R / 2 := by positivity
    let b : CampanatoBall x₀ R :=
      ⟨(x₀, R / 2), ⟨hhalf, by linarith, Metric.ball_subset_ball (by linarith)⟩⟩
    exact ⟨f b, ⟨b, rfl⟩⟩
  simpa [campanatoSeminorm, f] using (csSup_le_iff hS_bdd hS_nonempty).2 (by
    rintro t ⟨b, rfl⟩
    exact hcamp.ballValue_le b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.HasCampanatoBound.campanatoSeminorm_le then
    throwError "Refusing to shadow existing declaration DeGiorgi.HasCampanatoBound.campanatoSeminorm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.HasCampanatoBound.campanatoSeminorm_le ``Submission.DeGiorgi.HasCampanatoBound.campanatoSeminorm_le

lemma HasCampanatoBound.nonneg
    {u : E → ℝ} {x₀ : E} {R α C : ℝ}
    (_hα : 0 < α) (hR : 0 < R) (hcamp : HasCampanatoBound u x₀ R α C) :
    0 ≤ C := by
  let _ := _hα
  let b : CampanatoBall x₀ R := ⟨(x₀, R), ⟨hR, le_rfl, Set.Subset.rfl⟩⟩
  exact (campanatoBallValue_nonneg b).trans (hcamp.ballValue_le b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.HasCampanatoBound.nonneg then
    throwError "Refusing to shadow existing declaration DeGiorgi.HasCampanatoBound.nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.HasCampanatoBound.nonneg ``Submission.DeGiorgi.HasCampanatoBound.nonneg

/-- A conservative Hölder constant extracted from a Campanato bound. -/
noncomputable def CCampanatoHolder (d : ℕ) (α : ℝ) : ℝ :=
  (2 : ℝ) ^ (d + 3) / (1 - (2 : ℝ) ^ (-α))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.CCampanatoHolder then
    throwError "Refusing to shadow existing declaration DeGiorgi.CCampanatoHolder"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.CCampanatoHolder ``Submission.DeGiorgi.CCampanatoHolder

lemma closedBall_ae_eq_ball_of_pos (x : E) {r : ℝ} (hr : 0 < r) :
    Metric.closedBall x r =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] Metric.ball x r := by
  by_cases hd : d = 0
  · subst hd
    have hball : Metric.ball x r = Set.univ := by
      ext y
      have hyx : y = x := Subsingleton.elim _ _
      simp [Metric.mem_ball, hyx, hr]
    have hclosed : Metric.closedBall x r = Set.univ := by
      ext y
      have hyx : y = x := Subsingleton.elim _ _
      simp [Metric.mem_closedBall, hyx, hr.le]
    simp [hball, hclosed]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) <| by
      simpa [finrank_euclideanSpace] using hdpos
    refine (_root_.MeasureTheory.ae_eq_of_subset_of_measure_ge Metric.ball_subset_closedBall ?_
      measurableSet_ball.nullMeasurableSet measure_closedBall_lt_top.ne).symm
    simpa using le_of_eq (Measure.addHaar_closedBall_eq_addHaar_ball (μ := _root_.MeasureTheory.MeasureSpace.volume) x r)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.closedBall_ae_eq_ball_of_pos then
    throwError "Refusing to shadow existing declaration DeGiorgi.closedBall_ae_eq_ball_of_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.closedBall_ae_eq_ball_of_pos ``Submission.DeGiorgi.closedBall_ae_eq_ball_of_pos

lemma setAverage_closedBall_eq_ball_of_pos
    {u : E → ℝ} (x : E) {r : ℝ} (hr : 0 < r) :
    ⨍ z in Metric.closedBall x r, u z ∂volume = ⨍ z in Metric.ball x r, u z ∂volume := by
  exact MeasureTheory.setAverage_congr (closedBall_ae_eq_ball_of_pos x hr)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.setAverage_closedBall_eq_ball_of_pos then
    throwError "Refusing to shadow existing declaration DeGiorgi.setAverage_closedBall_eq_ball_of_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.setAverage_closedBall_eq_ball_of_pos ``Submission.DeGiorgi.setAverage_closedBall_eq_ball_of_pos

lemma tendsto_dyadic_radius_nhdsWithin_zero {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun n : ℕ => ρ / (2 : ℝ) ^ n) _root_.Filter.atTop (𝓝[>] 0) := by
  refine (tendsto_nhdsWithin_iff).2 ?_
  refine ⟨?_, Eventually.of_forall ?_⟩
  · have hpow :
        Tendsto (fun n : ℕ => ((1 / 2 : ℝ) ^ n)) _root_.Filter.atTop (𝓝 (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa [div_eq_mul_inv, one_div, inv_pow, mul_assoc, mul_left_comm, mul_comm] using
      hpow.const_mul ρ
  · intro n
    show ρ / (2 : ℝ) ^ n ∈ Set.Ioi (0 : ℝ)
    simpa [Set.mem_Ioi] using (show 0 < ρ / (2 : ℝ) ^ n by positivity)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.tendsto_dyadic_radius_nhdsWithin_zero then
    throwError "Refusing to shadow existing declaration DeGiorgi.tendsto_dyadic_radius_nhdsWithin_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.tendsto_dyadic_radius_nhdsWithin_zero ``Submission.DeGiorgi.tendsto_dyadic_radius_nhdsWithin_zero

lemma ball_subset_ball_of_mem_ball_half
    {x₀ x : E} {R r : ℝ}
    (hx : x ∈ Metric.ball x₀ (R / 2)) (_hr : 0 ≤ r) (hrR : r ≤ R / 2) :
    Metric.ball x r ⊆ Metric.ball x₀ R := by
  let _ := _hr
  intro z hz
  have hx' : _root_.Dist.dist x x₀ < R / 2 := by simpa using hx
  have hz' : _root_.Dist.dist z x < r := by simpa using hz
  refine Metric.mem_ball.mpr ?_
  calc
    dist z x₀ ≤ _root_.Dist.dist z x + _root_.Dist.dist x x₀ := dist_triangle _ _ _
    _ < r + R / 2 := by linarith
    _ ≤ R := by linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.ball_subset_ball_of_mem_ball_half then
    throwError "Refusing to shadow existing declaration DeGiorgi.ball_subset_ball_of_mem_ball_half"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.ball_subset_ball_of_mem_ball_half ``Submission.DeGiorgi.ball_subset_ball_of_mem_ball_half

lemma closedBall_subset_ball_of_mem_ball_half
    {x₀ x : E} {R r : ℝ}
    (hx : x ∈ Metric.ball x₀ (R / 2)) (_hr : 0 ≤ r) (hrR : r ≤ R / 2) :
    Metric.closedBall x r ⊆ Metric.ball x₀ R := by
  let _ := _hr
  intro z hz
  have hx' : _root_.Dist.dist x x₀ < R / 2 := by simpa using hx
  have hz' : _root_.Dist.dist z x ≤ r := by simpa using hz
  refine Metric.mem_ball.mpr ?_
  calc
    dist z x₀ ≤ _root_.Dist.dist z x + _root_.Dist.dist x x₀ := dist_triangle _ _ _
    _ < r + R / 2 := by linarith
    _ ≤ R := by linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.closedBall_subset_ball_of_mem_ball_half then
    throwError "Refusing to shadow existing declaration DeGiorgi.closedBall_subset_ball_of_mem_ball_half"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.closedBall_subset_ball_of_mem_ball_half ``Submission.DeGiorgi.closedBall_subset_ball_of_mem_ball_half

lemma hasCampanatoBound_of_ballSubset
    {u : E → ℝ} {x₀ : E} {R α C : ℝ}
    (hcamp : HasCampanatoBound u x₀ R α C)
    {x : E} {r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hsub : Metric.ball x r ⊆ Metric.ball x₀ R) :
    _root_.MeasureTheory.IntegrableOn u (Metric.ball x r) _root_.MeasureTheory.MeasureSpace.volume ∧
      r⁻¹ ^ α *
          ⨍ z in Metric.ball x r,
            |u z - ⨍ w in Metric.ball x r, u w| ∂volume
        ≤ C := by
  let b : CampanatoBall x₀ R := ⟨(x, r), ⟨hr, hrR, hsub⟩⟩
  exact hcamp b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.hasCampanatoBound_of_ballSubset then
    throwError "Refusing to shadow existing declaration DeGiorgi.hasCampanatoBound_of_ballSubset"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.hasCampanatoBound_of_ballSubset ``Submission.DeGiorgi.hasCampanatoBound_of_ballSubset

lemma le_mul_rpow_of_inv_rpow_mul_le
    {a C r α : ℝ} (hr : 0 < r)
    (h : r⁻¹ ^ α * a ≤ C) :
    a ≤ C * r ^ α := by
  have hrpow_nonneg : 0 ≤ r ^ α := Real.rpow_nonneg hr.le _
  have hrpow_ne : r ^ α ≠ 0 := (Real.rpow_pos_of_pos hr α).ne'
  have h' := mul_le_mul_of_nonneg_left h hrpow_nonneg
  calc
    a = (r ^ α * (r⁻¹ ^ α)) * a := by
      rw [Real.inv_rpow hr.le, mul_inv_cancel₀ hrpow_ne, one_mul]
    _ = r ^ α * (r⁻¹ ^ α * a) := by ring
    _ ≤ r ^ α * C := h'
    _ = C * r ^ α := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.le_mul_rpow_of_inv_rpow_mul_le then
    throwError "Refusing to shadow existing declaration DeGiorgi.le_mul_rpow_of_inv_rpow_mul_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.le_mul_rpow_of_inv_rpow_mul_le ``Submission.DeGiorgi.le_mul_rpow_of_inv_rpow_mul_le

lemma abs_ballAverage_half_sub_ballAverage_le
    {u : E → ℝ} {x : E} {r : ℝ}
    (hr : 0 < r)
    (hu_int : _root_.MeasureTheory.IntegrableOn u (Metric.ball x r) _root_.MeasureTheory.MeasureSpace.volume) :
    |⨍ z in Metric.ball x (r / 2), u z ∂volume - ⨍ z in Metric.ball x r, u z ∂volume|
      ≤ (2 : ℝ) ^ d *
        ⨍ z in Metric.ball x r, |u z - ⨍ w in Metric.ball x r, u w| ∂volume := by
  let S : Set E := Metric.ball x (r / 2)
  let B : Set E := Metric.ball x r
  let avg : ℝ := ⨍ w in B, u w ∂volume
  have hSsub : S ⊆ B := by
    intro z hz
    have hz' : _root_.Dist.dist z x < r / 2 := by simpa [S] using hz
    simpa [B] using (lt_of_lt_of_le hz' (by linarith))
  have hSfin : _root_.MeasureTheory.MeasureSpace.volume S ≠ ∞ := by
    simpa [S] using (_root_.MeasureTheory.measure_ball_lt_top (μ := _root_.MeasureTheory.MeasureSpace.volume) (x := x) (r := r / 2)).ne
  have hBfin : _root_.MeasureTheory.MeasureSpace.volume B ≠ ∞ := by
    simpa [B] using (_root_.MeasureTheory.measure_ball_lt_top (μ := _root_.MeasureTheory.MeasureSpace.volume) (x := x) (r := r)).ne
  have hS0 : _root_.MeasureTheory.MeasureSpace.volume S ≠ 0 := by
    simpa [S] using (_root_.Metric.measure_ball_pos (μ := _root_.MeasureTheory.MeasureSpace.volume) x (by positivity)).ne'
  have hB0 : _root_.MeasureTheory.MeasureSpace.volume B ≠ 0 := by
    simpa [B] using (_root_.Metric.measure_ball_pos (μ := _root_.MeasureTheory.MeasureSpace.volume) x hr).ne'
  have hSreal0 : volume.real S ≠ 0 := (MeasureTheory.measureReal_ne_zero_iff hSfin).2 hS0
  have hBreal0 : volume.real B ≠ 0 := (MeasureTheory.measureReal_ne_zero_iff hBfin).2 hB0
  have huS_int : _root_.MeasureTheory.IntegrableOn u S volume := hu_int.mono_set hSsub
  have hsub_int : _root_.MeasureTheory.IntegrableOn (fun z => u z - avg) S volume :=
    huS_int.sub (_root_.MeasureTheory.integrableOn_const hSfin)
  have habsB_int : _root_.MeasureTheory.IntegrableOn (fun z => |u z - avg|) B volume := by
    change _root_.MeasureTheory.Integrable (fun z => ‖u z - avg‖) (volume.restrict B)
    exact (hu_int.sub (_root_.MeasureTheory.integrableOn_const hBfin)).norm
  have hdiff :
      (⨍ z in S, u z ∂volume) - avg = ⨍ z in S, (u z - avg) ∂volume := by
    rw [MeasureTheory.setAverage_eq (μ := _root_.MeasureTheory.MeasureSpace.volume) (f := u) (s := S),
      MeasureTheory.setAverage_eq (μ := _root_.MeasureTheory.MeasureSpace.volume) (f := fun z => u z - avg) (s := S)]
    rw [_root_.MeasureTheory.integral_sub huS_int (_root_.MeasureTheory.integrableOn_const hSfin),
      MeasureTheory.setIntegral_const avg]
    simp [smul_eq_mul]
    field_simp [hSreal0]
  have hnorm :
      |⨍ z in S, (u z - avg) ∂volume|
        ≤ ⨍ z in S, |u z - avg| ∂volume := by
    have hnorm' :
        |∫ z in S, (u z - avg) ∂volume| ≤ ∫ z in S, |u z - avg| ∂volume := by
      simpa [Real.norm_eq_abs, avg] using
        (_root_.MeasureTheory.norm_integral_le_integral_norm (fun z => u z - avg) :
          ‖∫ z in S, (u z - avg) ∂volume‖ ≤ ∫ z in S, ‖u z - avg‖ ∂volume)
    have hSreal_inv_nonneg : 0 ≤ (volume.real S)⁻¹ := by positivity
    have hnorm'' := mul_le_mul_of_nonneg_left hnorm' hSreal_inv_nonneg
    calc
      |⨍ z in S, (u z - avg) ∂volume|
          = (volume.real S)⁻¹ * |∫ z in S, (u z - avg) ∂volume| := by
              rw [MeasureTheory.setAverage_eq, smul_eq_mul, abs_mul, abs_inv,
                abs_of_nonneg MeasureTheory.measureReal_nonneg]
      _ ≤ (volume.real S)⁻¹ * ∫ z in S, |u z - avg| ∂volume := hnorm''
      _ = ⨍ z in S, |u z - avg| ∂volume := by
            rw [MeasureTheory.setAverage_eq, smul_eq_mul]
  have hmono :
      ∫ z in S, |u z - avg| ∂volume ≤ ∫ z in B, |u z - avg| ∂volume := by
    exact MeasureTheory.setIntegral_mono_set habsB_int
      (Filter.Eventually.of_forall fun z => abs_nonneg (u z - avg))
      (Filter.Eventually.of_forall hSsub)
  have hvol :
      volume.real B = (2 : ℝ) ^ d * volume.real S := by
    simpa [S, B] using volumeReal_ball_halves x hr
  calc
    |⨍ z in S, u z ∂volume - avg|
        = |⨍ z in S, (u z - avg) ∂volume| := by rw [hdiff]
    _ ≤ ⨍ z in S, |u z - avg| ∂volume := hnorm
    _ = (volume.real S)⁻¹ * ∫ z in S, |u z - avg| ∂volume := by
      rw [MeasureTheory.setAverage_eq (μ := _root_.MeasureTheory.MeasureSpace.volume) (f := fun z => |u z - avg|) (s := S),
        smul_eq_mul]
    _ ≤ (volume.real S)⁻¹ * ∫ z in B, |u z - avg| ∂volume := by
      gcongr
    _ = (2 : ℝ) ^ d * ((volume.real B)⁻¹ * ∫ z in B, |u z - avg| ∂volume) := by
      rw [hvol]
      field_simp [hSreal0, hBreal0]
    _ = (2 : ℝ) ^ d * ⨍ z in Metric.ball x r, |u z - ⨍ w in Metric.ball x r, u w| ∂volume := by
      simp [B, avg, MeasureTheory.setAverage_eq, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.abs_ballAverage_half_sub_ballAverage_le then
    throwError "Refusing to shadow existing declaration DeGiorgi.abs_ballAverage_half_sub_ballAverage_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.abs_ballAverage_half_sub_ballAverage_le ``Submission.DeGiorgi.abs_ballAverage_half_sub_ballAverage_le

lemma abs_halfSubballAverage_sub_ballAverage_le
    {u : E → ℝ} {x c : E} {r : ℝ}
    (hr : 0 < r)
    (hsub : Metric.ball c (r / 2) ⊆ Metric.ball x r)
    (hu_int : _root_.MeasureTheory.IntegrableOn u (Metric.ball x r) _root_.MeasureTheory.MeasureSpace.volume) :
    |⨍ z in Metric.ball c (r / 2), u z ∂volume - ⨍ z in Metric.ball x r, u z ∂volume|
      ≤ (2 : ℝ) ^ d *
        ⨍ z in Metric.ball x r, |u z - ⨍ w in Metric.ball x r, u w| ∂volume := by
  let S : Set E := Metric.ball c (r / 2)
  let B : Set E := Metric.ball x r
  let avg : ℝ := ⨍ w in B, u w ∂volume
  have hSfin : _root_.MeasureTheory.MeasureSpace.volume S ≠ ∞ := by
    simpa [S] using (_root_.MeasureTheory.measure_ball_lt_top (μ := _root_.MeasureTheory.MeasureSpace.volume) (x := c) (r := r / 2)).ne
  have hBfin : _root_.MeasureTheory.MeasureSpace.volume B ≠ ∞ := by
    simpa [B] using (_root_.MeasureTheory.measure_ball_lt_top (μ := _root_.MeasureTheory.MeasureSpace.volume) (x := x) (r := r)).ne
  have hS0 : _root_.MeasureTheory.MeasureSpace.volume S ≠ 0 := by
    simpa [S] using (_root_.Metric.measure_ball_pos (μ := _root_.MeasureTheory.MeasureSpace.volume) c (by positivity)).ne'
  have hB0 : _root_.MeasureTheory.MeasureSpace.volume B ≠ 0 := by
    simpa [B] using (_root_.Metric.measure_ball_pos (μ := _root_.MeasureTheory.MeasureSpace.volume) x hr).ne'
  have hSreal0 : volume.real S ≠ 0 := (MeasureTheory.measureReal_ne_zero_iff hSfin).2 hS0
  have hBreal0 : volume.real B ≠ 0 := (MeasureTheory.measureReal_ne_zero_iff hBfin).2 hB0
  have huS_int : _root_.MeasureTheory.IntegrableOn u S volume := hu_int.mono_set hsub
  have hdiff :
      (⨍ z in S, u z ∂volume) - avg = ⨍ z in S, (u z - avg) ∂volume := by
    rw [MeasureTheory.setAverage_eq (μ := _root_.MeasureTheory.MeasureSpace.volume) (f := u) (s := S),
      MeasureTheory.setAverage_eq (μ := _root_.MeasureTheory.MeasureSpace.volume) (f := fun z => u z - avg) (s := S)]
    rw [_root_.MeasureTheory.integral_sub huS_int (_root_.MeasureTheory.integrableOn_const hSfin),
      MeasureTheory.setIntegral_const avg]
    simp [smul_eq_mul]
    field_simp [hSreal0]
  have hnorm :
      |⨍ z in S, (u z - avg) ∂volume|
        ≤ ⨍ z in S, |u z - avg| ∂volume := by
    have hnorm' :
        |∫ z in S, (u z - avg) ∂volume| ≤ ∫ z in S, |u z - avg| ∂volume := by
      simpa [Real.norm_eq_abs, avg] using
        (_root_.MeasureTheory.norm_integral_le_integral_norm (fun z => u z - avg) :
          ‖∫ z in S, (u z - avg) ∂volume‖ ≤ ∫ z in S, ‖u z - avg‖ ∂volume)
    have hSreal_inv_nonneg : 0 ≤ (volume.real S)⁻¹ := by positivity
    have hnorm'' := mul_le_mul_of_nonneg_left hnorm' hSreal_inv_nonneg
    calc
      |⨍ z in S, (u z - avg) ∂volume|
          = (volume.real S)⁻¹ * |∫ z in S, (u z - avg) ∂volume| := by
              rw [MeasureTheory.setAverage_eq, smul_eq_mul, abs_mul, abs_inv,
                abs_of_nonneg MeasureTheory.measureReal_nonneg]
      _ ≤ (volume.real S)⁻¹ * ∫ z in S, |u z - avg| ∂volume := hnorm''
      _ = ⨍ z in S, |u z - avg| ∂volume := by
            rw [MeasureTheory.setAverage_eq, smul_eq_mul]
  have habsB_int : _root_.MeasureTheory.IntegrableOn (fun z => |u z - avg|) B volume := by
    change _root_.MeasureTheory.Integrable (fun z => ‖u z - avg‖) (volume.restrict B)
    exact (hu_int.sub (_root_.MeasureTheory.integrableOn_const hBfin)).norm
  have hmono :
      ∫ z in S, |u z - avg| ∂volume ≤ ∫ z in B, |u z - avg| ∂volume := by
    exact MeasureTheory.setIntegral_mono_set habsB_int
      (Filter.Eventually.of_forall fun z => abs_nonneg (u z - avg))
      (Filter.Eventually.of_forall hsub)
  have hvol :
      volume.real B = (2 : ℝ) ^ d * volume.real S := by
    rw [show B = Metric.ball x r by rfl, show S = Metric.ball c (r / 2) by rfl]
    rw [volumeReal_ball_eq x hr, volumeReal_ball_eq c (by positivity)]
    have hr_eq : r ^ d = ((2 : ℝ) * (r / 2)) ^ d := by
      congr 1
      ring
    rw [hr_eq, mul_pow]
    ring
  calc
    |⨍ z in S, u z ∂volume - avg|
        = |⨍ z in S, (u z - avg) ∂volume| := by rw [hdiff]
    _ ≤ ⨍ z in S, |u z - avg| ∂volume := hnorm
    _ = (volume.real S)⁻¹ * ∫ z in S, |u z - avg| ∂volume := by
      rw [MeasureTheory.setAverage_eq (μ := _root_.MeasureTheory.MeasureSpace.volume) (f := fun z => |u z - avg|) (s := S),
        smul_eq_mul]
    _ ≤ (volume.real S)⁻¹ * ∫ z in B, |u z - avg| ∂volume := by
      gcongr
    _ = (2 : ℝ) ^ d * ((volume.real B)⁻¹ * ∫ z in B, |u z - avg| ∂volume) := by
      rw [hvol]
      field_simp [hSreal0, hBreal0]
    _ = (2 : ℝ) ^ d * ⨍ z in Metric.ball x r, |u z - ⨍ w in Metric.ball x r, u w| ∂volume := by
      simp [B, avg, MeasureTheory.setAverage_eq, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.abs_halfSubballAverage_sub_ballAverage_le then
    throwError "Refusing to shadow existing declaration DeGiorgi.abs_halfSubballAverage_sub_ballAverage_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.abs_halfSubballAverage_sub_ballAverage_le ``Submission.DeGiorgi.abs_halfSubballAverage_sub_ballAverage_le

lemma ballAverage_sub_ballAverage_sameRadius_le_campanato
    {u : E → ℝ} {x₀ : E} {R α C : ℝ}
    (hcamp : HasCampanatoBound u x₀ R α C)
    {x y : E} {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hxy : _root_.Dist.dist x y ≤ r)
    (hxsub : Metric.ball x r ⊆ Metric.ball x₀ R)
    (hysub : Metric.ball y r ⊆ Metric.ball x₀ R) :
    |⨍ z in Metric.ball x r, u z ∂volume - ⨍ z in Metric.ball y r, u z ∂volume|
      ≤ (2 : ℝ) ^ (d + 1) * C * r ^ α := by
  let c : E := midpoint ℝ x y
  have hcx : _root_.Dist.dist c x ≤ r / 2 := by
    calc
      dist c x = _root_.Dist.dist (midpoint ℝ x y) x := rfl
      _ = (1 / 2 : ℝ) * _root_.Dist.dist x y := by
          rw [dist_midpoint_left (𝕜 := ℝ)]
          rw [Real.norm_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
          ring
      _ = _root_.Dist.dist x y / 2 := by ring
      _ ≤ r / 2 := by linarith
  have hcy : _root_.Dist.dist c y ≤ r / 2 := by
    calc
      dist c y = _root_.Dist.dist (midpoint ℝ x y) y := rfl
      _ = (1 / 2 : ℝ) * _root_.Dist.dist x y := by
          rw [dist_midpoint_right (𝕜 := ℝ)]
          rw [Real.norm_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
          ring
      _ = _root_.Dist.dist x y / 2 := by ring
      _ ≤ r / 2 := by linarith
  have hsubx : Metric.ball c (r / 2) ⊆ Metric.ball x r := by
    intro z hz
    have hz' : _root_.Dist.dist z c < r / 2 := by simpa [c] using hz
    refine Metric.mem_ball.mpr <| lt_of_le_of_lt (dist_triangle z c x) ?_
    linarith
  have hsuby : Metric.ball c (r / 2) ⊆ Metric.ball y r := by
    intro z hz
    have hz' : _root_.Dist.dist z c < r / 2 := by simpa [c] using hz
    refine Metric.mem_ball.mpr <| lt_of_le_of_lt (dist_triangle z c y) ?_
    linarith
  rcases hasCampanatoBound_of_ballSubset hcamp hr hrR hxsub with ⟨hx_int, hx_ball⟩
  rcases hasCampanatoBound_of_ballSubset hcamp hr hrR hysub with ⟨hy_int, hy_ball⟩
  have hoscx :
      ⨍ z in Metric.ball x r,
          |u z - ⨍ w in Metric.ball x r, u w| ∂volume
        ≤ C * r ^ α :=
    le_mul_rpow_of_inv_rpow_mul_le hr hx_ball
  have hoscy :
      ⨍ z in Metric.ball y r,
          |u z - ⨍ w in Metric.ball y r, u w| ∂volume
        ≤ C * r ^ α :=
    le_mul_rpow_of_inv_rpow_mul_le hr hy_ball
  calc
    |⨍ z in Metric.ball x r, u z ∂volume - ⨍ z in Metric.ball y r, u z ∂volume|
      ≤ |⨍ z in Metric.ball x r, u z ∂volume - ⨍ z in Metric.ball c (r / 2), u z ∂volume| +
          |⨍ z in Metric.ball c (r / 2), u z ∂volume - ⨍ z in Metric.ball y r, u z ∂volume| := by
        have := abs_sub_le
          (⨍ z in Metric.ball x r, u z ∂volume)
          (⨍ z in Metric.ball c (r / 2), u z ∂volume)
          (⨍ z in Metric.ball y r, u z ∂volume)
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    _ ≤ (2 : ℝ) ^ d * ⨍ z in Metric.ball x r, |u z - ⨍ w in Metric.ball x r, u w| ∂volume +
          (2 : ℝ) ^ d * ⨍ z in Metric.ball y r, |u z - ⨍ w in Metric.ball y r, u w| ∂volume := by
        gcongr
        · simpa [abs_sub_comm] using abs_halfSubballAverage_sub_ballAverage_le hr hsubx hx_int
        · simpa using abs_halfSubballAverage_sub_ballAverage_le hr hsuby hy_int
    _ ≤ (2 : ℝ) ^ d * (C * r ^ α) + (2 : ℝ) ^ d * (C * r ^ α) := by
        gcongr
    _ = (2 : ℝ) ^ (d + 1) * C * r ^ α := by
        ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.ballAverage_sub_ballAverage_sameRadius_le_campanato then
    throwError "Refusing to shadow existing declaration DeGiorgi.ballAverage_sub_ballAverage_sameRadius_le_campanato"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.ballAverage_sub_ballAverage_sameRadius_le_campanato ``Submission.DeGiorgi.ballAverage_sub_ballAverage_sameRadius_le_campanato

lemma dyadicBallAverage_step_le_campanato
    {u : E → ℝ} {x₀ x : E} {R α C ρ : ℝ}
    (hcamp : HasCampanatoBound u x₀ R α C)
    (hρ : 0 < ρ) (hρR : ρ ≤ R) (hsub : Metric.ball x ρ ⊆ Metric.ball x₀ R)
    (n : ℕ) :
    |dyadicBallAverage u x ρ n - dyadicBallAverage u x ρ (n + 1)|
      ≤ (2 : ℝ) ^ d * C * (ρ / (2 : ℝ) ^ n) ^ α := by
  have hr : 0 < ρ / (2 : ℝ) ^ n := by positivity
  have hrR : ρ / (2 : ℝ) ^ n ≤ R := by
    calc
      ρ / (2 : ℝ) ^ n ≤ ρ := by
        have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
          exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
        exact div_le_self hρ.le hpow
      _ ≤ R := hρR
  have hsubn : Metric.ball x (ρ / (2 : ℝ) ^ n) ⊆ Metric.ball x₀ R := by
    refine Set.Subset.trans ?_ hsub
    exact Metric.ball_subset_ball (by
      have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
        exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      exact div_le_self hρ.le hpow)
  rcases hasCampanatoBound_of_ballSubset hcamp hr hrR hsubn with ⟨hu_int, hball⟩
  have hosc :
      ⨍ z in Metric.ball x (ρ / (2 : ℝ) ^ n),
          |u z - ⨍ w in Metric.ball x (ρ / (2 : ℝ) ^ n), u w| ∂volume
        ≤ C * (ρ / (2 : ℝ) ^ n) ^ α :=
    le_mul_rpow_of_inv_rpow_mul_le hr hball
  calc
    |dyadicBallAverage u x ρ n - dyadicBallAverage u x ρ (n + 1)|
      ≤ (2 : ℝ) ^ d *
          ⨍ z in Metric.ball x (ρ / (2 : ℝ) ^ n),
            |u z - ⨍ w in Metric.ball x (ρ / (2 : ℝ) ^ n), u w| ∂volume := by
        simpa [abs_sub_comm, dyadicBallAverage, div_eq_mul_inv, pow_succ, mul_assoc, mul_left_comm,
          mul_comm] using abs_ballAverage_half_sub_ballAverage_le hr hu_int
    _ ≤ (2 : ℝ) ^ d * (C * (ρ / (2 : ℝ) ^ n) ^ α) := by
      gcongr
    _ = (2 : ℝ) ^ d * C * (ρ / (2 : ℝ) ^ n) ^ α := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.dyadicBallAverage_step_le_campanato then
    throwError "Refusing to shadow existing declaration DeGiorgi.dyadicBallAverage_step_le_campanato"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.dyadicBallAverage_step_le_campanato ``Submission.DeGiorgi.dyadicBallAverage_step_le_campanato

lemma dyadicBallAverage_step_le_geometric
    {u : E → ℝ} {x₀ x : E} {R α C ρ : ℝ}
    (_hα : 0 < α)
    (hcamp : HasCampanatoBound u x₀ R α C)
    (hρ : 0 < ρ) (hρR : ρ ≤ R) (hsub : Metric.ball x ρ ⊆ Metric.ball x₀ R)
    (n : ℕ) :
    _root_.Dist.dist (dyadicBallAverage u x ρ n) (dyadicBallAverage u x ρ (n + 1))
      ≤ ((2 : ℝ) ^ d * C * ρ ^ α) * ((2 : ℝ) ^ (-α)) ^ n := by
  let _ := _hα
  have hstep := dyadicBallAverage_step_le_campanato hcamp hρ hρR hsub n
  have hrpow :
      (ρ / (2 : ℝ) ^ n) ^ α = ρ ^ α * ((2 : ℝ) ^ (-α)) ^ n := by
    calc
      (ρ / (2 : ℝ) ^ n) ^ α = ρ ^ α / (((2 : ℝ) ^ n) ^ α) := by
        rw [Real.div_rpow hρ.le (by positivity)]
      _ = ρ ^ α / (((2 : ℝ) ^ α) ^ n) := by
        rw [← Real.rpow_natCast_mul (by positivity) n α]
        rw [mul_comm, Real.rpow_mul_natCast (by positivity)]
      _ = ρ ^ α * ((((2 : ℝ) ^ α) ^ n)⁻¹) := by rw [div_eq_mul_inv]
      _ = ρ ^ α * (((2 : ℝ) ^ α)⁻¹) ^ n := by rw [inv_pow]
      _ = ρ ^ α * ((2 : ℝ) ^ (-α)) ^ n := by
          rw [Real.rpow_neg (by positivity)]
  simpa [Real.dist_eq, hrpow, mul_assoc, mul_left_comm, mul_comm] using hstep

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.dyadicBallAverage_step_le_geometric then
    throwError "Refusing to shadow existing declaration DeGiorgi.dyadicBallAverage_step_le_geometric"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.dyadicBallAverage_step_le_geometric ``Submission.DeGiorgi.dyadicBallAverage_step_le_geometric

lemma dyadicBallAverage_cauchy
    {u : E → ℝ} {x₀ x : E} {R α C ρ : ℝ}
    (hα : 0 < α)
    (hcamp : HasCampanatoBound u x₀ R α C)
    (hρ : 0 < ρ) (hρR : ρ ≤ R) (hsub : Metric.ball x ρ ⊆ Metric.ball x₀ R) :
    CauchySeq (dyadicBallAverage u x ρ) := by
  have hq_lt : (2 : ℝ) ^ (-α) < 1 := by
    rw [Real.rpow_neg (by positivity)]
    have h2a : 1 < (2 : ℝ) ^ α := Real.one_lt_rpow (by norm_num) hα
    exact inv_lt_one_of_one_lt₀ h2a
  exact cauchySeq_of_le_geometric (r := (2 : ℝ) ^ (-α))
    (C := (2 : ℝ) ^ d * C * ρ ^ α) hq_lt
    (dyadicBallAverage_step_le_geometric hα hcamp hρ hρR hsub)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.dyadicBallAverage_cauchy then
    throwError "Refusing to shadow existing declaration DeGiorgi.dyadicBallAverage_cauchy"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.dyadicBallAverage_cauchy ``Submission.DeGiorgi.dyadicBallAverage_cauchy

noncomputable def dyadicBallAverageLimit
    (u : E → ℝ) (x : E) (ρ : ℝ) : ℝ :=
  _root_.Filter.limUnder _root_.Filter.atTop (dyadicBallAverage u x ρ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.dyadicBallAverageLimit then
    throwError "Refusing to shadow existing declaration DeGiorgi.dyadicBallAverageLimit"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.dyadicBallAverageLimit ``Submission.DeGiorgi.dyadicBallAverageLimit

lemma tendsto_dyadicBallAverageLimit
    {u : E → ℝ} {x₀ x : E} {R α C ρ : ℝ}
    (hα : 0 < α)
    (hcamp : HasCampanatoBound u x₀ R α C)
    (hρ : 0 < ρ) (hρR : ρ ≤ R) (hsub : Metric.ball x ρ ⊆ Metric.ball x₀ R) :
    Tendsto (dyadicBallAverage u x ρ) _root_.Filter.atTop (𝓝 (dyadicBallAverageLimit u x ρ)) := by
  simpa [dyadicBallAverageLimit] using
    (dyadicBallAverage_cauchy hα hcamp hρ hρR hsub).tendsto_limUnder

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.tendsto_dyadicBallAverageLimit then
    throwError "Refusing to shadow existing declaration DeGiorgi.tendsto_dyadicBallAverageLimit"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.tendsto_dyadicBallAverageLimit ``Submission.DeGiorgi.tendsto_dyadicBallAverageLimit

lemma dyadicBallAverage_tail_le
    {u : E → ℝ} {x₀ x : E} {R α C ρ : ℝ}
    (hα : 0 < α)
    (hcamp : HasCampanatoBound u x₀ R α C)
    (hρ : 0 < ρ) (hρR : ρ ≤ R) (hsub : Metric.ball x ρ ⊆ Metric.ball x₀ R)
    (n : ℕ) :
    _root_.Dist.dist (dyadicBallAverage u x ρ n) (dyadicBallAverageLimit u x ρ)
      ≤ (((2 : ℝ) ^ d * C * ρ ^ α) * ((2 : ℝ) ^ (-α)) ^ n) / (1 - (2 : ℝ) ^ (-α)) := by
  have hq_lt : (2 : ℝ) ^ (-α) < 1 := by
    rw [Real.rpow_neg (by positivity)]
    have h2a : 1 < (2 : ℝ) ^ α := Real.one_lt_rpow (by norm_num) hα
    exact inv_lt_one_of_one_lt₀ h2a
  exact dist_le_of_le_geometric_of_tendsto
    (r := (2 : ℝ) ^ (-α)) (C := (2 : ℝ) ^ d * C * ρ ^ α)
    hq_lt (dyadicBallAverage_step_le_geometric hα hcamp hρ hρR hsub)
    (tendsto_dyadicBallAverageLimit hα hcamp hρ hρR hsub) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.dyadicBallAverage_tail_le then
    throwError "Refusing to shadow existing declaration DeGiorgi.dyadicBallAverage_tail_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.dyadicBallAverage_tail_le ``Submission.DeGiorgi.dyadicBallAverage_tail_le

lemma abs_halfSubballAverage_sub_ballAverage_le_campanato
    {u : E → ℝ} {x₀ : E} {R α C : ℝ}
    (hR : 0 < R) (hcamp : HasCampanatoBound u x₀ R α C)
    {c : E} (hsub : Metric.ball c (R / 2) ⊆ Metric.ball x₀ R) :
    |⨍ z in Metric.ball c (R / 2), u z ∂volume - ⨍ z in Metric.ball x₀ R, u z ∂volume|
      ≤ (2 : ℝ) ^ d * C * R ^ α := by
  rcases hasCampanatoBound_of_ballSubset hcamp hR le_rfl
    (Set.Subset.rfl : Metric.ball x₀ R ⊆ Metric.ball x₀ R)
    with ⟨hu_int, hball⟩
  have hosc :
      ⨍ z in Metric.ball x₀ R,
          |u z - ⨍ w in Metric.ball x₀ R, u w| ∂volume
        ≤ C * R ^ α :=
    le_mul_rpow_of_inv_rpow_mul_le hR hball
  calc
    |⨍ z in Metric.ball c (R / 2), u z ∂volume - ⨍ z in Metric.ball x₀ R, u z ∂volume|
      ≤ (2 : ℝ) ^ d *
          ⨍ z in Metric.ball x₀ R,
            |u z - ⨍ w in Metric.ball x₀ R, u w| ∂volume := by
        simpa [abs_sub_comm] using abs_halfSubballAverage_sub_ballAverage_le hR hsub hu_int
    _ ≤ (2 : ℝ) ^ d * (C * R ^ α) := by
        gcongr
    _ = (2 : ℝ) ^ d * C * R ^ α := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.abs_halfSubballAverage_sub_ballAverage_le_campanato then
    throwError "Refusing to shadow existing declaration DeGiorgi.abs_halfSubballAverage_sub_ballAverage_le_campanato"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.abs_halfSubballAverage_sub_ballAverage_le_campanato ``Submission.DeGiorgi.abs_halfSubballAverage_sub_ballAverage_le_campanato

lemma ballAverage_half_sub_ballAverage_le_campanato
    {u : E → ℝ} {x₀ : E} {R α C : ℝ}
    (hcamp : HasCampanatoBound u x₀ R α C)
    {x : E} {r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hsub : Metric.ball x r ⊆ Metric.ball x₀ R) :
    |⨍ z in Metric.ball x (r / 2), u z ∂volume - ⨍ z in Metric.ball x r, u z ∂volume|
      ≤ (2 : ℝ) ^ d * C * r ^ α := by
  rcases hasCampanatoBound_of_ballSubset hcamp hr hrR hsub with ⟨hu_int, hball⟩
  have hosc :
      ⨍ z in Metric.ball x r,
          |u z - ⨍ w in Metric.ball x r, u w| ∂volume
        ≤ C * r ^ α :=
    le_mul_rpow_of_inv_rpow_mul_le hr hball
  calc
    |⨍ z in Metric.ball x (r / 2), u z ∂volume - ⨍ z in Metric.ball x r, u z ∂volume|
      ≤ (2 : ℝ) ^ d *
          ⨍ z in Metric.ball x r,
            |u z - ⨍ w in Metric.ball x r, u w| ∂volume :=
      abs_ballAverage_half_sub_ballAverage_le hr hu_int
    _ ≤ (2 : ℝ) ^ d * (C * r ^ α) := by
      gcongr
    _ = (2 : ℝ) ^ d * C * r ^ α := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.ballAverage_half_sub_ballAverage_le_campanato then
    throwError "Refusing to shadow existing declaration DeGiorgi.ballAverage_half_sub_ballAverage_le_campanato"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.ballAverage_half_sub_ballAverage_le_campanato ``Submission.DeGiorgi.ballAverage_half_sub_ballAverage_le_campanato

/-- On the inner ball, the dyadic Campanato average limit agrees a.e. with the original function. -/
lemma ae_eq_dyadicBallAverageLimit_on_halfBall
    {u : E → ℝ} {x₀ : E} {R α C_camp : ℝ}
    (hα : 0 < α) (hR : 0 < R)
    (hcamp : HasCampanatoBound u x₀ R α C_camp) :
    ∀ᵐ x ∂volume.restrict (Metric.ball x₀ (R / 2)),
      dyadicBallAverageLimit u x (R / 2) = u x := by
  classical
  let outer : Set E := Metric.ball x₀ R
  let inner : Set E := Metric.ball x₀ (R / 2)
  let ρ : ℝ := R / 2
  let f : E → ℝ := outer.indicator u
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρR : ρ ≤ R := by
    dsimp [ρ]
    linarith
  have hinner_subset_outer : inner ⊆ outer := by
    exact Metric.ball_subset_ball hρR
  let bouter : CampanatoBall x₀ R := ⟨(x₀, R), ⟨hR, le_rfl, Set.Subset.rfl⟩⟩
  have houter_int : _root_.MeasureTheory.IntegrableOn u outer volume := hcamp.integrableOn bouter
  have hf_int : _root_.MeasureTheory.Integrable f volume := houter_int.integrable_indicator measurableSet_ball
  have hdiff_ae :
      ∀ᵐ x ∂volume,
        _root_.Filter.Tendsto (fun n : ℕ => ⨍ y in Metric.closedBall x (ρ / (2 : ℝ) ^ n), f y ∂volume)
          atTop (𝓝 (f x)) := by
    filter_upwards
        [((IsUnifLocDoublingMeasure.vitaliFamily (μ := _root_.MeasureTheory.MeasureSpace.volume) (K := 0)).ae_tendsto_average
          hf_int.locallyIntegrable)] with x hdx
    exact Tendsto.comp hdx <|
      IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt (μ := _root_.MeasureTheory.MeasureSpace.volume) (K := 0)
        (fun _ : ℕ => x) (fun n : ℕ => ρ / (2 : ℝ) ^ n)
        (tendsto_dyadic_radius_nhdsWithin_zero hρ)
        (Eventually.of_forall fun n => by
          exact Metric.mem_closedBall_self (x := x)
            (by positivity : 0 ≤ 0 * (ρ / (2 : ℝ) ^ n)))
  have hinner_eq_ae :
      ∀ᵐ x ∂volume.restrict inner, dyadicBallAverageLimit u x ρ = u x := by
    rw [_root_.MeasureTheory.ae_restrict_iff' measurableSet_ball]
    filter_upwards [hdiff_ae] with x hdx hx_inner
    have hx_outer : x ∈ outer := hinner_subset_outer hx_inner
    have hsub_ball : Metric.ball x ρ ⊆ outer :=
      ball_subset_ball_of_mem_ball_half hx_inner hρ.le le_rfl
    have hlimit_u :
        Tendsto (dyadicBallAverage u x ρ) _root_.Filter.atTop (𝓝 (dyadicBallAverageLimit u x ρ)) :=
      tendsto_dyadicBallAverageLimit hα hcamp hρ hρR hsub_ball
    have hclosed_to_u :
        _root_.Filter.Tendsto (fun n : ℕ => ⨍ y in Metric.closedBall x (ρ / (2 : ℝ) ^ n), f y ∂volume)
          atTop (𝓝 (u x)) := by
      simpa [f, outer, hx_outer] using hdx
    have hclosed_eq :
        (fun n : ℕ => ⨍ y in Metric.closedBall x (ρ / (2 : ℝ) ^ n), f y ∂volume)
          =ᶠ[_root_.Filter.atTop] dyadicBallAverage u x ρ := by
      refine Eventually.of_forall fun n => ?_
      have hrn_nonneg : 0 ≤ ρ / (2 : ℝ) ^ n := by positivity
      have hrnR : ρ / (2 : ℝ) ^ n ≤ R / 2 := by
        calc
          ρ / (2 : ℝ) ^ n ≤ ρ := by
            exact div_le_self hρ.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
          _ = R / 2 := by rfl
      have hclosedsub :
          Metric.closedBall x (ρ / (2 : ℝ) ^ n) ⊆ outer :=
        closedBall_subset_ball_of_mem_ball_half hx_inner hrn_nonneg hrnR
      calc
        ⨍ y in Metric.closedBall x (ρ / (2 : ℝ) ^ n), f y ∂volume
            = ⨍ y in Metric.closedBall x (ρ / (2 : ℝ) ^ n), u y ∂volume := by
                apply MeasureTheory.setAverage_congr_fun Metric.isClosed_closedBall.measurableSet
                exact Eventually.of_forall fun z hz => by
                  simp [f, outer, hclosedsub hz]
        _ = ⨍ y in Metric.ball x (ρ / (2 : ℝ) ^ n), u y ∂volume := by
              exact setAverage_closedBall_eq_ball_of_pos x (by positivity)
        _ = dyadicBallAverage u x ρ n := by
              simp [dyadicBallAverage]
    have hdyad_to_u :
        Tendsto (dyadicBallAverage u x ρ) _root_.Filter.atTop (𝓝 (u x)) :=
      Tendsto.congr' hclosed_eq hclosed_to_u
    exact tendsto_nhds_unique hlimit_u hdyad_to_u
  simpa [inner, ρ] using hinner_eq_ae

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.ae_eq_dyadicBallAverageLimit_on_halfBall then
    throwError "Refusing to shadow existing declaration DeGiorgi.ae_eq_dyadicBallAverageLimit_on_halfBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.ae_eq_dyadicBallAverageLimit_on_halfBall ``Submission.DeGiorgi.ae_eq_dyadicBallAverageLimit_on_halfBall

lemma dyadicBallAverageLimit_holder_small
    {u : E → ℝ} {x₀ : E} {R α C_camp : ℝ}
    (hα : 0 < α) (hα_le : α ≤ 1) (hR : 0 < R)
    (hcamp : HasCampanatoBound u x₀ R α C_camp)
    {x y : E}
    (hx : x ∈ Metric.ball x₀ (R / 2))
    (hy : y ∈ Metric.ball x₀ (R / 2))
    (hsmall : ‖x - y‖ ≤ R / 2) :
    |dyadicBallAverageLimit u x (R / 2) - dyadicBallAverageLimit u y (R / 2)|
      ≤ CCampanatoHolder d α * C_camp * ‖x - y‖ ^ α := by
  let outer : Set E := Metric.ball x₀ R
  let ρ : ℝ := R / 2
  let q : ℝ := (2 : ℝ) ^ (-α)
  let invDen : ℝ := (1 - q)⁻¹
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρR : ρ ≤ R := by
    dsimp [ρ]
    linarith
  have hC_nonneg : 0 ≤ C_camp := hcamp.nonneg hα hR
  have hq_lt : q < 1 := by
    dsimp [q]
    rw [Real.rpow_neg (by positivity)]
    have h2a : 1 < (2 : ℝ) ^ α := Real.one_lt_rpow (by norm_num) hα
    exact inv_lt_one_of_one_lt₀ h2a
  have hden_pos : 0 < 1 - q := sub_pos.mpr hq_lt
  have h2a_le : (2 : ℝ) ^ α ≤ 2 := by
    simpa using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (2 : ℝ)) hα_le)
  have hq_ge_half : (1 / 2 : ℝ) ≤ q := by
    dsimp [q]
    rw [Real.rpow_neg (by positivity)]
    have h2a_pos : 0 < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
    simpa [one_div] using (one_div_le_one_div_of_le h2a_pos h2a_le)
  have hinvDen_ge_two : (2 : ℝ) ≤ invDen := by
    dsimp [invDen]
    have hden_half : 1 - q ≤ (1 / 2 : ℝ) := by linarith
    have hinv := one_div_le_one_div_of_le hden_pos hden_half
    simpa using hinv
  have hsubx : Metric.ball x ρ ⊆ outer :=
    ball_subset_ball_of_mem_ball_half hx hρ.le le_rfl
  have hsuby : Metric.ball y ρ ⊆ outer :=
    ball_subset_ball_of_mem_ball_half hy hρ.le le_rfl
  let K1 : ℝ := (2 : ℝ) ^ (d + 1) * invDen * C_camp * ‖x - y‖ ^ α
  have hK1_nonneg : 0 ≤ K1 := by
    dsimp [K1]
    positivity
  by_cases hxy_eq : x = y
  · subst x
    have hzero : ‖y - y‖ ^ α = 0 := by
      simp [Real.zero_rpow hα.ne']
    rw [sub_self, abs_zero, hzero]
    simp
  · have hdist_pos : 0 < ‖x - y‖ := by
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hxy_eq)
    obtain ⟨n, hn_lt, hn_le⟩ := exists_nat_pow_near_of_lt_one
      (show 0 < ‖x - y‖ / ρ by exact div_pos hdist_pos hρ)
      (show ‖x - y‖ / ρ ≤ 1 by
        have hsmall' : ‖x - y‖ ≤ 1 * ρ := by simpa [ρ] using hsmall
        exact (div_le_iff₀ hρ).2 hsmall')
      (by norm_num : 0 < (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1)
    let r_n : ℝ := ρ / (2 : ℝ) ^ n
    let ax : ℝ := dyadicBallAverage u x ρ n
    let ay : ℝ := dyadicBallAverage u y ρ n
    let lx : ℝ := dyadicBallAverageLimit u x ρ
    let ly : ℝ := dyadicBallAverageLimit u y ρ
    have hrn : 0 < r_n := by
      dsimp [r_n]
      positivity
    have hrn_half : r_n ≤ R / 2 := by
      calc
        r_n ≤ ρ := by
          dsimp [r_n]
          exact div_le_self hρ.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
        _ = R / 2 := by rfl
    have hrnR : r_n ≤ R := le_trans hrn_half hρR
    have hsubx_n : Metric.ball x r_n ⊆ outer :=
      ball_subset_ball_of_mem_ball_half hx hrn.le hrn_half
    have hsuby_n : Metric.ball y r_n ⊆ outer :=
      ball_subset_ball_of_mem_ball_half hy hrn.le hrn_half
    have hdist_le_rn_norm : ‖x - y‖ ≤ r_n := by
      have h := (div_le_iff₀ hρ).1 hn_le
      simpa [r_n, div_eq_mul_inv, inv_pow, mul_assoc, mul_left_comm, mul_comm] using h
    have hdist_le_rn : _root_.Dist.dist x y ≤ r_n := by
      simpa [dist_eq_norm] using hdist_le_rn_norm
    have hrn_lt_two_norm : r_n < 2 * ‖x - y‖ := by
      have h := (lt_div_iff₀ hρ).mp hn_lt
      calc
        r_n = ρ * ((1 / 2 : ℝ) ^ n) := by
          dsimp [r_n]
          rw [div_eq_mul_inv]
          have hpowinv : ((2 : ℝ) ^ n)⁻¹ = ((1 / 2 : ℝ) ^ n) := by
            rw [one_div]
            exact (inv_pow (2 : ℝ) n).symm
          exact congrArg (fun t : ℝ => ρ * t) hpowinv
        _ = 2 * (ρ * ((1 / 2 : ℝ) ^ (n + 1))) := by
          rw [pow_succ]
          ring
        _ < 2 * ‖x - y‖ := by
          have h' : ρ * ((1 / 2 : ℝ) ^ (n + 1)) < ‖x - y‖ := by
            simpa [mul_comm] using h
          gcongr
    have hrpow_le_two :
        r_n ^ α ≤ 2 * ‖x - y‖ ^ α := by
      calc
        r_n ^ α ≤ (2 * ‖x - y‖) ^ α := by
          exact Real.rpow_le_rpow (by positivity) hrn_lt_two_norm.le hα.le
        _ = (2 : ℝ) ^ α * ‖x - y‖ ^ α := by
            rw [Real.mul_rpow (by positivity) (norm_nonneg _)]
        _ ≤ 2 * ‖x - y‖ ^ α := by
            exact mul_le_mul_of_nonneg_right h2a_le
              (Real.rpow_nonneg (norm_nonneg _) _)
    have hrpow_eq : r_n ^ α = ρ ^ α * q ^ n := by
      dsimp [r_n, q]
      calc
        (ρ / (2 : ℝ) ^ n) ^ α = ρ ^ α / (((2 : ℝ) ^ n) ^ α) := by
          rw [Real.div_rpow hρ.le (by positivity)]
        _ = ρ ^ α / (((2 : ℝ) ^ α) ^ n) := by
          rw [← Real.rpow_natCast_mul (by positivity) n α]
          rw [mul_comm, Real.rpow_mul_natCast (by positivity)]
        _ = ρ ^ α * ((((2 : ℝ) ^ α) ^ n)⁻¹) := by rw [div_eq_mul_inv]
        _ = ρ ^ α * (((2 : ℝ) ^ α)⁻¹) ^ n := by rw [inv_pow]
        _ = ρ ^ α * ((2 : ℝ) ^ (-α)) ^ n := by
            rw [Real.rpow_neg (by positivity)]
    have hscaleTail :
        (2 : ℝ) ^ d * invDen * C_camp * r_n ^ α ≤ K1 := by
      dsimp [K1]
      calc
        (2 : ℝ) ^ d * invDen * C_camp * r_n ^ α
            ≤ (2 : ℝ) ^ d * invDen * C_camp * (2 * ‖x - y‖ ^ α) := by
                gcongr
        _ = (2 : ℝ) ^ (d + 1) * invDen * C_camp * ‖x - y‖ ^ α := by
            rw [pow_succ']
            ring
    have htailx :
        dist ax lx ≤ (2 : ℝ) ^ d * invDen * C_camp * r_n ^ α := by
      simpa [ax, lx, invDen, q, hrpow_eq, div_eq_mul_inv,
        mul_assoc, mul_left_comm, mul_comm] using
        (dyadicBallAverage_tail_le hα hcamp hρ hρR hsubx n)
    have htaily :
        dist ay ly ≤ (2 : ℝ) ^ d * invDen * C_camp * r_n ^ α := by
      simpa [ay, ly, invDen, q, hrpow_eq, div_eq_mul_inv,
        mul_assoc, mul_left_comm, mul_comm] using
        (dyadicBallAverage_tail_le hα hcamp hρ hρR hsuby n)
    have htailxK : _root_.Dist.dist ax lx ≤ K1 := by
      exact htailx.trans hscaleTail
    have htailyK : _root_.Dist.dist ay ly ≤ K1 := by
      exact htaily.trans hscaleTail
    have havgxy :
        |ax - ay| ≤ (2 : ℝ) ^ (d + 1) * C_camp * r_n ^ α := by
      simpa [ax, ay, dyadicBallAverage, r_n] using
        (ballAverage_sub_ballAverage_sameRadius_le_campanato
          hcamp hrn hrnR hdist_le_rn hsubx_n hsuby_n)
    have hscaleAvg :
        (2 : ℝ) ^ (d + 1) * C_camp * r_n ^ α ≤ K1 := by
      dsimp [K1]
      calc
        (2 : ℝ) ^ (d + 1) * C_camp * r_n ^ α
            ≤ (2 : ℝ) ^ (d + 1) * C_camp * (2 * ‖x - y‖ ^ α) := by
                gcongr
        _ ≤ (2 : ℝ) ^ (d + 1) * C_camp * (invDen * ‖x - y‖ ^ α) := by
                gcongr
        _ = (2 : ℝ) ^ (d + 1) * invDen * C_camp * ‖x - y‖ ^ α := by
                ring
    have havgxyK : |ax - ay| ≤ K1 := by
      exact havgxy.trans hscaleAvg
    have htri : _root_.Dist.dist lx ly ≤ _root_.Dist.dist lx ax + _root_.Dist.dist ax ay + _root_.Dist.dist ay ly := by
      calc
        dist lx ly ≤ _root_.Dist.dist lx ax + _root_.Dist.dist ax ly := dist_triangle _ _ _
        _ ≤ _root_.Dist.dist lx ax + (_root_.Dist.dist ax ay + _root_.Dist.dist ay ly) := by
            gcongr
            exact dist_triangle _ _ _
        _ = _root_.Dist.dist lx ax + _root_.Dist.dist ax ay + _root_.Dist.dist ay ly := by ring
    have hlxax : _root_.Dist.dist lx ax ≤ K1 := by
      simpa [dist_comm] using htailxK
    have haxay : _root_.Dist.dist ax ay ≤ K1 := by
      simpa [Real.dist_eq] using havgxyK
    have hsumK : _root_.Dist.dist lx ax + _root_.Dist.dist ax ay + _root_.Dist.dist ay ly ≤ K1 + K1 + K1 := by
      exact add_le_add (add_le_add hlxax haxay) htailyK
    calc
      |dyadicBallAverageLimit u x (R / 2) - dyadicBallAverageLimit u y (R / 2)|
          = |lx - ly| := by simp [lx, ly, ρ]
      _ ≤ K1 + K1 + K1 := by
          calc
            |lx - ly| = _root_.Dist.dist lx ly := by rw [Real.dist_eq]
            _ ≤ _root_.Dist.dist lx ax + _root_.Dist.dist ax ay + _root_.Dist.dist ay ly := htri
            _ ≤ K1 + K1 + K1 := hsumK
      _ ≤ 4 * K1 := by
          linarith
      _ = CCampanatoHolder d α * C_camp * ‖x - y‖ ^ α := by
          dsimp [K1, CCampanatoHolder, invDen, q]
          ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.dyadicBallAverageLimit_holder_small then
    throwError "Refusing to shadow existing declaration DeGiorgi.dyadicBallAverageLimit_holder_small"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.dyadicBallAverageLimit_holder_small ``Submission.DeGiorgi.dyadicBallAverageLimit_holder_small

lemma dyadicBallAverageLimit_holder_large
    {u : E → ℝ} {x₀ : E} {R α C_camp : ℝ}
    (hα : 0 < α) (hα_le : α ≤ 1) (hR : 0 < R)
    (hcamp : HasCampanatoBound u x₀ R α C_camp)
    {x y : E}
    (hx : x ∈ Metric.ball x₀ (R / 2))
    (hy : y ∈ Metric.ball x₀ (R / 2))
    (hlarge : R / 2 ≤ ‖x - y‖) :
    |dyadicBallAverageLimit u x (R / 2) - dyadicBallAverageLimit u y (R / 2)|
      ≤ CCampanatoHolder d α * C_camp * ‖x - y‖ ^ α := by
  let outer : Set E := Metric.ball x₀ R
  let ρ : ℝ := R / 2
  let q : ℝ := (2 : ℝ) ^ (-α)
  let invDen : ℝ := (1 - q)⁻¹
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρR : ρ ≤ R := by
    dsimp [ρ]
    linarith
  have hC_nonneg : 0 ≤ C_camp := hcamp.nonneg hα hR
  have hq_lt : q < 1 := by
    dsimp [q]
    rw [Real.rpow_neg (by positivity)]
    have h2a : 1 < (2 : ℝ) ^ α := Real.one_lt_rpow (by norm_num) hα
    exact inv_lt_one_of_one_lt₀ h2a
  have hden_pos : 0 < 1 - q := sub_pos.mpr hq_lt
  have hinvDen_nonneg : 0 ≤ invDen := by
    dsimp [invDen]
    positivity
  have h2a_le : (2 : ℝ) ^ α ≤ 2 := by
    simpa using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (2 : ℝ)) hα_le)
  have hq_ge_half : (1 / 2 : ℝ) ≤ q := by
    dsimp [q]
    rw [Real.rpow_neg (by positivity)]
    have h2a_pos : 0 < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
    simpa [one_div] using (one_div_le_one_div_of_le h2a_pos h2a_le)
  have hinvDen_ge_two : (2 : ℝ) ≤ invDen := by
    dsimp [invDen]
    have hden_half : 1 - q ≤ (1 / 2 : ℝ) := by linarith
    have hinv := one_div_le_one_div_of_le hden_pos hden_half
    simpa using hinv
  have hsubx : Metric.ball x ρ ⊆ outer :=
    ball_subset_ball_of_mem_ball_half hx hρ.le le_rfl
  have hsuby : Metric.ball y ρ ⊆ outer :=
    ball_subset_ball_of_mem_ball_half hy hρ.le le_rfl
  let K1 : ℝ := (2 : ℝ) ^ (d + 1) * invDen * C_camp * ‖x - y‖ ^ α
  let ax0 : ℝ := dyadicBallAverage u x ρ 0
  let ay0 : ℝ := dyadicBallAverage u y ρ 0
  let lx : ℝ := dyadicBallAverageLimit u x ρ
  let ly : ℝ := dyadicBallAverageLimit u y ρ
  let m0 : ℝ := ⨍ z in outer, u z ∂volume
  have hρpow_le :
      ρ ^ α ≤ ‖x - y‖ ^ α :=
    Real.rpow_le_rpow hρ.le hlarge hα.le
  have hR_le_two_norm : R ≤ 2 * ‖x - y‖ := by
    have hlarge' : R / 2 ≤ ‖x - y‖ := by simpa [ρ] using hlarge
    linarith
  have hRpow_le_two :
      R ^ α ≤ 2 * ‖x - y‖ ^ α := by
    calc
      R ^ α ≤ (2 * ‖x - y‖) ^ α := by
        exact Real.rpow_le_rpow hR.le hR_le_two_norm hα.le
      _ = (2 : ℝ) ^ α * ‖x - y‖ ^ α := by
          rw [Real.mul_rpow (by positivity) (norm_nonneg _)]
      _ ≤ 2 * ‖x - y‖ ^ α := by
          exact mul_le_mul_of_nonneg_right h2a_le
            (Real.rpow_nonneg (norm_nonneg _) _)
  have hscaleTail :
      (2 : ℝ) ^ d * invDen * C_camp * ρ ^ α ≤ K1 := by
    have hpow_le : (2 : ℝ) ^ d ≤ (2 : ℝ) ^ (d + 1) := by
      rw [pow_succ']
      nlinarith [show 0 ≤ (2 : ℝ) ^ d by positivity]
    dsimp [K1]
    calc
      (2 : ℝ) ^ d * invDen * C_camp * ρ ^ α
          ≤ (2 : ℝ) ^ d * invDen * C_camp * ‖x - y‖ ^ α := by
              gcongr
      _ ≤ (2 : ℝ) ^ (d + 1) * invDen * C_camp * ‖x - y‖ ^ α := by
              have hfac_nonneg : 0 ≤ invDen * C_camp * ‖x - y‖ ^ α := by positivity
              calc
                (2 : ℝ) ^ d * invDen * C_camp * ‖x - y‖ ^ α
                    = (2 : ℝ) ^ d * (invDen * C_camp * ‖x - y‖ ^ α) := by ring
                _ ≤ (2 : ℝ) ^ (d + 1) * (invDen * C_camp * ‖x - y‖ ^ α) := by
                    exact mul_le_mul_of_nonneg_right hpow_le hfac_nonneg
                _ = (2 : ℝ) ^ (d + 1) * invDen * C_camp * ‖x - y‖ ^ α := by ring
  have htailx :
      dist ax0 lx ≤ (2 : ℝ) ^ d * invDen * C_camp * ρ ^ α := by
    simpa [ax0, lx, invDen, q, dyadicBallAverage, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using
      (dyadicBallAverage_tail_le hα hcamp hρ hρR hsubx 0)
  have htaily :
      dist ay0 ly ≤ (2 : ℝ) ^ d * invDen * C_camp * ρ ^ α := by
    simpa [ay0, ly, invDen, q, dyadicBallAverage, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using
      (dyadicBallAverage_tail_le hα hcamp hρ hρR hsuby 0)
  have htailxK : _root_.Dist.dist ax0 lx ≤ K1 := by
    exact htailx.trans hscaleTail
  have htailyK : _root_.Dist.dist ay0 ly ≤ K1 := by
    exact htaily.trans hscaleTail
  have havgx :
      |ax0 - m0| ≤ (2 : ℝ) ^ d * C_camp * R ^ α := by
    simpa [ax0, m0, dyadicBallAverage, ρ] using
      (abs_halfSubballAverage_sub_ballAverage_le_campanato hR hcamp hsubx)
  have havgy :
      |m0 - ay0| ≤ (2 : ℝ) ^ d * C_camp * R ^ α := by
    have htmp := abs_halfSubballAverage_sub_ballAverage_le_campanato hR hcamp hsuby
    simpa [ay0, m0, dyadicBallAverage, ρ, abs_sub_comm] using htmp
  have hscaleOuter :
      (2 : ℝ) ^ d * C_camp * R ^ α ≤ K1 := by
    have hone_le_invDen : (1 : ℝ) ≤ invDen := by linarith
    have hbase_nonneg : 0 ≤ C_camp * ‖x - y‖ ^ α := by positivity
    have hC_mul :
        C_camp * ‖x - y‖ ^ α ≤ invDen * C_camp * ‖x - y‖ ^ α := by
      simpa [one_mul, mul_assoc] using
        (mul_le_mul_of_nonneg_right hone_le_invDen hbase_nonneg)
    dsimp [K1]
    calc
      (2 : ℝ) ^ d * C_camp * R ^ α
          ≤ (2 : ℝ) ^ d * C_camp * (2 * ‖x - y‖ ^ α) := by
              gcongr
      _ = (2 : ℝ) ^ (d + 1) * C_camp * ‖x - y‖ ^ α := by
          rw [pow_succ']
          ring
      _ ≤ (2 : ℝ) ^ (d + 1) * (invDen * C_camp * ‖x - y‖ ^ α) := by
              calc
                (2 : ℝ) ^ (d + 1) * C_camp * ‖x - y‖ ^ α
                    = (2 : ℝ) ^ (d + 1) * (C_camp * ‖x - y‖ ^ α) := by ring
                _ ≤ (2 : ℝ) ^ (d + 1) * (invDen * C_camp * ‖x - y‖ ^ α) := by
                    exact mul_le_mul_of_nonneg_left hC_mul (by positivity)
      _ = (2 : ℝ) ^ (d + 1) * invDen * C_camp * ‖x - y‖ ^ α := by
          ring
  have havgxK : |ax0 - m0| ≤ K1 := by
    exact havgx.trans hscaleOuter
  have havgyK : |m0 - ay0| ≤ K1 := by
    exact havgy.trans hscaleOuter
  have htri :
      dist lx ly ≤ _root_.Dist.dist lx ax0 + _root_.Dist.dist ax0 m0 + _root_.Dist.dist m0 ay0 + _root_.Dist.dist ay0 ly := by
    calc
      dist lx ly ≤ _root_.Dist.dist lx ax0 + _root_.Dist.dist ax0 ly := dist_triangle _ _ _
      _ ≤ _root_.Dist.dist lx ax0 + (_root_.Dist.dist ax0 m0 + _root_.Dist.dist m0 ly) := by
          gcongr
          exact dist_triangle _ _ _
      _ ≤ _root_.Dist.dist lx ax0 + (_root_.Dist.dist ax0 m0 + (_root_.Dist.dist m0 ay0 + _root_.Dist.dist ay0 ly)) := by
          gcongr
          exact dist_triangle _ _ _
      _ = _root_.Dist.dist lx ax0 + _root_.Dist.dist ax0 m0 + _root_.Dist.dist m0 ay0 + _root_.Dist.dist ay0 ly := by ring
  have hlxax0 : _root_.Dist.dist lx ax0 ≤ K1 := by
    simpa [dist_comm] using htailxK
  have hax0m0 : _root_.Dist.dist ax0 m0 ≤ K1 := by
    simpa [Real.dist_eq] using havgxK
  have hm0ay0 : _root_.Dist.dist m0 ay0 ≤ K1 := by
    simpa [Real.dist_eq] using havgyK
  have hsumK :
      dist lx ax0 + _root_.Dist.dist ax0 m0 + _root_.Dist.dist m0 ay0 + _root_.Dist.dist ay0 ly ≤ K1 + K1 + K1 + K1 := by
    exact add_le_add (add_le_add (add_le_add hlxax0 hax0m0) hm0ay0) htailyK
  calc
    |dyadicBallAverageLimit u x (R / 2) - dyadicBallAverageLimit u y (R / 2)|
        = |lx - ly| := by simp [lx, ly, ρ]
    _ ≤ K1 + K1 + K1 + K1 := by
        calc
          |lx - ly| = _root_.Dist.dist lx ly := by rw [Real.dist_eq]
          _ ≤ _root_.Dist.dist lx ax0 + _root_.Dist.dist ax0 m0 + _root_.Dist.dist m0 ay0 + _root_.Dist.dist ay0 ly := htri
          _ ≤ K1 + K1 + K1 + K1 := hsumK
    _ = CCampanatoHolder d α * C_camp * ‖x - y‖ ^ α := by
        dsimp [K1, CCampanatoHolder, invDen, q]
        ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.dyadicBallAverageLimit_holder_large then
    throwError "Refusing to shadow existing declaration DeGiorgi.dyadicBallAverageLimit_holder_large"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.dyadicBallAverageLimit_holder_large ``Submission.DeGiorgi.dyadicBallAverageLimit_holder_large

/-- A Campanato bound determines a Hölder representative up to a.e. equality. -/
theorem campanato_implies_holder
    {u : E → ℝ} {x₀ : E} {R α C_camp : ℝ}
    (hα : 0 < α) (hα_le : α ≤ 1) (hR : 0 < R)
    (hcamp : HasCampanatoBound u x₀ R α C_camp) :
    ∃ v : E → ℝ,
      (∀ᵐ x ∂volume.restrict (Metric.ball x₀ R), v x = u x) ∧
      ∀ x ∈ Metric.ball x₀ (R / 2), ∀ y ∈ Metric.ball x₀ (R / 2),
        |v x - v y| ≤ CCampanatoHolder d α * C_camp * ‖x - y‖ ^ α := by
  classical
  let outer : Set E := Metric.ball x₀ R
  let inner : Set E := Metric.ball x₀ (R / 2)
  let ρ : ℝ := R / 2
  let q : ℝ := (2 : ℝ) ^ (-α)
  let invDen : ℝ := (1 - q)⁻¹
  let v : E → ℝ := fun x =>
    if x ∈ inner then dyadicBallAverageLimit u x ρ else u x
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρR : ρ ≤ R := by
    dsimp [ρ]
    linarith
  have hC_nonneg : 0 ≤ C_camp := hcamp.nonneg hα hR
  have hq_lt : q < 1 := by
    dsimp [q]
    rw [Real.rpow_neg (by positivity)]
    have h2a : 1 < (2 : ℝ) ^ α := Real.one_lt_rpow (by norm_num) hα
    exact inv_lt_one_of_one_lt₀ h2a
  have hden_pos : 0 < 1 - q := sub_pos.mpr hq_lt
  have hinvDen_nonneg : 0 ≤ invDen := by
    dsimp [invDen]
    positivity
  have h2a_le : (2 : ℝ) ^ α ≤ 2 := by
    simpa using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (2 : ℝ)) hα_le)
  have hq_ge_half : (1 / 2 : ℝ) ≤ q := by
    dsimp [q]
    rw [Real.rpow_neg (by positivity)]
    have h2a_pos : 0 < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
    simpa [one_div] using (one_div_le_one_div_of_le h2a_pos h2a_le)
  have hinvDen_ge_two : (2 : ℝ) ≤ invDen := by
    dsimp [invDen]
    have hden_half : 1 - q ≤ (1 / 2 : ℝ) := by linarith
    have hinv := one_div_le_one_div_of_le hden_pos hden_half
    simpa using hinv
  have hinner_eq_global :
      ∀ᵐ x ∂volume, x ∈ inner → dyadicBallAverageLimit u x ρ = u x := by
    have hinner_eq_ae :
        ∀ᵐ x ∂volume.restrict inner, dyadicBallAverageLimit u x ρ = u x := by
      simpa [inner, ρ] using ae_eq_dyadicBallAverageLimit_on_halfBall hα hR hcamp
    rw [_root_.MeasureTheory.ae_restrict_iff' measurableSet_ball] at hinner_eq_ae
    exact hinner_eq_ae
  refine ⟨v, ?_, ?_⟩
  · rw [_root_.MeasureTheory.ae_restrict_iff' measurableSet_ball]
    filter_upwards [hinner_eq_global] with x hx hx_outer
    by_cases hx_inner : x ∈ inner
    · dsimp [v]
      rw [if_pos hx_inner]
      exact hx hx_inner
    · dsimp [v]
      rw [if_neg hx_inner]
  · intro x hx y hy
    have hx_inner : x ∈ inner := by simpa [inner] using hx
    have hy_inner : y ∈ inner := by simpa [inner] using hy
    have hvx : v x = dyadicBallAverageLimit u x ρ := by
      dsimp [v]
      rw [if_pos hx_inner]
    have hvy : v y = dyadicBallAverageLimit u y ρ := by
      dsimp [v]
      rw [if_pos hy_inner]
    by_cases hsmall : ‖x - y‖ ≤ ρ
    · rw [hvx, hvy]
      simpa [ρ] using
        (dyadicBallAverageLimit_holder_small hα hα_le hR hcamp hx hy
          (by simpa [ρ] using hsmall))
    · have hlarge : ρ ≤ ‖x - y‖ := le_of_not_ge hsmall
      rw [hvx, hvy]
      simpa [ρ] using
        (dyadicBallAverageLimit_holder_large hα hα_le hR hcamp hx hy
          (by simpa [ρ] using hlarge))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.campanato_implies_holder then
    throwError "Refusing to shadow existing declaration DeGiorgi.campanato_implies_holder"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.campanato_implies_holder ``Submission.DeGiorgi.campanato_implies_holder

lemma holder_hasCampanatoBound
    {u : E → ℝ} {x₀ : E} {R α C_hold : ℝ}
    (hα : 0 < α) (hC_hold : 0 ≤ C_hold)
    (hhold : ∀ x ∈ Metric.ball x₀ R, ∀ y ∈ Metric.ball x₀ R,
      |u x - u y| ≤ C_hold * ‖x - y‖ ^ α) :
    HasCampanatoBound u x₀ R α (C_hold * (2 : ℝ) ^ α) := by
  intro b
  rcases b with ⟨⟨y, r⟩, hbr⟩
  rcases hbr with ⟨hr, hrR, hsub⟩
  let αnn : ℝ≥0 := ⟨α, hα.le⟩
  let Chold : ℝ≥0 := ⟨C_hold, hC_hold⟩
  let B : Set E := Metric.ball y r
  let avg : ℝ := ⨍ z in B, u z ∂volume
  have hBmeas : MeasurableSet B := by
    simpa [B] using (Metric.isOpen_ball.measurableSet : MeasurableSet (Metric.ball y r))
  have hyB : y ∈ B := by
    change y ∈ Metric.ball y r
    exact Metric.mem_ball_self hr
  have hyR : y ∈ Metric.ball x₀ R := hsub hyB
  have hBfin : _root_.MeasureTheory.MeasureSpace.volume B ≠ ∞ := by
    simpa [B] using (_root_.MeasureTheory.measure_ball_lt_top (μ := _root_.MeasureTheory.MeasureSpace.volume) (x := y) (r := r)).ne
  have hB0 : _root_.MeasureTheory.MeasureSpace.volume B ≠ 0 := by
    exact (_root_.Metric.measure_ball_pos (μ := _root_.MeasureTheory.MeasureSpace.volume) y hr).ne'
  have hholderB : HolderOnWith Chold αnn u B := by
    intro x hx z hz
    have hChold : ENNReal.ofReal C_hold = (Chold : ℝ≥0∞) := by
      unfold Chold
      exact ENNReal.ofReal_eq_coe_nnreal hC_hold
    have hdist0 : ENNReal.ofReal (_root_.Dist.dist (u x) (u z)) ≤
        ENNReal.ofReal C_hold * ENNReal.ofReal (_root_.Dist.dist x z) ^ α := by
      rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg hα.le,
        ← ENNReal.ofReal_mul hC_hold]
      exact ENNReal.ofReal_le_ofReal <| by
        simpa [Real.dist_eq, dist_eq_norm] using hhold x (hsub hx) z (hsub hz)
    have hdist : ENNReal.ofReal (_root_.Dist.dist (u x) (u z)) ≤
        (Chold : ℝ≥0∞) * ENNReal.ofReal (_root_.Dist.dist x z) ^ α := by
      calc
        ENNReal.ofReal (_root_.Dist.dist (u x) (u z))
            ≤ ENNReal.ofReal C_hold * ENNReal.ofReal (_root_.Dist.dist x z) ^ α := hdist0
        _ = (Chold : ℝ≥0∞) * ENNReal.ofReal (_root_.Dist.dist x z) ^ α := by rw [hChold]
    rw [edist_dist, edist_dist]
    rw [show (αnn : ℝ) = α by rfl]
    exact hdist
  have hcontB : ContinuousOn u B := hholderB.continuousOn (show 0 < αnn by exact hα)
  have hu_int : _root_.MeasureTheory.IntegrableOn u B volume := by
    have hBfin_lt : _root_.MeasureTheory.MeasureSpace.volume B < ∞ := lt_top_iff_ne_top.2 hBfin
    refine IntegrableOn.of_bound hBfin_lt (hcontB.aestronglyMeasurable hBmeas)
      (‖u y‖ + C_hold * r ^ α) ?_
    filter_upwards [_root_.MeasureTheory.self_mem_ae_restrict hBmeas] with z hz
    have hzR : z ∈ Metric.ball x₀ R := hsub hz
    have hdist_le : _root_.Dist.dist z y ≤ r := le_of_lt (by simpa [B] using hz)
    have hrpow_le : _root_.Dist.dist z y ^ α ≤ r ^ α :=
      Real.rpow_le_rpow dist_nonneg hdist_le hα.le
    have hdiff : |u z - u y| ≤ C_hold * r ^ α := by
      calc
        |u z - u y| ≤ C_hold * _root_.Dist.dist z y ^ α := by
          change |u z - u y| ≤ C_hold * ‖z - y‖ ^ α
          exact hhold z hzR y hyR
        _ ≤ C_hold * r ^ α := by
          exact mul_le_mul_of_nonneg_left hrpow_le hC_hold
    calc
      ‖u z‖ ≤ |u z - u y| + ‖u y‖ := by
        simpa [Real.dist_eq] using (dist_triangle (u z) (u y) 0)
      _ ≤ ‖u y‖ + C_hold * r ^ α := by
          linarith
  refine ⟨hu_int, ?_⟩
  have hpoint : ∀ x ∈ B, |u x - avg| ≤ C_hold * (2 * r) ^ α := by
    obtain ⟨c, hcB, havg⟩ := MeasureTheory.exists_eq_setAverage
      (μ := _root_.MeasureTheory.MeasureSpace.volume) (s := B) (f := u) (_root_.Metric.isConnected_ball hr) hcontB hu_int hBfin hB0
    intro x hx
    have hxR : x ∈ Metric.ball x₀ R := hsub hx
    have hcR : c ∈ Metric.ball x₀ R := hsub hcB
    have hdist_le : _root_.Dist.dist x c ≤ 2 * r := by
      have hxy : _root_.Dist.dist x y < r := by simpa [B] using hx
      have hyc : _root_.Dist.dist c y < r := by simpa [B] using hcB
      have hyc' : _root_.Dist.dist y c < r := by simpa [dist_comm] using hyc
      have htri : _root_.Dist.dist x c ≤ _root_.Dist.dist x y + _root_.Dist.dist y c := dist_triangle _ _ _
      have hsum : _root_.Dist.dist x y + _root_.Dist.dist y c < 2 * r := by
        linarith
      exact htri.trans hsum.le
    calc
      |u x - avg| = |u x - u c| := by
        change |u x - (⨍ z in B, u z ∂volume)| = |u x - u c|
        rw [← havg]
      _ ≤ C_hold * _root_.Dist.dist x c ^ α := by
          change |u x - u c| ≤ C_hold * ‖x - c‖ ^ α
          exact hhold x hxR c hcR
      _ ≤ C_hold * (2 * r) ^ α := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow dist_nonneg hdist_le hα.le) hC_hold
  have hAvgBound : (⨍ x in B, |u x - avg| ∂volume) ≤ C_hold * (2 * r) ^ α := by
    have hg_int : _root_.MeasureTheory.IntegrableOn (fun x => |u x - avg|) B volume := by
      change _root_.MeasureTheory.Integrable (fun x => ‖u x - avg‖) (volume.restrict B)
      exact (hu_int.sub (_root_.MeasureTheory.integrableOn_const hBfin)).norm
    obtain ⟨x', hx'B, hAvgLe⟩ := MeasureTheory.exists_setAverage_le
        (μ := _root_.MeasureTheory.MeasureSpace.volume) (s := B) (f := fun x => |u x - avg|) hB0 hBfin hg_int
    exact hAvgLe.trans (hpoint x' hx'B)
  have hrpow :
      r⁻¹ ^ α * (2 * r) ^ α = (r⁻¹ * (2 * r)) ^ α := by
    simpa using
      (Real.mul_rpow (x := r⁻¹) (y := 2 * r) (z := α)
        (inv_nonneg.mpr hr.le) (by positivity)).symm
  have hmul : r⁻¹ * (2 * r) = (2 : ℝ) := by
    calc
      r⁻¹ * (2 * r) = 2 * (r⁻¹ * r) := by ring
      _ = 2 := by rw [inv_mul_cancel₀ (ne_of_gt hr), mul_one]
  calc
    r⁻¹ ^ α * (⨍ x in B, |u x - avg| ∂volume)
        ≤ r⁻¹ ^ α * (C_hold * (2 * r) ^ α) := by
        exact mul_le_mul_of_nonneg_left hAvgBound (Real.rpow_nonneg (inv_nonneg.mpr hr.le) _)
    _ = C_hold * (r⁻¹ ^ α * (2 * r) ^ α) := by ring
    _ = C_hold * ((r⁻¹ * (2 * r)) ^ α) := by rw [hrpow]
    _ = C_hold * (2 : ℝ) ^ α := by rw [hmul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.holder_hasCampanatoBound then
    throwError "Refusing to shadow existing declaration DeGiorgi.holder_hasCampanatoBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.holder_hasCampanatoBound ``Submission.DeGiorgi.holder_hasCampanatoBound

/-- A Hölder continuous function has controlled Campanato seminorm. -/
theorem holder_implies_campanato
    {u : E → ℝ} {x₀ : E} {R α C_hold : ℝ}
    (hα : 0 < α) (hR : 0 < R) (hC_hold : 0 ≤ C_hold)
    (hhold : ∀ x ∈ Metric.ball x₀ R, ∀ y ∈ Metric.ball x₀ R,
      |u x - u y| ≤ C_hold * ‖x - y‖ ^ α) :
    campanatoSeminorm u x₀ R α ≤ C_hold * (2 : ℝ) ^ α := by
  exact (holder_hasCampanatoBound hα hC_hold hhold).campanatoSeminorm_le hR

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.holder_implies_campanato then
    throwError "Refusing to shadow existing declaration DeGiorgi.holder_implies_campanato"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.holder_implies_campanato ``Submission.DeGiorgi.holder_implies_campanato

end DeGiorgi
