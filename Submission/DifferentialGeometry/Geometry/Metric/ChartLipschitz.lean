import Mathlib.Geometry.Manifold.Riemannian.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian

open _root_.Bundle _root_.Filter _root_.Manifold _root_.MeasureTheory _root_.Metric _root_.Set
open scoped _root_.ENNReal _root_.Manifold _root_.NNReal _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace

theorem exists_lipschitzOnWith_extChartAt (q : M) :
    ∃ K : ℝ≥0, ∃ s ∈ 𝓝 q,
      LipschitzOnWith K (extChartAt I q) s := by
  rcases eventually_enorm_mfderiv_extChartAt_lt I q with
    ⟨C, hC, hCevent⟩
  let good : Set M :=
    {x | let L : TangentSpace I x →L[Real] E := mfderiv I 𝓘(Real, E) (extChartAt I q) x
         ‖L‖ₑ < C} ∩
      (extChartAt I q).source
  have hgood : good ∈ 𝓝 q := by
    exact _root_.Filter.inter_mem hCevent (extChartAt_source_mem_nhds (I := I) q)
  obtain ⟨r, hr, hrsub⟩ :=
    setOfPred_riemannianEDist_lt_subset_nhds (I := I) hgood
  let ρ : ℝ≥0 := r / 8
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    positivity
  have hρr : ρ < r := by
    exact div_lt_self hr (by norm_num)
  let s : Set M := {x | _root_.Manifold.riemannianEDist I q x < ρ}
  have hs : s ∈ 𝓝 q := by
    exact eventually_riemannianEDist_lt I q (by exact_mod_cast hρ)
  refine ⟨2 * C, s, hs, ?_⟩
  intro y hy z hz
  have hyρ : _root_.Manifold.riemannianEDist I q y < (ρ : ℝ≥0∞) := by
    simpa only [s, Set.mem_ofPred_eq] using hy
  have hzρ : _root_.Manifold.riemannianEDist I q z < (ρ : ℝ≥0∞) := by
    simpa only [s, Set.mem_ofPred_eq] using hz
  let d : ℝ≥0∞ := _root_.Manifold.riemannianEDist I y z
  by_cases hd : d = 0
  · have hyGood : y ∈ good := hrsub (hyρ.trans (by exact_mod_cast hρr))
    have hzGood : z ∈ good := hrsub (hzρ.trans (by exact_mod_cast hρr))
    have hySrc : y ∈ (extChartAt I q).source := hyGood.2
    have hzSrc : z ∈ (extChartAt I q).source := hzGood.2
    have hedist : _root_.EDist.edist y z = 0 := by
      rw [IsRiemannianManifold.out (I := I) y z]
      exact hd
    have hsep : Inseparable y z := EMetric.inseparable_iff.mpr hedist
    have himg : Inseparable (extChartAt I q y) (extChartAt I q z) :=
      hsep.map_of_continuousOn (continuousOn_extChartAt (I := I) q)
        hySrc hzSrc
    rw [himg.edist_eq_zero, hedist, _root_.MulZeroClass.mul_zero]
  · have hdpos : 0 < d := bot_lt_iff_ne_bot.mpr hd
    have hdle : d ≤ (ρ : ℝ≥0∞) + ρ := by
      calc
        d ≤ _root_.Manifold.riemannianEDist I y q + _root_.Manifold.riemannianEDist I q z := by
          simpa only [d] using
            (_root_.Manifold.riemannianEDist_triangle (I := I) (x := y) (y := q) (z := z))
        _ = _root_.Manifold.riemannianEDist I q y + _root_.Manifold.riemannianEDist I q z := by
          rw [_root_.Manifold.riemannianEDist_comm]
        _ ≤ (ρ : ℝ≥0∞) + ρ := add_le_add hyρ.le hzρ.le
    have hdtop : d ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) hdle
    let delta : ℝ≥0 := d.toNNReal
    have hdelta : (delta : ℝ≥0∞) = d := by
      simpa only [delta] using ENNReal.coe_toNNReal hdtop
    have hdeltapos : 0 < delta := by
      exact_mod_cast (show (0 : ℝ≥0∞) < (delta : ℝ≥0∞) by
        simpa only [hdelta] using hdpos)
    have hdeltalt : delta < 2 * ρ := by
      have hdeltaltE : (delta : ℝ≥0∞) < (2 * ρ : ℝ≥0) := by
        rw [hdelta]
        calc
          d ≤ _root_.Manifold.riemannianEDist I y q + _root_.Manifold.riemannianEDist I q z := by
            simpa only [d] using
              (_root_.Manifold.riemannianEDist_triangle (I := I) (x := y) (y := q) (z := z))
          _ = _root_.Manifold.riemannianEDist I q y + _root_.Manifold.riemannianEDist I q z := by
            rw [_root_.Manifold.riemannianEDist_comm]
          _ < (ρ : ℝ≥0∞) + ρ := ENNReal.add_lt_add hyρ hzρ
          _ = (2 * ρ : ℝ≥0) := by
            norm_num [two_mul]
      exact_mod_cast hdeltaltE
    have hstay : ρ + 2 * delta < r := by
      exact_mod_cast (show (ρ : Real) + 2 * (delta : Real) < (r : Real) by
        have hreal : (delta : Real) < 2 * (ρ : Real) := by
          exact_mod_cast hdeltalt
        have hρreal : (ρ : Real) = (r : Real) / 8 := by
          simp only [ρ, NNReal.coe_div, NNReal.coe_ofNat]
        have hrreal : 0 < (r : Real) := by exact_mod_cast hr
        rw [hρreal] at hreal ⊢
        nlinarith)
    have hdpath : d < (2 * delta : ℝ≥0) := by
      rw [← hdelta]
      exact_mod_cast (show delta < 2 * delta by
        rw [two_mul]
        exact lt_add_of_pos_right delta hdeltapos)
    obtain ⟨gamma, hgamma0, hgamma1, hgamma, hlen, -, -⟩ :=
      _root_.Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hdpath zero_lt_one
    have hgammaGood : ∀ t ∈ _root_.Set.Icc (0 : Real) 1, gamma t ∈ good := by
      intro t ht
      have hprefix :
          riemannianEDist I y (gamma t) < (2 * delta : ℝ≥0) := by
        calc
          riemannianEDist I y (gamma t) ≤ _root_.Manifold.pathELength I gamma 0 t :=
            _root_.Manifold.riemannianEDist_le_pathELength hgamma.contMDiffOn hgamma0 rfl ht.1
          _ ≤ _root_.Manifold.pathELength I gamma 0 1 := _root_.Manifold.pathELength_mono le_rfl ht.2
          _ < (2 * delta : ℝ≥0) := hlen
      apply hrsub
      calc
        _root_.Manifold.riemannianEDist I q (gamma t) ≤
            riemannianEDist I q y + _root_.Manifold.riemannianEDist I y (gamma t) :=
          _root_.Manifold.riemannianEDist_triangle
        _ < (ρ : ℝ≥0∞) + (2 * delta : ℝ≥0) :=
          ENNReal.add_lt_add hyρ hprefix
        _ < (r : ℝ≥0∞) := by exact_mod_cast hstay
    let F : Real → E := extChartAt I q ∘ gamma
    have hF : ContDiffOn Real 1 F (_root_.Set.Icc (0 : Real) 1) := by
      rw [← contMDiffOn_iff_contDiffOn]
      apply contMDiffOn_extChartAt.comp (I' := I)
          (t := (chartAt H q).source) hgamma.contMDiffOn
      intro t ht
      change gamma t ∈ (chartAt H q).source
      simpa only [extChartAt_source] using (hgammaGood t ht).2
    calc
      _root_.EDist.edist (extChartAt I q y) (extChartAt I q z) =
          ‖F 1 - F 0‖ₑ := by
        rw [_root_.PseudoEMetricSpace.edist_comm, edist_eq_enorm_sub]
        simp only [F, Function.comp_apply, hgamma0, hgamma1]
      _ ≤ ∫⁻ t in _root_.Set.Icc (0 : Real) 1,
          ‖derivWithin F (_root_.Set.Icc (0 : Real) 1) t‖ₑ :=
        enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hF zero_le_one
      _ = ∫⁻ t in _root_.Set.Icc (0 : Real) 1,
          ‖mfderiv[_root_.Set.Icc (0 : Real) 1] F t 1‖ₑ := by
        simp_rw [← fderivWithin_derivWithin, mfderivWithin_eq_fderivWithin]
        rfl
      _ ≤ ∫⁻ t in _root_.Set.Icc (0 : Real) 1,
          C * ‖mfderiv[_root_.Set.Icc (0 : Real) 1] gamma t 1‖ₑ := by
        apply _root_.MeasureTheory.setLIntegral_mono' measurableSet_Icc
        intro t ht
        have hcomp : mfderiv[_root_.Set.Icc (0 : Real) 1] F t =
            (mfderiv I 𝓘(Real, E) (extChartAt I q) (gamma t)) ∘L
              (mfderiv[_root_.Set.Icc (0 : Real) 1] gamma t) := by
          apply mfderiv_comp_mfderivWithin
          · exact mdifferentiableAt_extChartAt (by
              simpa only [extChartAt_source] using (hgammaGood t ht).2)
          · exact (hgamma.mdifferentiable one_ne_zero).mdifferentiableOn _ ht
          · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
            exact uniqueDiffOn_Icc zero_lt_one t ht
        have happly : mfderiv[_root_.Set.Icc (0 : Real) 1] F t 1 =
            (mfderiv I 𝓘(Real, E) (extChartAt I q) (gamma t))
              (mfderiv[_root_.Set.Icc (0 : Real) 1] gamma t 1) := congr($hcomp 1)
        rw [happly]
        apply (ContinuousLinearMap.le_opENorm _ _).trans
        gcongr
        exact (hgammaGood t ht).1.le
      _ = C * _root_.Manifold.pathELength I gamma 0 1 := by
        rw [_root_.MeasureTheory.lintegral_const_mul' _ _ ENNReal.coe_ne_top,
          _root_.Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
      _ ≤ C * (2 * delta : ℝ≥0) := mul_right_mono hlen.le
      _ = ((2 * C : ℝ≥0) : ℝ≥0∞) * _root_.EDist.edist y z := by
        rw [IsRiemannianManifold.out (I := I) y z]
        change (C : ℝ≥0∞) * ((2 * delta : ℝ≥0) : ℝ≥0∞) =
          ((2 * C : ℝ≥0) : ℝ≥0∞) * d
        rw [← hdelta]
        exact_mod_cast (show C * (2 * delta) = (2 * C) * delta by ring)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.exists_lipschitzOnWith_extChartAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.exists_lipschitzOnWith_extChartAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.exists_lipschitzOnWith_extChartAt ``Submission.DifferentialGeometry.Geometry.Riemannian.exists_lipschitzOnWith_extChartAt

theorem locallyLipschitzOn_extChartAt (p : M) :
    LocallyLipschitzOn (extChartAt I p).source (extChartAt I p) := by
  intro q hq
  obtain ⟨K, s, hs, hKs⟩ := exists_lipschitzOnWith_extChartAt (I := I) q
  let F : E → E := extChartAt I p ∘ (extChartAt I q).symm
  have hqdom : extChartAt I q q ∈
      ((extChartAt I q).symm ≫ extChartAt I p).source := by
    rw [PartialEquiv.trans_source]
    refine ⟨(extChartAt I q).map_source
      (mem_extChartAt_source (I := I) q), ?_⟩
    change (extChartAt I q).symm (extChartAt I q q) ∈
      (extChartAt I p).source
    rw [(extChartAt I q).left_inv (mem_extChartAt_source (I := I) q)]
    exact hq
  have hF : ContDiffWithinAt Real 1 F (_root_.Set.range I) (extChartAt I q q) := by
    simpa only [F] using
      contDiffWithinAt_ext_coord_change (I := I) p q hqdom
  obtain ⟨L, t, ht, hLt⟩ := hF.exists_lipschitzOnWith I.convex_range
  have htpre : (extChartAt I q) ⁻¹' t ∈ 𝓝 q :=
    extChartAt_preimage_mem_nhds_of_mem_nhdsWithin
      (mem_extChartAt_source (I := I) q) ht
  let u : Set M := s ∩ (extChartAt I q) ⁻¹' t ∩
    (extChartAt I q).source ∩ (extChartAt I p).source
  have hu0 : s ∩ (extChartAt I q) ⁻¹' t ∩
      (extChartAt I q).source ∈ 𝓝 q :=
    inter_mem (_root_.Filter.inter_mem hs htpre) (extChartAt_source_mem_nhds (I := I) q)
  have hu : u ∈ 𝓝[(extChartAt I p).source] q := by
    exact _root_.Filter.inter_mem (mem_nhdsWithin_of_mem_nhds hu0) self_mem_nhdsWithin
  refine ⟨L * K, u, hu, ?_⟩
  intro y hy z hz
  rcases hy with ⟨⟨⟨hys, hyt⟩, hysrc⟩, _hyp⟩
  rcases hz with ⟨⟨⟨hzs, hzt⟩, hzsrc⟩, _hzp⟩
  have hyInv : (extChartAt I q).symm (extChartAt I q y) = y :=
    (extChartAt I q).left_inv hysrc
  have hzInv : (extChartAt I q).symm (extChartAt I q z) = z :=
    (extChartAt I q).left_inv hzsrc
  calc
    _root_.EDist.edist (extChartAt I p y) (extChartAt I p z) =
        edist (F (extChartAt I q y)) (F (extChartAt I q z)) := by
      simp only [F, Function.comp_apply, hyInv, hzInv]
    _ ≤ L * _root_.EDist.edist (extChartAt I q y) (extChartAt I q z) := hLt hyt hzt
    _ ≤ L * (K * _root_.EDist.edist y z) := mul_right_mono (hKs hys hzs)
    _ = ((L * K : ℝ≥0) : ℝ≥0∞) * _root_.EDist.edist y z := by
      change (L : ℝ≥0∞) * ((K : ℝ≥0∞) * _root_.EDist.edist y z) =
        ((L : ℝ≥0∞) * K) * _root_.EDist.edist y z
      exact (mul_assoc _ _ _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.locallyLipschitzOn_extChartAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.locallyLipschitzOn_extChartAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.locallyLipschitzOn_extChartAt ``Submission.DifferentialGeometry.Geometry.Riemannian.locallyLipschitzOn_extChartAt

variable {N : Type*} [PseudoMetricSpace N] [ChartedSpace H N]
  [IsManifold I 1 N]
  [RiemannianBundle (fun x : N ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : N ↦ TangentSpace I x)]
  [IsRiemannianManifold I N]

theorem exists_lipschitzOnWith_extChartAt_of_isCompact (p : N) {K : Set N} (hK : IsCompact K)
    (hKsrc : K ⊆ (extChartAt I p).source) :
    ∃ C : ℝ≥0, LipschitzOnWith C (extChartAt I p) K :=
  ((locallyLipschitzOn_extChartAt (I := I) p).mono hKsrc).exists_lipschitzOnWith_of_compact hK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.exists_lipschitzOnWith_extChartAt_of_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.exists_lipschitzOnWith_extChartAt_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.exists_lipschitzOnWith_extChartAt_of_isCompact ``Submission.DifferentialGeometry.Geometry.Riemannian.exists_lipschitzOnWith_extChartAt_of_isCompact

end DifferentialGeometry.Geometry.Riemannian
