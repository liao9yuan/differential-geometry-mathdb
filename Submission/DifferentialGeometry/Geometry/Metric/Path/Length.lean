import Submission.DifferentialGeometry.Topology.Manifold.Path.Regularity
import Mathlib.Geometry.Manifold.Riemannian.PathELength

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.Set
open scoped _root_.ENNReal _root_.Manifold _root_.Topology

namespace Path
open _root_.Path

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [∀ x : M, ENorm (TangentSpace I x)]

open _root_.Path in
noncomputable def riemannianELength {x y : M} (γ : Path x y) : ENNReal :=
  Manifold.pathELength I γ.extend 0 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Path.riemannianELength then
    throwError "Refusing to shadow existing declaration Path.riemannianELength"
  Lean.modifyEnv fun env => Lean.addAlias env `Path.riemannianELength ``Submission.Path.riemannianELength

open _root_.Path in
@[simp]
theorem riemannianELength_refl
    [∀ z : M, ENormSMulClass Real (TangentSpace I z)]
    (x : M) :
    riemannianELength (I := I) (Path.refl x) = 0 := by
  rw [riemannianELength, Path.refl_extend,
    Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  change
    ∫⁻ _ : Real in Set.Icc 0 1,
      ‖(mfderiv 𝓘(Real, Real) I (fun _ : Real => x) _) 1‖ₑ = 0
  have hzero : ‖(0 : TangentSpace I x)‖ₑ = 0 := by
    calc
      _ = ‖(0 : Real) • (0 : TangentSpace I x)‖ₑ := by rw [zero_smul]
      _ = ‖(0 : Real)‖ₑ * ‖(0 : TangentSpace I x)‖ₑ := enorm_smul _ _
      _ = 0 := by simp
  simp only [mfderiv_const, zero_apply, hzero,
    MeasureTheory.lintegral_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Path.riemannianELength_refl then
    throwError "Refusing to shadow existing declaration Path.riemannianELength_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `Path.riemannianELength_refl ``Submission.Path.riemannianELength_refl

section PathLength

variable [∀ z : M, ENormSMulClass Real (TangentSpace I z)]

open _root_.Path in
theorem riemannianELength_symm {x y : M} {p : Path x y}
    (hp : MDifferentiableOn 𝓘(Real, Real) I p.extend (_root_.Set.Icc 0 1)) :
    riemannianELength (I := I) p.symm = riemannianELength (I := I) p := by
  unfold riemannianELength
  rw [Path.extend_symm]
  simpa only [Function.comp_def, sub_self, sub_zero] using
    (Manifold.pathELength_comp_of_antitoneOn
      (I := I) (γ := p.extend)
      (f := fun t : Real => 1 - t)
      (a := 0) (b := 1) zero_le_one
      (by
        intro a _ b _ hab
        dsimp
        linarith)
      (by fun_prop)
      (by
        simpa using
          hp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Path.riemannianELength_symm then
    throwError "Refusing to shadow existing declaration Path.riemannianELength_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `Path.riemannianELength_symm ``Submission.Path.riemannianELength_symm

open _root_.Path in
theorem riemannianELength_trans {x y z : M}
    {p : Path x y} {q : Path y z}
    (hp : MDifferentiableOn 𝓘(Real, Real) I p.extend (_root_.Set.Icc 0 1))
    (hq : MDifferentiableOn 𝓘(Real, Real) I q.extend (_root_.Set.Icc 0 1)) :
    riemannianELength (I := I) (p.trans q) =
      riemannianELength (I := I) p + riemannianELength (I := I) q := by
  have hleft :
      Manifold.pathELength I (p.trans q).extend 0 (1 / 2) =
        Manifold.pathELength I p.extend 0 1 := by
    calc
      _ = Manifold.pathELength I
          (p.extend ∘ fun t : Real => 2 * t) 0 (1 / 2) := by
        apply Manifold.pathELength_congr
        intro t ht
        simpa only [Function.comp_apply] using
          Path.extend_trans_of_le_half p q ht.2
      _ = _ := by
        convert Manifold.pathELength_comp_of_monotoneOn
          (I := I) (γ := p.extend)
          (f := fun t : Real => 2 * t)
          (a := 0) (b := 1 / 2)
          (by norm_num)
          (by
            intro a _ b _ hab
            dsimp
            linarith)
          (by fun_prop)
          (by
            simpa using
              hp)
          using 1; norm_num
  have hright :
      Manifold.pathELength I (p.trans q).extend (1 / 2) 1 =
        Manifold.pathELength I q.extend 0 1 := by
    calc
      _ = Manifold.pathELength I
          (q.extend ∘ fun t : Real => 2 * t - 1) (1 / 2) 1 := by
        apply Manifold.pathELength_congr
        intro t ht
        simpa only [Function.comp_apply] using
          Path.extend_trans_of_half_le p q ht.1
      _ = _ := by
        convert Manifold.pathELength_comp_of_monotoneOn
          (I := I) (γ := q.extend)
          (f := fun t : Real => 2 * t - 1)
          (a := 1 / 2) (b := 1)
          (by norm_num)
          (by
            intro a _ b _ hab
            dsimp
            linarith)
          (by fun_prop)
          (by
            convert hq using 1
            norm_num)
          using 1; norm_num
  change
    Manifold.pathELength I (p.trans q).extend 0 1 =
      Manifold.pathELength I p.extend 0 1 +
        Manifold.pathELength I q.extend 0 1
  calc
    _ = Manifold.pathELength I (p.trans q).extend 0 (1 / 2) +
        Manifold.pathELength I (p.trans q).extend (1 / 2) 1 :=
      (Manifold.pathELength_add
        (I := I) (γ := (p.trans q).extend)
        (by norm_num) (by norm_num)).symm
    _ = _ := by rw [hleft, hright]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Path.riemannianELength_trans then
    throwError "Refusing to shadow existing declaration Path.riemannianELength_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `Path.riemannianELength_trans ``Submission.Path.riemannianELength_trans

end PathLength

end Path

namespace Manifold
open _root_.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [∀ x : M, ENorm (TangentSpace I x)]

variable [∀ z : M, ENormSMulClass Real (TangentSpace I z)]

open _root_.Manifold in
theorem exists_path_isContMDiffWithSittingInstants_of_riemannianEDist_lt
    {x y : M} {r : ENNReal}
    (hxy : Manifold.riemannianEDist I x y < r) :
    ∃ p : Path x y,
      Path.IsContMDiffWithSittingInstants (I := I) 1 p ∧
      Path.riemannianELength (I := I) p < r := by
  obtain ⟨γ, hγ0, hγ1, hγC1, hγlen, hγflat0, hγflat1⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt
      hxy (a := (0 : Real)) (b := (1 : Real)) zero_lt_one
  let p : Path x y := {
    toFun := fun t => γ t
    continuous_toFun := hγC1.continuous.comp continuous_subtype_val
    source' := hγ0
    target' := hγ1 }
  let tail : Real → M :=
    Set.piecewise (Set.Iic (1 : Real)) γ (fun _ => y)
  have htailC1 : ContMDiff 𝓘(Real, Real) I 1 tail := by
    exact ContMDiff.piecewise_Iic hγC1 contMDiff_const hγflat1
  have htail0 :
      tail =ᶠ[𝓝 (0 : Real)] γ := by
    filter_upwards [eventually_lt_nhds zero_lt_one] with t ht
    exact (Set.Iic (1 : Real)).piecewise_eq_of_mem γ (fun _ => y) ht.le
  have hjoin0 :
      (fun _ : Real => x) =ᶠ[𝓝 (0 : Real)] tail :=
    hγflat0.symm.trans htail0.symm
  have hext :
      p.extend =
        Set.piecewise (Set.Iic (0 : Real)) (fun _ => x) tail := by
    funext t
    by_cases ht0 : t ≤ 0
    · rw [p.extend_of_le_zero ht0]
      exact ((Set.Iic (0 : Real)).piecewise_eq_of_mem
        (fun _ => x) tail ht0).symm
    · have h0t : 0 ≤ t := (not_le.mp ht0).le
      rw [(Set.Iic (0 : Real)).piecewise_eq_of_notMem
        (fun _ => x) tail ht0]
      by_cases ht1 : t ≤ 1
      · have ht : t ∈ Set.Icc (0 : Real) 1 := ⟨h0t, ht1⟩
        rw [p.extend_apply ht]
        change γ t = tail t
        exact ((Set.Iic (1 : Real)).piecewise_eq_of_mem
          γ (fun _ => y) ht1).symm
      · have h1t : 1 ≤ t := (not_le.mp ht1).le
        rw [p.extend_of_one_le h1t]
        exact ((Set.Iic (1 : Real)).piecewise_eq_of_notMem
          γ (fun _ => y) ht1).symm
  have hpflat0 :
      p.extend =ᶠ[𝓝 (0 : Real)] (fun _ => x) := by
    rw [hext]
    filter_upwards [hjoin0, eventually_lt_nhds zero_lt_one] with t hjoin ht
    by_cases ht0 : t ≤ 0
    · exact (Set.Iic (0 : Real)).piecewise_eq_of_mem
        (fun _ => x) tail ht0
    · rw [(Set.Iic (0 : Real)).piecewise_eq_of_notMem
        (fun _ => x) tail ht0]
      exact hjoin.symm
  have hpflat1 :
      p.extend =ᶠ[𝓝 (1 : Real)] (fun _ => y) := by
    rw [hext]
    filter_upwards [hγflat1, eventually_gt_nhds zero_lt_one] with t hγt ht
    have ht0 : ¬ t ≤ 0 := not_le.mpr ht
    rw [(Set.Iic (0 : Real)).piecewise_eq_of_notMem
      (fun _ => x) tail ht0]
    by_cases ht1 : t ≤ 1
    · change Set.piecewise (Set.Iic (1 : Real)) γ (fun _ => y) t = y
      rw [(Set.Iic (1 : Real)).piecewise_eq_of_mem
        γ (fun _ => y) ht1]
      exact hγt
    · change Set.piecewise (Set.Iic (1 : Real)) γ (fun _ => y) t = y
      exact (Set.Iic (1 : Real)).piecewise_eq_of_notMem
        γ (fun _ => y) ht1
  refine ⟨p, {
    contMDiff := ?_
    eventuallyEq_zero := hpflat0
    eventuallyEq_one := hpflat1 }, ?_⟩
  · rw [hext]
    exact ContMDiff.piecewise_Iic contMDiff_const htailC1 hjoin0
  · change Manifold.pathELength I p.extend 0 1 < r
    calc
      Manifold.pathELength I p.extend 0 1 =
          Manifold.pathELength I γ 0 1 := by
        apply Manifold.pathELength_congr
        intro t ht
        rw [p.extend_apply ht]
        rfl
      _ < r := hγlen

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_path_isContMDiffWithSittingInstants_of_riemannianEDist_lt then
    throwError "Refusing to shadow existing declaration Manifold.exists_path_isContMDiffWithSittingInstants_of_riemannianEDist_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_path_isContMDiffWithSittingInstants_of_riemannianEDist_lt ``Submission.Manifold.exists_path_isContMDiffWithSittingInstants_of_riemannianEDist_lt

end Manifold
