import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.L2
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Geometry.Manifold.BumpFunction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.BoundedContinuousFunction _root_.MeasureTheory.BoundedContinuousFunction
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace BoundedContinuousFunction

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

def SmoothScalar.toContinuousMap {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) : C(M, ℝ) :=
  ⟨f.toFun, f.smooth.continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContinuousMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContinuousMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContinuousMap ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContinuousMap

omit [Module.Finite ℝ E] [I.Boundaryless] [T2Space M] [CompactSpace M] in
@[simp] lemma SmoothScalar.toContinuousMap_apply {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) (x : M) :
    f.toContinuousMap x = f.toFun x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContinuousMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContinuousMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContinuousMap_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContinuousMap_apply

omit [Module.Finite ℝ E] [I.Boundaryless] [T2Space M] [CompactSpace M] in
@[simp] lemma SmoothScalar.toContinuousMap_zero {g : SmoothRiemannianMetric I M} :
    (0 : SmoothScalar g).toContinuousMap = (0 : C(M, ℝ)) := by
  ext x
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContinuousMap_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContinuousMap_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContinuousMap_zero ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContinuousMap_zero

omit [Module.Finite ℝ E] [I.Boundaryless] [T2Space M] [CompactSpace M] in
@[simp] lemma SmoothScalar.toContinuousMap_add {g : SmoothRiemannianMetric I M}
    (f h : SmoothScalar g) :
    (f + h).toContinuousMap = f.toContinuousMap + h.toContinuousMap := by
  ext x
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContinuousMap_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContinuousMap_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContinuousMap_add ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContinuousMap_add

omit [Module.Finite ℝ E] [I.Boundaryless] [T2Space M] [CompactSpace M] in
@[simp] lemma SmoothScalar.toContinuousMap_smul {g : SmoothRiemannianMetric I M}
    (c : ℝ) (f : SmoothScalar g) :
    (c • f).toContinuousMap = c • f.toContinuousMap := by
  ext x
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContinuousMap_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContinuousMap_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContinuousMap_smul ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContinuousMap_smul

def SmoothScalar.one (g : SmoothRiemannianMetric I M) : SmoothScalar g where
  toFun := fun _ => (1 : ℝ)
  smooth := contMDiff_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.one ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.one

omit [Module.Finite ℝ E] [I.Boundaryless] [T2Space M] [CompactSpace M] in
@[simp] lemma SmoothScalar.one_toFun (g : SmoothRiemannianMetric I M) :
    (SmoothScalar.one g).toFun = fun _ : M => (1 : ℝ) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.one_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.one_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.one_toFun ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.one_toFun

def SmoothScalar.mul {g : SmoothRiemannianMetric I M} (f h : SmoothScalar g) :
    SmoothScalar g where
  toFun := fun x => f.toFun x * h.toFun x
  smooth := f.smooth.mul h.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.mul ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.mul

omit [Module.Finite ℝ E] [I.Boundaryless] [T2Space M] [CompactSpace M] in
@[simp] lemma SmoothScalar.mul_toFun {g : SmoothRiemannianMetric I M}
    (f h : SmoothScalar g) :
    (SmoothScalar.mul f h).toFun = fun x => f.toFun x * h.toFun x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.mul_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.mul_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.mul_toFun ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.mul_toFun

def SmoothScalar.imageInContinuousMap (g : SmoothRiemannianMetric I M) :
    Set C(M, ℝ) :=
  { φ : C(M, ℝ) | ∃ f : SmoothScalar g, f.toContinuousMap = φ }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.imageInContinuousMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.imageInContinuousMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.imageInContinuousMap ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.imageInContinuousMap

def smoothScalarSubalgebra (g : SmoothRiemannianMetric I M) :
    Subalgebra ℝ C(M, ℝ) where
  carrier := SmoothScalar.imageInContinuousMap g
  mul_mem' := by
    rintro φ ψ ⟨f, hf⟩ ⟨h, hh⟩
    refine ⟨SmoothScalar.mul f h, ?_⟩
    ext x
    have h1 : φ x = f.toFun x := by rw [← hf]; rfl
    have h2 : ψ x = h.toFun x := by rw [← hh]; rfl
    change f.toFun x * h.toFun x = (φ * ψ) x
    rw [ContinuousMap.mul_apply, h1, h2]
  one_mem' := ⟨SmoothScalar.one g, by ext x; rfl⟩
  add_mem' := by
    rintro φ ψ ⟨f, hf⟩ ⟨h, hh⟩
    refine ⟨f + h, ?_⟩
    ext x
    have h1 : φ x = f.toFun x := by rw [← hf]; rfl
    have h2 : ψ x = h.toFun x := by rw [← hh]; rfl
    change f.toFun x + h.toFun x = (φ + ψ) x
    rw [ContinuousMap.add_apply, h1, h2]
  zero_mem' := ⟨(0 : SmoothScalar g), by ext x; rfl⟩
  algebraMap_mem' c := by
    refine ⟨c • SmoothScalar.one g, ?_⟩
    apply ContinuousMap.ext
    intro x
    change c * (1 : ℝ) = (_root_.Algebra.algebraMap ℝ C(M, ℝ) c) x
    rw [mul_one, Algebra.algebraMap_eq_smul_one]
    change c = (c • (1 : C(M, ℝ))) x
    rw [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothScalarSubalgebra then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothScalarSubalgebra"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothScalarSubalgebra ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothScalarSubalgebra

omit [Module.Finite ℝ E] [I.Boundaryless] [T2Space M] [CompactSpace M] in
@[simp] lemma mem_smoothScalarSubalgebra_iff {g : SmoothRiemannianMetric I M}
    {φ : C(M, ℝ)} :
    φ ∈ smoothScalarSubalgebra (I := I) (M := M) g ↔
      ∃ f : SmoothScalar g, f.toContinuousMap = φ := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.mem_smoothScalarSubalgebra_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.mem_smoothScalarSubalgebra_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.mem_smoothScalarSubalgebra_iff ``Submission.DifferentialGeometry.Analysis.Laplacian.mem_smoothScalarSubalgebra_iff

omit [I.Boundaryless] [CompactSpace M] in
private lemma exists_smooth_separating
    (x y : M) (hxy : x ≠ y) :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ f x = 1 ∧ f y = 0 := by
  classical
  have h_compl_open : IsOpen ({y}ᶜ : Set M) := isOpen_compl_singleton
  have h_x_in_compl : x ∈ ({y}ᶜ : Set M) := by
    intro hx
    rw [Set.mem_singleton_iff] at hx
    exact hxy hx
  have h_compl_mem : ({y}ᶜ : Set M) ∈ 𝓝 x :=
    h_compl_open.mem_nhds h_x_in_compl
  have hbasis := SmoothBumpFunction.nhds_basis_support (I := I) h_compl_mem
  obtain ⟨φ, hφ_tsupp⟩ := hbasis.ex_mem
  refine ⟨(φ : M → ℝ), φ.contMDiff, ?_, ?_⟩
  · exact φ.eq_one
  · by_contra hy
    have hy_support : y ∈ tsupport (φ : M → ℝ) := subset_tsupport _ hy
    have hy_in_compl : y ∈ ({y}ᶜ : Set M) := hφ_tsupp hy_support
    exact hy_in_compl rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.exists_smooth_separating
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.exists_smooth_separating target :: scope.openDecls } }

omit [I.Boundaryless] [CompactSpace M] in
theorem smoothScalarSubalgebra_separatesPoints (g : SmoothRiemannianMetric I M) :
    (smoothScalarSubalgebra (I := I) (M := M) g).SeparatesPoints := by
  intro x y hxy
  obtain ⟨f, hf, hfx, hfy⟩ := exists_smooth_separating (I := I) (M := M) x y hxy
  refine ⟨f, ?_, ?_⟩
  · refine ⟨(⟨f, hf⟩ : SmoothScalar g).toContinuousMap, ?_, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩
  · rw [hfx, hfy]
    exact one_ne_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothScalarSubalgebra_separatesPoints then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothScalarSubalgebra_separatesPoints"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothScalarSubalgebra_separatesPoints ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothScalarSubalgebra_separatesPoints

omit [I.Boundaryless] in
theorem exists_smoothScalar_sup_close (g : SmoothRiemannianMetric I M)
    (φ : C(M, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : SmoothScalar g, ‖f.toContinuousMap - φ‖ < ε := by
  obtain ⟨g', hg'_lt⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
      (smoothScalarSubalgebra (I := I) (M := M) g)
      (smoothScalarSubalgebra_separatesPoints (I := I) (M := M) g) φ ε hε
  obtain ⟨f, hf⟩ := g'.2
  refine ⟨f, ?_⟩
  rw [hf]
  exact hg'_lt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.exists_smoothScalar_sup_close then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.exists_smoothScalar_sup_close"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.exists_smoothScalar_sup_close ``Submission.DifferentialGeometry.Analysis.Laplacian.exists_smoothScalar_sup_close

omit [I.Boundaryless] [CompactSpace M] in
private lemma eLpNorm_two_le_of_norm_le [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (φ : M → ℝ) (_hφ : Continuous φ) (K : ℝ)
    (hK : ∀ x, ‖φ x‖ ≤ K) :
    eLpNorm φ 2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      (riemannianVolumeMeasure (I := I) (M := M) g
          (Set.univ : Set M)) ^ (2 : ℝ≥0∞).toReal⁻¹ *
        ENNReal.ofReal K := by
  have : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  exact MeasureTheory.eLpNorm_le_of_ae_bound (μ := riemannianVolumeMeasure (I := I) (M := M) g)
    (f := φ) (C := K) (Filter.Eventually.of_forall hK)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.eLpNorm_two_le_of_norm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.eLpNorm_two_le_of_norm_le target :: scope.openDecls } }

omit [I.Boundaryless] in
private lemma eLpNorm_smooth_sub_bc_le
    (g : SmoothRiemannianMetric I M)
    (f : SmoothScalar g) (ψ : M →ᵇ ℝ) (δ : ℝ)
    (h_pt : ∀ x : M, ‖f.toFun x - ψ x‖ ≤ δ) :
    _root_.MeasureTheory.eLpNorm (fun x : M => f.toFun x - ψ x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      (riemannianVolumeMeasure (I := I) (M := M) g) Set.univ ^
          ((2 : ℝ≥0∞).toReal⁻¹) * ENNReal.ofReal δ := by
  classical
  have : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have h_diff_cont : Continuous (fun x : M => f.toFun x - ψ x) :=
    f.smooth.continuous.sub ψ.continuous
  exact eLpNorm_two_le_of_norm_le (I := I) (M := M) g _ h_diff_cont δ h_pt

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.eLpNorm_smooth_sub_bc_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.eLpNorm_smooth_sub_bc_le target :: scope.openDecls } }

omit [T2Space M] [CompactSpace M] in
private lemma edist_toLp_eq_eLpNorm
    {μ : _root_.MeasureTheory.Measure M} (a b : M → ℝ) (ha : _root_.MeasureTheory.MemLp a 2 μ) (hb : _root_.MeasureTheory.MemLp b 2 μ) :
    edist (ha.toLp a) (hb.toLp b) = _root_.MeasureTheory.eLpNorm (fun x : M => a x - b x) 2 μ := by
  rw [Lp.edist_toLp_toLp]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.edist_toLp_eq_eLpNorm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.edist_toLp_eq_eLpNorm target :: scope.openDecls } }

omit [I.Boundaryless] in
private lemma exists_smoothToLp_close_to_memLp
    (g : SmoothRiemannianMetric I M)
    [hμ_fin : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g)]
    [hμ_wreg : (riemannianVolumeMeasure (I := I) (M := M) g).WeaklyRegular]
    (h : M → ℝ) (h_mem : _root_.MeasureTheory.MemLp h 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ f : SmoothScalar g,
      edist (f.memLp_two.toLp f.toFun) (h_mem.toLp h) ≤ ε := by
  classical
  set μvol := riemannianVolumeMeasure (I := I) (M := M) g with hμvol_def
  have h2 : (ε / 2 : ℝ≥0∞) ≠ 0 := by
    rw [Ne, ENNReal.div_eq_zero_iff, not_or]
    exact ⟨hε, ENNReal.ofNat_ne_top⟩
  obtain ⟨ψ_bc, hψ_eLpNorm_le, _hψ_mem⟩ :=
    h_mem.exists_boundedContinuous_eLpNorm_sub_le (E := ℝ) (μ := μvol) (p := 2)
      ENNReal.ofNat_ne_top h2
  have h_finite : μvol Set.univ < ⊤ := IsFiniteMeasure.measure_univ_lt_top
  set Cμ_enn : ℝ≥0∞ := μvol Set.univ ^ ((2 : ℝ≥0∞).toReal⁻¹) with hCμ_enn_def
  have hCμ_enn_ne_top : Cμ_enn ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ ((2 : ℝ≥0∞).toReal⁻¹))
      h_finite.ne
  obtain ⟨δ_real, hδ_pos, hδ_bound⟩ :
      ∃ δ_real : ℝ, 0 < δ_real ∧ Cμ_enn * ENNReal.ofReal δ_real ≤ ε / 2 := by
    by_cases h_top : ε / 2 = ⊤
    · refine ⟨1, by norm_num, ?_⟩
      rw [h_top]; exact le_top
    · set Cμ : ℝ := Cμ_enn.toReal with hCμ_def
      have hCμ_nn : 0 ≤ Cμ := ENNReal.toReal_nonneg
      set δ_real : ℝ := (ε / 2).toReal / (Cμ + 1) with hδ_def
      have hε2_pos : 0 < (ε / 2).toReal := by
        rw [ENNReal.toReal_pos_iff]
        exact ⟨pos_iff_ne_zero.mpr h2, lt_top_iff_ne_top.mpr h_top⟩
      have hCμ1_pos : 0 < Cμ + 1 := by linarith
      have hδ_pos : 0 < δ_real := by positivity
      refine ⟨δ_real, hδ_pos, ?_⟩
      have hCμ_enn_eq : Cμ_enn = ENNReal.ofReal Cμ := by
        rw [hCμ_def, ENNReal.ofReal_toReal hCμ_enn_ne_top]
      rw [hCμ_enn_eq, ← ENNReal.ofReal_mul hCμ_nn]
      have hreal_le : Cμ * δ_real ≤ (ε / 2).toReal := by
        rw [hδ_def]
        rw [mul_comm Cμ ((ε / 2).toReal / (Cμ + 1))]
        rw [div_mul_eq_mul_div]
        rw [div_le_iff₀ hCμ1_pos]
        nlinarith
      calc ENNReal.ofReal (Cμ * δ_real)
          ≤ ENNReal.ofReal (ε / 2).toReal := ENNReal.ofReal_le_ofReal hreal_le
        _ = ε / 2 := ENNReal.ofReal_toReal h_top
  set ψ_cont : C(M, ℝ) := ψ_bc.toContinuousMap with hψ_cont_def
  obtain ⟨f_smooth, hf_close⟩ := exists_smoothScalar_sup_close (I := I) (M := M) g ψ_cont hδ_pos
  have h_pointwise_bound : ∀ x : M, ‖f_smooth.toFun x - ψ_bc x‖ ≤ δ_real := by
    intro x
    have heq : f_smooth.toFun x - ψ_bc x =
        (f_smooth.toContinuousMap - ψ_cont) x := rfl
    rw [heq]
    exact (_root_.BoundedContinuousFunction.norm_coe_le_norm _ x).trans hf_close.le
  have h_eLpNorm_diff :
      _root_.MeasureTheory.eLpNorm (fun x : M => f_smooth.toFun x - ψ_bc x) 2 μvol ≤
        Cμ_enn * ENNReal.ofReal δ_real :=
    eLpNorm_smooth_sub_bc_le (I := I) (M := M) g f_smooth ψ_bc δ_real h_pointwise_bound
  refine ⟨f_smooth, ?_⟩
  have hψ_mem : _root_.MeasureTheory.MemLp (ψ_bc : M → ℝ) 2 μvol := _hψ_mem
  have h1 :
      _root_.EDist.edist (f_smooth.memLp_two.toLp f_smooth.toFun)
          (hψ_mem.toLp (ψ_bc : M → ℝ)) ≤ ε / 2 := by
    rw [edist_toLp_eq_eLpNorm]
    exact le_trans h_eLpNorm_diff hδ_bound
  have h2_bound :
      edist (hψ_mem.toLp (ψ_bc : M → ℝ)) (h_mem.toLp h) ≤ ε / 2 := by
    rw [edist_toLp_eq_eLpNorm]
    rw [show (fun x : M => (ψ_bc : M → ℝ) x - h x) = -(fun x : M => h x - ψ_bc x) from
        funext fun x => by rw [Pi.neg_apply]; ring]
    rw [_root_.MeasureTheory.eLpNorm_neg]
    exact hψ_eLpNorm_le
  calc _root_.EDist.edist (f_smooth.memLp_two.toLp f_smooth.toFun) (h_mem.toLp h)
      ≤ _root_.EDist.edist (f_smooth.memLp_two.toLp f_smooth.toFun)
            (hψ_mem.toLp (ψ_bc : M → ℝ)) +
          edist (hψ_mem.toLp (ψ_bc : M → ℝ)) (h_mem.toLp h) :=
        _root_.PseudoEMetricSpace.edist_triangle _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2_bound
    _ = ε := ENNReal.add_halves _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.exists_smoothToLp_close_to_memLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.exists_smoothToLp_close_to_memLp target :: scope.openDecls } }

theorem denseRange_smoothToLp (g : SmoothRiemannianMetric I M) :
    DenseRange (smoothToLp (I := I) (M := M) g) := by
  classical
  have : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have : (riemannianVolumeMeasure (I := I) (M := M) g).WeaklyRegular :=
    (riemannianVolumeMeasure_regular (I := I) (M := M) g).weaklyRegular
  intro v
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedEBall).2 fun ε hε ↦ ?_
  obtain ⟨f, hf⟩ := exists_smoothToLp_close_to_memLp (I := I) (M := M) g
    (v : M → ℝ) (Lp.memLp v) (ne_of_gt hε)
  refine ⟨smoothToLp (I := I) (M := M) g f, _root_.Set.mem_range_self _, ?_⟩
  rw [Metric.mem_closedEBall]
  have h_smooth_eq : (smoothToLp (I := I) (M := M) g f : _root_.MeasureTheory.Lp ℝ 2 _) =
      f.memLp_two.toLp f.toFun := rfl
  rw [h_smooth_eq]
  have h_v_eq : v = (Lp.memLp v).toLp (v : M → ℝ) := (Lp.toLp_coeFn v _).symm
  conv_lhs => rw [show v = (Lp.memLp v).toLp (v : M → ℝ) from h_v_eq]
  exact hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.denseRange_smoothToLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.denseRange_smoothToLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.denseRange_smoothToLp ``Submission.DifferentialGeometry.Analysis.Laplacian.denseRange_smoothToLp

theorem denseRange_H1ComplToLp (g : SmoothRiemannianMetric I M) :
    DenseRange (H1ComplToLp (I := I) (M := M) g) := by
  refine Dense.mono ?_ (denseRange_smoothToLp (I := I) (M := M) g)
  rintro y ⟨u, hu⟩
  refine ⟨smoothToH1Compl (I := I) (M := M) g u, ?_⟩
  rw [H1ComplToLp_smoothToH1Compl]
  exact hu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.denseRange_H1ComplToLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.denseRange_H1ComplToLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.denseRange_H1ComplToLp ``Submission.DifferentialGeometry.Analysis.Laplacian.denseRange_H1ComplToLp

end Laplacian
end Analysis
end DifferentialGeometry

end
