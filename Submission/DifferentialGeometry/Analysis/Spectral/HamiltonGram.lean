import Mathlib.Analysis.InnerProductSpace.Positive

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.Spectral

open scoped _root_.BigOperators _root_.RealInnerProductSpace

private theorem move_outer4 {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [AddCommMonoid R] (f : κ → ι → ι → ι → ι → R) :
    (∑ r, ∑ a, ∑ b, ∑ c, ∑ d, f r a b c d) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ r, f r a b c d := by
  calc
    _ = ∑ a, ∑ r, ∑ b, ∑ c, ∑ d, f r a b c d :=
      Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ r, ∑ c, ∑ d, f r a b c d := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, ∑ r, ∑ d, f r a b c d := by
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ r, f r a b c d := by
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Finset.sum_congr rfl fun c _ => Finset.sum_comm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.move_outer4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.move_outer4 target :: scope.openDecls } }

private theorem move_outer3 {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [AddCommMonoid R] (f : κ → ι → ι → ι → R) :
    (∑ r, ∑ a, ∑ b, ∑ c, f r a b c) =
      ∑ a, ∑ b, ∑ c, ∑ r, f r a b c := by
  calc
    _ = ∑ a, ∑ r, ∑ b, ∑ c, f r a b c := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ r, ∑ c, f r a b c := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, ∑ r, f r a b c := by
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => Finset.sum_comm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.move_outer3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.move_outer3 target :: scope.openDecls } }

private theorem move_outer2 {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [AddCommMonoid R] (f : κ → ι → ι → R) :
    (∑ r, ∑ a, ∑ b, f r a b) = ∑ a, ∑ b, ∑ r, f r a b := by
  calc
    _ = ∑ a, ∑ r, ∑ b, f r a b := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ r, f r a b := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_comm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.move_outer2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.move_outer2 target :: scope.openDecls } }

theorem exists_finite_gram_factorization
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    [FiniteDimensional Real V] (T : V →L[Real] V)
    (hT : T.IsPositive) :
    ∃ (m : Nat) (v : Fin m → V),
      T = ∑ i, InnerProductSpace.rankOne Real (v i) (v i) := by
  exact (ContinuousLinearMap.isPositive_iff_eq_sum_rankOne).mp hT

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.exists_finite_gram_factorization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.exists_finite_gram_factorization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.exists_finite_gram_factorization ``Submission.DifferentialGeometry.Analysis.Spectral.exists_finite_gram_factorization

theorem finite_gram_factorization_quadratic
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    [FiniteDimensional Real V] (T : V →L[Real] V)
    (hT : T.IsPositive) :
    ∃ (m : Nat) (v : Fin m → V), ∀ z : V,
      inner Real (T z) z = ∑ i, (_root_.Inner.inner Real (v i) z) ^ 2 := by
  obtain ⟨m, v, hv⟩ := exists_finite_gram_factorization T hT
  refine ⟨m, v, ?_⟩
  intro z
  rw [hv]
  simp only [sum_apply, InnerProductSpace.rankOne_apply, sum_inner]
  simp_rw [real_inner_smul_left]
  ring_nf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.finite_gram_factorization_quadratic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.finite_gram_factorization_quadratic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.finite_gram_factorization_quadratic ``Submission.DifferentialGeometry.Analysis.Spectral.finite_gram_factorization_quadratic

def hamiltonGramK {ι κ : Type*} [Fintype κ]
    (Y : κ → ι → ι → Real) (a b c d : ι) : Real :=
  ∑ r, Y r a b * Y r c d

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamiltonGramK then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamiltonGramK"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamiltonGramK ``Submission.DifferentialGeometry.Analysis.Spectral.hamiltonGramK

def hamiltonGramP {ι κ : Type*} [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real) (a b c : ι) : Real :=
  ∑ r, Y r a b * X r c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamiltonGramP then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamiltonGramP"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamiltonGramP ``Submission.DifferentialGeometry.Analysis.Spectral.hamiltonGramP

def hamiltonGramM {ι κ : Type*} [Fintype κ]
    (X : κ → ι → Real) (a b : ι) : Real :=
  ∑ r, X r a * X r b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamiltonGramM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamiltonGramM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamiltonGramM ``Submission.DifferentialGeometry.Analysis.Spectral.hamiltonGramM

def hamiltonGramLinearTerm {ι κ : Type*} [Fintype ι]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real) (r : κ) : Real :=
  (∑ a, ∑ b, Y r a b * U a b) + ∑ c, X r c * W c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamiltonGramLinearTerm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamiltonGramLinearTerm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamiltonGramLinearTerm ``Submission.DifferentialGeometry.Analysis.Spectral.hamiltonGramLinearTerm

def hamiltonGramQuadratic {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real) : Real :=
  ∑ r, (hamiltonGramLinearTerm Y X U W r) ^ 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamiltonGramQuadratic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamiltonGramQuadratic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamiltonGramQuadratic ``Submission.DifferentialGeometry.Analysis.Spectral.hamiltonGramQuadratic

def hamiltonGramReaction {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real) : Real :=
  ∑ r, ∑ s,
    ((∑ a, ∑ c, Y r a c * X s c * W a) -
      (∑ a, ∑ c, Y s a c * X r c * W a) -
      2 * (∑ a, ∑ b, ∑ c, Y r a c * Y s b c * U a b)) ^ 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamiltonGramReaction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamiltonGramReaction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamiltonGramReaction ``Submission.DifferentialGeometry.Analysis.Spectral.hamiltonGramReaction

def hamiltonGramSigma {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real) (a b : ι) : Real :=
  ∑ r, Y r a b * hamiltonGramLinearTerm Y X U W r

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamiltonGramSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamiltonGramSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamiltonGramSigma ``Submission.DifferentialGeometry.Analysis.Spectral.hamiltonGramSigma

def hamiltonQuadraticForm {ι : Type*} [Fintype ι]
    (K : ι → ι → ι → ι → Real) (P : ι → ι → ι → Real)
    (M : ι → ι → Real) (U : ι → ι → Real) (W : ι → Real) : Real :=
  (∑ a, ∑ b, ∑ c, ∑ d, K a b c d * U a b * U c d) +
    2 * (∑ a, ∑ b, ∑ c, P a b c * U a b * W c) +
    ∑ a, ∑ b, M a b * W a * W b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamiltonQuadraticForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamiltonQuadraticForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamiltonQuadraticForm ``Submission.DifferentialGeometry.Analysis.Spectral.hamiltonQuadraticForm

theorem exists_hamiltonGram_factorization
    {ι : Type*} [Fintype ι]
    (K : ι → ι → ι → ι → Real)
    (P : ι → ι → ι → Real)
    (M : ι → ι → Real)
    (hKPair : ∀ a b c d, K a b c d = K c d a b)
    (hKSkew : ∀ a b c d, K a b c d = -K b a c d)
    (hPSkew : ∀ a b c, P a b c = -P b a c)
    (hMSymm : ∀ a b, M a b = M b a)
    (hQ : ∀ (U : ι → ι → Real) (W : ι → Real),
      0 ≤ hamiltonQuadraticForm K P M U W) :
    ∃ (m : Nat) (Y : Fin m → ι → ι → Real) (X : Fin m → ι → Real),
      (∀ r a b, Y r a b = -Y r b a) ∧
      K = hamiltonGramK Y ∧
      P = hamiltonGramP Y X ∧
      M = hamiltonGramM X := by
  classical
  let B : Matrix ((ι × ι) ⊕ ι) ((ι × ι) ⊕ ι) Real := fun i j =>
    match i, j with
    | Sum.inl (a, b), Sum.inl (c, d) => K a b c d
    | Sum.inl (a, b), Sum.inr c => P a b c
    | Sum.inr c, Sum.inl (a, b) => P a b c
    | Sum.inr a, Sum.inr b => M a b
  have hB : B.PosSemidef := Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (by
      unfold Matrix.IsHermitian
      ext i j
      rcases i with i | i
      · rcases i with ⟨a, b⟩
        rcases j with j | j
        · rcases j with ⟨c, d⟩
          change K c d a b = K a b c d
          exact hKPair c d a b
        · change P a b j = P a b j
          rfl
      · rcases j with j | j
        · rcases j with ⟨c, d⟩
          change P c d i = P c d i
          rfl
        · change M j i = M i j
          exact hMSymm j i)
    (by
      intro z
      have hz := hQ (fun a b => z (Sum.inl (a, b))) (fun a => z (Sum.inr a))
      simp only [dotProduct, Matrix.mulVec, B, Fintype.sum_sum_type, _root_.TrivialStar.star_trivial]
      simp_rw [Fintype.sum_prod_type]
      simp_rw [mul_add]
      simp only [Finset.sum_add_distrib]
      simp_rw [Finset.mul_sum]
      unfold hamiltonQuadraticForm at hz
      rw [show (∑ x, ∑ a, ∑ b,
          z (Sum.inr x) * (P a b x * z (Sum.inl (a, b)))) =
          ∑ a, ∑ b, ∑ x,
            z (Sum.inr x) * (P a b x * z (Sum.inl (a, b))) by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]]
      have hKTerm (a b c d : ι) :
          z (Sum.inl (a, b)) * (K a b c d * z (Sum.inl (c, d))) =
            K a b c d * z (Sum.inl (a, b)) * z (Sum.inl (c, d)) := by
        ring
      have hPFirst (a b c : ι) :
          z (Sum.inl (a, b)) * (P a b c * z (Sum.inr c)) =
            P a b c * z (Sum.inl (a, b)) * z (Sum.inr c) := by
        ring
      have hPSecond (a b c : ι) :
          z (Sum.inr c) * (P a b c * z (Sum.inl (a, b))) =
            P a b c * z (Sum.inl (a, b)) * z (Sum.inr c) := by
        ring
      have hMTerm (a b : ι) :
          z (Sum.inr a) * (M a b * z (Sum.inr b)) =
            M a b * z (Sum.inr a) * z (Sum.inr b) := by
        ring
      simp_rw [hKTerm]
      simp_rw [hPFirst]
      simp_rw [hPSecond]
      simp_rw [hMTerm]
      simpa only [two_mul, add_assoc] using hz)
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hB
  let Y₀ : Fin m → ι → ι → Real := fun r a b => v r (Sum.inl (a, b))
  let X : Fin m → ι → Real := fun r a => v r (Sum.inr a)
  let Y : Fin m → ι → ι → Real := fun r a b =>
    (Y₀ r a b - Y₀ r b a) / 2
  refine ⟨m, Y, X, ?_, ?_, ?_, ?_⟩
  · intro r a b
    simp only [Y]
    ring
  · funext a b c d
    have habcd := congrFun (congrFun hv (Sum.inl (a, b))) (Sum.inl (c, d))
    have habdc := congrFun (congrFun hv (Sum.inl (a, b))) (Sum.inl (d, c))
    have hbacd := congrFun (congrFun hv (Sum.inl (b, a))) (Sum.inl (c, d))
    have hbadc := congrFun (congrFun hv (Sum.inl (b, a))) (Sum.inl (d, c))
    simp only [B, Matrix.sum_apply, Matrix.vecMulVec_apply, _root_.TrivialStar.star_trivial] at habcd
    simp only [B, Matrix.sum_apply, Matrix.vecMulVec_apply, _root_.TrivialStar.star_trivial] at habdc
    simp only [B, Matrix.sum_apply, Matrix.vecMulVec_apply, _root_.TrivialStar.star_trivial] at hbacd
    simp only [B, Matrix.sum_apply, Matrix.vecMulVec_apply, _root_.TrivialStar.star_trivial] at hbadc
    unfold hamiltonGramK
    simp only [Y]
    change K a b c d = ∑ x,
      ((v x (Sum.inl (a, b)) - v x (Sum.inl (b, a))) / 2) *
      ((v x (Sum.inl (c, d)) - v x (Sum.inl (d, c))) / 2)
    have hexpand (x : Fin m) :
        ((v x (Sum.inl (a, b)) - v x (Sum.inl (b, a))) / 2) *
            ((v x (Sum.inl (c, d)) - v x (Sum.inl (d, c))) / 2) =
          (v x (Sum.inl (a, b)) * v x (Sum.inl (c, d)) -
            v x (Sum.inl (a, b)) * v x (Sum.inl (d, c)) -
            v x (Sum.inl (b, a)) * v x (Sum.inl (c, d)) +
            v x (Sum.inl (b, a)) * v x (Sum.inl (d, c))) / 4 := by
      ring
    simp_rw [hexpand]
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib]
    rw [← habcd, ← habdc, ← hbacd, ← hbadc]
    have hKLast (i j k l : ι) : K i j k l = -K i j l k := by
      rw [hKPair, hKSkew, hKPair]
    linarith [hKLast a b c d, hKSkew a b c d,
      hKLast b a c d, hKSkew a b d c]
  · funext a b c
    have habc := congrFun (congrFun hv (Sum.inl (a, b))) (Sum.inr c)
    have hbac := congrFun (congrFun hv (Sum.inl (b, a))) (Sum.inr c)
    simp only [B, Matrix.sum_apply, Matrix.vecMulVec_apply, _root_.TrivialStar.star_trivial] at habc hbac
    unfold hamiltonGramP
    change P a b c = ∑ x,
      ((v x (Sum.inl (a, b)) - v x (Sum.inl (b, a))) / 2) * v x (Sum.inr c)
    have hexpand (x : Fin m) :
        ((v x (Sum.inl (a, b)) - v x (Sum.inl (b, a))) / 2) *
            v x (Sum.inr c) =
          (v x (Sum.inl (a, b)) * v x (Sum.inr c) -
            v x (Sum.inl (b, a)) * v x (Sum.inr c)) / 2 := by
      ring
    simp_rw [hexpand]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    rw [← habc, ← hbac]
    linarith [hPSkew a b c]
  · funext a b
    have hab := congrFun (congrFun hv (Sum.inr a)) (Sum.inr b)
    simpa only [B, Matrix.sum_apply, Matrix.vecMulVec_apply, _root_.TrivialStar.star_trivial,
      hamiltonGramM, X] using hab

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.exists_hamiltonGram_factorization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.exists_hamiltonGram_factorization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.exists_hamiltonGram_factorization ``Submission.DifferentialGeometry.Analysis.Spectral.exists_hamiltonGram_factorization

def hamiltonReactionPolynomial {ι : Type*} [Fintype ι]
    (K : ι → ι → ι → ι → Real) (P : ι → ι → ι → Real)
    (M : ι → ι → Real) (U : ι → ι → Real) (W : ι → Real) : Real :=
  2 * ∑ a, ∑ b, ∑ c, ∑ d, K a c b d * M c d * W a * W b -
    2 * ∑ a, ∑ b, ∑ c, ∑ d, P a c d * P b d c * W a * W b +
    8 * ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
      K a d c e * P d b e * U a b * W c +
    4 * ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f,
      K a e c f * K b e d f * U a b * U c d

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamiltonReactionPolynomial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamiltonReactionPolynomial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamiltonReactionPolynomial ``Submission.DifferentialGeometry.Analysis.Spectral.hamiltonReactionPolynomial

theorem hamiltonGram_quadratic_eq_hamiltonQuadraticForm
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real) :
    hamiltonGramQuadratic Y X U W =
      hamiltonQuadraticForm (hamiltonGramK Y) (hamiltonGramP Y X)
        (hamiltonGramM X) U W := by
  unfold hamiltonGramQuadratic hamiltonGramLinearTerm hamiltonQuadraticForm
    hamiltonGramK hamiltonGramP hamiltonGramM
  have hYY (r : κ) :
      (∑ a, ∑ b, Y r a b * U a b) ^ 2 =
        ∑ a, ∑ b, ∑ c, ∑ d,
          (Y r a b * Y r c d) * U a b * U c d := by
    rw [pow_two, Fintype.sum_mul_sum]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  have hYX (r : κ) :
      (∑ a, ∑ b, Y r a b * U a b) * (∑ c, X r c * W c) =
        ∑ a, ∑ b, ∑ c,
          (Y r a b * X r c) * U a b * W c := by
    rw [Fintype.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hXX (r : κ) :
      (∑ c, X r c * W c) ^ 2 =
        ∑ c, ∑ d, (X r c * X r d) * W c * W d := by
    rw [pow_two, Fintype.sum_mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  have hsq (r : κ) :
      ((∑ a, ∑ b, Y r a b * U a b) + (∑ c, X r c * W c)) ^ 2 =
        (∑ a, ∑ b, Y r a b * U a b) ^ 2 +
          2 * ((∑ a, ∑ b, Y r a b * U a b) * (∑ c, X r c * W c)) +
          (∑ c, X r c * W c) ^ 2 := by
    ring
  simp_rw [hsq]
  simp_rw [hYY]
  simp_rw [hYX]
  simp_rw [hXX]
  have hYYsum :
      (∑ x, ∑ a, ∑ b, ∑ c, ∑ d,
        Y x a b * Y x c d * U a b * U c d) =
        ∑ a, ∑ b, ∑ c, ∑ d,
          (∑ r, Y r a b * Y r c d) * U a b * U c d := by
    calc
      _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ x,
          Y x a b * Y x c d * U a b * U c d := move_outer4 _
      _ = _ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun c _ => ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        calc
          _ = ∑ x, (Y x a b * Y x c d) * (U a b * U c d) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            ring
          _ = (∑ x, Y x a b * Y x c d) * (U a b * U c d) := by
            rw [Finset.sum_mul]
          _ = _ := by ring
  have hYXsum :
      (∑ x, 2 * ∑ a, ∑ b, ∑ c,
        Y x a b * X x c * U a b * W c) =
        2 * ∑ a, ∑ b, ∑ c,
          (∑ r, Y r a b * X r c) * U a b * W c := by
    calc
      _ = 2 * (∑ x, ∑ a, ∑ b, ∑ c,
          Y x a b * X x c * U a b * W c) := by
        rw [Finset.mul_sum]
      _ = 2 * (∑ a, ∑ b, ∑ c, ∑ x,
          Y x a b * X x c * U a b * W c) := by
        rw [move_outer3]
      _ = _ := by
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun b _ => ?_
        refine Finset.sum_congr rfl fun c _ => ?_
        calc
          _ = ∑ x, (Y x a b * X x c) * (U a b * W c) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            ring
          _ = (∑ x, Y x a b * X x c) * (U a b * W c) := by
            rw [Finset.sum_mul]
          _ = _ := by ring
  have hXXsum :
      (∑ x, ∑ c, ∑ d,
        X x c * X x d * W c * W d) =
        ∑ c, ∑ d, (∑ r, X r c * X r d) * W c * W d := by
    calc
      _ = ∑ c, ∑ d, ∑ x,
          X x c * X x d * W c * W d := move_outer2 _
      _ = _ := by
        refine Finset.sum_congr rfl fun c _ => ?_
        refine Finset.sum_congr rfl fun d _ => ?_
        calc
          _ = ∑ x, (X x c * X x d) * (W c * W d) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            ring
          _ = (∑ x, X x c * X x d) * (W c * W d) := by
            rw [Finset.sum_mul]
          _ = _ := by ring
  simp only [Finset.sum_add_distrib]
  rw [hYYsum, hYXsum, hXXsum]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamiltonGram_quadratic_eq_hamiltonQuadraticForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamiltonGram_quadratic_eq_hamiltonQuadraticForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamiltonGram_quadratic_eq_hamiltonQuadraticForm ``Submission.DifferentialGeometry.Analysis.Spectral.hamiltonGram_quadratic_eq_hamiltonQuadraticForm

theorem hamiltonGramSigma_eq_block
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real) (a b : ι) :
    hamiltonGramSigma Y X U W a b =
      (∑ c, hamiltonGramP Y X a b c * W c) +
        ∑ c, ∑ d, hamiltonGramK Y a b c d * U c d := by
  unfold hamiltonGramSigma hamiltonGramLinearTerm hamiltonGramP hamiltonGramK
  simp_rw [Finset.sum_mul]
  simp_rw [mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib]
  have hX :
      (∑ x, ∑ i, Y x a b * (X x i * W i)) =
        ∑ x, ∑ i, Y i a b * X i x * W x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hU :
      (∑ x, ∑ x_1, ∑ i, Y x a b * (Y x x_1 i * U x_1 i)) =
        ∑ x, ∑ x_1, ∑ i, Y i a b * Y i x x_1 * U x x_1 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x_1 _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hX, hU]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamiltonGramSigma_eq_block then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamiltonGramSigma_eq_block"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamiltonGramSigma_eq_block ``Submission.DifferentialGeometry.Analysis.Spectral.hamiltonGramSigma_eq_block

theorem hamiltonGram_quadratic_nonneg
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real) :
    0 ≤ hamiltonGramQuadratic Y X U W := by
  unfold hamiltonGramQuadratic
  exact Finset.sum_nonneg fun r _ => sq_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamiltonGram_quadratic_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamiltonGram_quadratic_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamiltonGram_quadratic_nonneg ``Submission.DifferentialGeometry.Analysis.Spectral.hamiltonGram_quadratic_nonneg

theorem hamiltonGram_linearTerm_eq_zero_of_quadratic_eq_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real)
    (hzero : hamiltonGramQuadratic Y X U W = 0) :
    ∀ r, hamiltonGramLinearTerm Y X U W r = 0 := by
  intro r
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg
    (fun s _ => sq_nonneg (hamiltonGramLinearTerm Y X U W s))).mp hzero
  exact sq_eq_zero_iff.mp (hterms r (Finset.mem_univ r))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamiltonGram_linearTerm_eq_zero_of_quadratic_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamiltonGram_linearTerm_eq_zero_of_quadratic_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamiltonGram_linearTerm_eq_zero_of_quadratic_eq_zero ``Submission.DifferentialGeometry.Analysis.Spectral.hamiltonGram_linearTerm_eq_zero_of_quadratic_eq_zero

theorem hamiltonGram_quadratic_eq_zero_iff_linearTerms_eq_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real) :
    hamiltonGramQuadratic Y X U W = 0 ↔
      ∀ r, hamiltonGramLinearTerm Y X U W r = 0 := by
  constructor
  · exact hamiltonGram_linearTerm_eq_zero_of_quadratic_eq_zero Y X U W
  · intro hterm
    unfold hamiltonGramQuadratic
    apply Finset.sum_eq_zero
    intro r hr
    rw [hterm r]
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamiltonGram_quadratic_eq_zero_iff_linearTerms_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamiltonGram_quadratic_eq_zero_iff_linearTerms_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamiltonGram_quadratic_eq_zero_iff_linearTerms_eq_zero ``Submission.DifferentialGeometry.Analysis.Spectral.hamiltonGram_quadratic_eq_zero_iff_linearTerms_eq_zero

theorem hamiltonGram_reaction_nonneg
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real) :
    0 ≤ hamiltonGramReaction Y X U W := by
  unfold hamiltonGramReaction
  exact Finset.sum_nonneg fun r _ =>
      Finset.sum_nonneg fun s _ => sq_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamiltonGram_reaction_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamiltonGram_reaction_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamiltonGram_reaction_nonneg ``Submission.DifferentialGeometry.Analysis.Spectral.hamiltonGram_reaction_nonneg

theorem hamiltonGram_reaction_tangent_nonneg
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real) :
    0 ≤ hamiltonGramQuadratic Y X U W + hamiltonGramReaction Y X U W := by
  exact add_nonneg (hamiltonGram_quadratic_nonneg Y X U W)
    (hamiltonGram_reaction_nonneg Y X U W)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamiltonGram_reaction_tangent_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamiltonGram_reaction_tangent_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamiltonGram_reaction_tangent_nonneg ``Submission.DifferentialGeometry.Analysis.Spectral.hamiltonGram_reaction_tangent_nonneg

theorem hamiltonGram_reaction_tangent_nonneg_of_quadratic_eq_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real)
    (hzero : hamiltonGramQuadratic Y X U W = 0) :
    0 ≤ hamiltonGramReaction Y X U W := by
  have h := hamiltonGram_reaction_tangent_nonneg Y X U W
  rw [hzero, zero_add] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamiltonGram_reaction_tangent_nonneg_of_quadratic_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamiltonGram_reaction_tangent_nonneg_of_quadratic_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamiltonGram_reaction_tangent_nonneg_of_quadratic_eq_zero ``Submission.DifferentialGeometry.Analysis.Spectral.hamiltonGram_reaction_tangent_nonneg_of_quadratic_eq_zero

theorem hamiltonGram_sigma_eq_zero_of_quadratic_eq_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : κ → ι → ι → Real) (X : κ → ι → Real)
    (U : ι → ι → Real) (W : ι → Real)
    (hzero : hamiltonGramQuadratic Y X U W = 0) (a b : ι) :
    hamiltonGramSigma Y X U W a b = 0 := by
  have hterm := hamiltonGram_linearTerm_eq_zero_of_quadratic_eq_zero Y X U W hzero
  unfold hamiltonGramSigma
  simp [hterm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hamiltonGram_sigma_eq_zero_of_quadratic_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hamiltonGram_sigma_eq_zero_of_quadratic_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hamiltonGram_sigma_eq_zero_of_quadratic_eq_zero ``Submission.DifferentialGeometry.Analysis.Spectral.hamiltonGram_sigma_eq_zero_of_quadratic_eq_zero

end DifferentialGeometry.Analysis.Spectral
