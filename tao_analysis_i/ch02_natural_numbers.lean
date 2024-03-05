import Mathlib.Init.Logic
import Mathlib.Tactic.Cases

inductive XNat where
  -- Axiom 2.1
  | zero : XNat
  -- Axiom 2.2
  | succ : XNat → XNat

namespace XNat

postfix:max "++" => succ

variable (n m a b c : XNat)

/-- Axiom 2.3. Lean's inductive types already assume this. -/
theorem succ_ne_zero : n++ ≠ zero := by
  exact XNat.noConfusion

/-- Proposition 2.1.6 -/
theorem four_ne_zero : zero++++++++ ≠ zero :=
  succ_ne_zero _

/-- Axiom 2.4. Lean's inductive types already assume this. -/
theorem succ_inj : n++ = m++ → n = m := by
  intro h
  rw [succ.injEq] at h
  exact h

/-- Proposition 2.1.8 -/
theorem six_ne_two : zero++++++++++++ ≠ zero++++ := by
  intro h
  have := succ_inj _ _ (succ_inj _ _ h)
  exact four_ne_zero this

/-- Axiom 2.5. Lean's inductive types already assume this. -/
theorem succ_ind (P : XNat → Prop) (P_zero : P zero) (P_succ : ∀ n, P n → P n++) : ∀ n, P n
  | zero => P_zero
  | m++ => by
    apply P_succ
    -- We're allowed to recursively call `succ_ind`, because `m` is smaller than `succ m`.
    exact succ_ind P P_zero P_succ m

/-- Definition 2.2.1. Addition of natural numbers. -/
def add : XNat → XNat → XNat
  | zero, m => m
  | n++, m => (add n m)++

infixl:65 " + " => add

/-- Lemma 2.2.2 -/
theorem add_zero : n + zero = n := by
  induction n
  case zero => rfl
  case succ n h => rw [add, h]

/-- Lemma 2.2.3 -/
theorem add_succ : n + m++ = (n + m)++ := by
  induction n
  case zero => rfl
  case succ n h => rw [add, h, add]

/-- Proposition 2.2.4 -/
theorem add_comm : n + m = m + n := by
  induction n
  case zero => rw [add_zero, add]
  case succ n h => rw [add, h, add_succ]

/-- Proposition 2.2.5 -/
theorem add_assoc : (a + b) + c = a + (b + c) := by
  induction a
  case zero => rfl
  case succ n h => rw [add, add, h, add]

/-- Proposition 2.2.6 -/
theorem add_left_cancel : a + b = a + c → b = c := by
  induction a
  case zero => exact id
  case succ a h =>
    intro h₂
    apply h
    exact succ_inj _ _ h₂

/-- Definition 2.2.7 -/
def Positive : Prop := n ≠ zero

/-- Proposition 2.2.8 -/
theorem pos_add_eq_pos (ha : Positive a) : Positive (a + b) := by
  cases b
  case zero =>
    rw [add_zero]
    exact ha
  case succ b => -- don't need the induction hypothesis
    rw [add_succ]
    apply succ_ne_zero

/-- Corollary 2.2.9 -/
theorem eq_zero_of_add_eq_zero (h : a + b = zero) : a = zero ∧ b = zero := by
  cases a
  case succ a => exact (succ_ne_zero _ h).elim
  cases b
  case succ b => exact (succ_ne_zero _ h).elim
  exact ⟨rfl, rfl⟩

/-- Lemma 2.2.10 -/
theorem exists_unique_pred (ha : Positive a) : ∃! b : XNat, b++ = a := by
  cases a
  case zero => exact (ha rfl).elim
  case succ a => exact ⟨a, rfl, fun a' h ↦ succ_inj a' a h⟩

/-- Definition 2.2.11, part 1 -/
def LE (m n : XNat) : Prop :=
  ∃ a : XNat, n = m + a

infix:50 " ≤ " => LE
notation:50 lhs:50 " ≥ " rhs:50 => (LE rhs lhs)

/-- Definition 2.2.11, part 2 -/
def LT (m n : XNat) : Prop :=
  n ≥ m ∧ n ≠ m

infix:50 " < " => LT
notation:50 lhs:50 " > " rhs:50 => rhs < lhs

/-- Proposition 2.2.12a -/
theorem ge_rfl : a ≥ a := by
  exists zero
  rw [add_zero]

/-- Proposition 2.2.12b -/
theorem ge_trans (hab : a ≥ b) (hbc : b ≥ c) : a ≥ c := by
  have ⟨d₁, h₁⟩ := hab
  have ⟨d₂, h₂⟩ := hbc
  exists d₁ + d₂
  rw [h₁, h₂, add_assoc, add_comm d₂ d₁]

/-- Proposition 2.2.12c -/
theorem ge_antisymm (hab : a ≥ b) (hba : b ≥ a) : a = b := by
  have ⟨d₁, h₁⟩ := hab
  have ⟨d₂, h₂⟩ := hba
  rw [← add_zero b, h₁, add_assoc] at h₂
  have : zero = d₁ + d₂ := add_left_cancel _ _ _ h₂
  have ⟨d₁_zero, _⟩ := eq_zero_of_add_eq_zero _ _ this.symm
  rw [d₁_zero, add_zero] at h₁
  exact h₁

/-- Proposition 2.2.12d -/
theorem ge_iff_add_right_ge : a ≥ b ↔ a + c ≥ b + c := by
  constructor
  · intro ⟨d, h⟩
    exists d
    rw [h, add_assoc, add_assoc, add_comm d c]
  · intro ⟨d, h⟩
    exists d
    apply add_left_cancel c _ _
    rw [add_comm, h, add_comm b c, add_assoc]

/-- Proposition 2.2.12e -/
theorem lt_iff_succ_le : a < b ↔ a++ ≤ b := by
  constructor
  · intro ⟨⟨d, h₁⟩, h₂⟩
    cases d
    case zero =>
      rw [add_zero] at h₁
      exact (h₂ h₁).elim
    case succ d =>
      exists d
      rw [add_succ] at h₁
      exact h₁
  · intro ⟨d, h⟩
    constructor
    · exists (d++) -- TODO: brackets required here. Problem with precedence?
      rw [add_succ]
      exact h
    · intro heq
      rw [← add_zero b, heq, add, ← add_succ] at h
      have : zero = d++ := add_left_cancel _ _ _ h
      exact succ_ne_zero _ this.symm

/-- Proposition 2.2.12f -/
theorem le_iff_eq_add_pos : a < b ↔ (∃ d, Positive d ∧ b = a + d) := by
  constructor
  · intro ⟨⟨d, h₁⟩, h₂⟩
    refine ⟨d, fun h ↦ ?_, h₁⟩
    rw [h, add_zero] at h₁
    exact h₂ h₁
  · intro ⟨d, h₁, h₂⟩
    refine ⟨⟨d, h₂⟩, fun h ↦ ?_⟩
    rw [← add_zero b, h] at h₂
    have : zero = d := add_left_cancel _ _ _ h₂
    exact h₁ this.symm

-- TODO: this is a long way to express that exactly 1 statement is true. shorten it.
/-- Proposition 2.2.13, 1 excludes 2 -/
theorem trichotomy_1n2 : a < b → ¬(a = b) :=
  fun h ↦ h.2.symm

/-- Proposition 2.2.13, 3 excludes 2 -/
theorem trichotomy_3n2 : a > b → ¬(a = b) :=
  fun h₁ h₂ ↦ trichotomy_1n2 b a h₁ h₂.symm

/-- Proposition 2.2.13, 2 excludes 1 -/
theorem trichotomy_2n1 : a = b → ¬(a < b) :=
  fun h₁ h₂ ↦ trichotomy_1n2 a b h₂ h₁

/-- Proposition 2.2.13, 2 excludes 3 -/
theorem trichotomy_2n3 : a = b → ¬(a > b) :=
  fun h₁ h₂ ↦ trichotomy_1n2 b a h₂ h₁.symm

/-- Proposition 2.2.13, 1 excludes 3 -/
theorem trichotomy_1n3 : a < b → ¬(a > b) := by
  intro h₁ h₂
  have : a = b := ge_antisymm a b h₂.1 h₁.1
  exact trichotomy_1n2 a b h₁ this

/-- Proposition 2.2.13, 3 excludes 1 -/
theorem trichotomy_3n1 : a > b → ¬(a < b) :=
  fun h₁ h₂ ↦ trichotomy_1n3 a b h₂ h₁

/-- Proposition 2.2.13, 1 or 2 or 3 -/
theorem trichotomy_123 : a < b ∨ a = b ∨ a > b := by
  induction a
  case zero =>
    cases b
    case zero => exact Or.inr (Or.inl rfl)
    case succ b => exact Or.inl ⟨⟨b++, rfl⟩, succ_ne_zero b⟩
  case succ a ih =>
    cases' ih with h h23
    · have ⟨⟨d, h₁⟩, h₂⟩ := h
      match d with
      | zero => exact (h₂ (add_zero a ▸ h₁)).elim
      | succ zero =>
        rw [add_succ, add_zero] at h₁
        exact Or.inr (Or.inl h₁.symm)
      | succ (succ d) =>
        refine' Or.inl ⟨⟨d++, _⟩, _⟩
        · rw [add_succ] at h₁
          exact h₁
        · rw [← add_zero a++, h₁, add_succ, add]
          intro h₃
          have h₃ := succ_inj _ _ h₃
          have h₃ := add_left_cancel _ _ _ h₃
          exact succ_ne_zero _ h₃
    cases' h23 with h h
    · apply Or.inr (Or.inr _)
      rw [h]
      refine' ⟨⟨zero++, _⟩, _⟩
      · rw [add_succ, add_zero]
      · rw [← add_zero b, ← add_succ]
        intro h₂
        exact succ_ne_zero zero (add_left_cancel _ _ _ h₂)
    · apply Or.inr (Or.inr _)
      have ⟨⟨d, h₁⟩, _⟩ := h
      refine' ⟨⟨d++, _⟩, _⟩
      · rw [h₁, add_succ]
      · rw [← add_zero b, h₁, ← add_succ]
        intro h₃
        exact succ_ne_zero d (add_left_cancel _ _ _ h₃)

/-- Proposition 2.2.14 -/
theorem strong_ind (m₀ : XNat) (P : XNat → Prop)
    (P_succ : ∀ m, m ≥ m₀ → (∀ m', m₀ ≤ m' ∧ m' < m → P m') → P m) :
    ∀ m, m ≥ m₀ → P m := by
  let Q (n : XNat) : Prop := ∀ m, m₀ ≤ m ∧ m < n → P m
  suffices ∀ n, Q n by
    intro m h
    refine' this m++ m ⟨h, _⟩
    refine' ⟨⟨zero++, _⟩, _⟩
    · rw [add_succ, add_zero]
    · rw [← add_zero m, ← add_succ]
      intro h
      exact succ_ne_zero _ (add_left_cancel _ _ _ h)
  intro n
  induction n
  case zero =>
    intro m ⟨_, ⟨⟨d, h₁⟩, h₂⟩⟩
    have : zero = m := (eq_zero_of_add_eq_zero _ _ h₁.symm).1.symm
    refine' (h₂ this).elim
  case succ n ih =>
    intro m h
    cases' trichotomy_123 m n with h₁ h₂₃
    · exact ih m ⟨h.1, h₁⟩
    cases' h₂₃ with h₂ h₃
    · refine' P_succ m h.1 (fun m' ↦ _)
      rw [h₂]
      exact ih m'
    · have h₁ := (lt_iff_succ_le _ _).1 h.2
      have h₂ := (lt_iff_succ_le _ _).1 h₃
      have h := (lt_iff_succ_le _ _).2 (ge_trans _ _ _ h₂ h₁)
      exact (trichotomy_1n2 _ _ h rfl).elim

/-- Exercise 2.2.6 -/
theorem backward_ind (n : XNat) (P : XNat → Prop) (h₁ : ∀ m, P m++ → P m) (h₂ : P n) :
    ∀ m, m ≤ n → P m := by
  induction n
  case zero =>
    intro m ⟨d, h⟩
    rw [(eq_zero_of_add_eq_zero _ _ h.symm).1]
    exact h₂
  case succ n ih =>
    intro m ⟨d, h⟩
    cases d
    case zero =>
      rw [h, add_zero] at h₂
      exact h₂
    case succ d =>
      rw [add_succ] at h
      exact ih (h₁ _ h₂) m ⟨d, succ_inj _ _ h⟩

/-- Exercise 2.2.7 -/
theorem ind_start_n (n : XNat) (P : XNat → Prop) (h₁ : ∀ m, P m → P m++) (h₂ : P n) :
    ∀ m, m ≥ n → P m := by
  suffices ∀ d : XNat, P (n + d) by
    intro m ⟨d, h⟩
    rw [h]
    exact this d
  intro d
  induction d
  case zero => rw [add_zero]; exact h₂
  case succ d ih => rw [add_succ]; exact h₁ _ ih

/-- Definition 2.3.1. Multiplication of natural numbers. -/
def mul : XNat → XNat → XNat
  | zero, _ => zero
  | n++, m => (mul n m) + m

infixl:70 " * " => mul

theorem mul_zero : n * zero = zero := by
  induction n
  case zero => rfl
  case succ n h => rw [mul, h]; rfl

theorem mul_succ : n * m++ = n * m + n := by
  induction n
  case zero => rfl
  case succ n h => rw [mul, h, mul, add_assoc, add_assoc, add_succ n m, add_succ m n, add_comm n m]

/-- Lemma 2.3.2 -/
theorem mul_comm : n * m = m * n := by
  induction n
  case zero => rw [mul_zero]; rfl
  case succ n h => rw [mul, h, mul_succ]

/-- Lemma 2.3.3 -/
theorem mul_eq_zero_iff_eq_zero : n * m = zero ↔ n = zero ∨ m = zero := by
  constructor
  · intro h
    match n, m with
    | zero, _ => exact Or.inl rfl
    | _, zero => exact Or.inr rfl
    | succ n, succ m =>
      rw [mul, add_succ] at h
      exact (succ_ne_zero _ h).elim
  · intro
    | Or.inl h => rw [h]; rfl
    | Or.inr h => rw [h, mul_zero]

/-- Proposition 2.3.4, left distributive law -/
theorem left_distrib : a * (b + c) = a * b + a * c := by
  induction c
  case zero => rw [mul_zero, add_zero, add_zero]
  case succ c ih => rw [add_succ, mul_succ, ih, mul_succ, add_assoc]

/-- Proposition 2.3.4, right distributive law -/
theorem right_distrib : (b + c) * a = b * a + c * a := by
  rw [mul_comm, left_distrib, mul_comm, mul_comm a c]

/-- Proposition 2.3.5 -/
theorem mul_assoc : (a * b) * c = a * (b * c) := by
  induction a
  case zero => rfl
  case succ a ih => rw [mul, right_distrib, mul, ih]

/-- Proposition 2.3.6 -/
theorem le_imp_mul_pos_le (h₁ : a < b) (hc : Positive c) : a * c < b * c := by
  have ⟨d, hd, h⟩ := (le_iff_eq_add_pos _ _).1 h₁
  rw [h, right_distrib]
  refine' (le_iff_eq_add_pos _ _).2 ⟨d * c, fun h ↦ _, rfl⟩
  match (mul_eq_zero_iff_eq_zero _ _).1 h with
  | Or.inl h => exact hd h
  | Or.inr h => exact hc h

/-- Corollary 2.3.7 -/
theorem mul_right_cancel (h : a * c = b * c) (hc : c ≠ zero) : a = b := by
  match trichotomy_123 a b with
  | Or.inl h' =>
    have := le_imp_mul_pos_le _ _ _ h' hc
    exact (trichotomy_1n2 _ _ this h).elim
  | Or.inr (Or.inl h') => exact h'
  | Or.inr (Or.inr h') =>
    have := le_imp_mul_pos_le _ _ _ h' hc
    exact (trichotomy_3n2 _ _ this h).elim

/-- Proposition 2.3.9 -/
theorem euclid_div (n q : XNat) (hq : Positive q) :
    ∃ m r : XNat, zero ≤ r ∧ r < q ∧ n = m * q + r := by
  refine' strong_ind zero (P := fun n ↦ ∃ m r : XNat, zero ≤ r ∧ r < q ∧ n = m * q + r) _ n ⟨n, rfl⟩
  intro m _ ih
  match trichotomy_123 m q with
  | Or.inl h => exact ⟨zero, m, ⟨m, rfl⟩, h, rfl⟩
  | Or.inr h =>
    have ⟨d, h⟩ : q ≤ m := by
      cases' h with h h
      · rw [h]; exact ge_rfl _
      · exact h.1
    have ⟨dm, dr, hd₁, hd₂, hd₃⟩ : ∃ m r : XNat, zero ≤ r ∧ r < q ∧ d = m * q + r := by
      refine' ih d ⟨⟨d, rfl⟩, _⟩
      exact (le_iff_eq_add_pos _ _).2 ⟨q, hq, add_comm _ _ ▸ h⟩
    refine' ⟨dm++, dr, hd₁, hd₂, _⟩
    rw [h, hd₃, mul, add_comm, add_assoc, add_comm dr, ← add_assoc]

/-- Definition 2.3.11 -/
def pow : XNat → XNat → XNat
  | _, zero => zero++
  | m, n++ => (pow m n) * m

infixr:80 " ^ " => pow

/-- Exercise 2.3.4 -/
theorem binom_pow_two : (a + b) ^ zero++++ = a ^ zero++++ + zero++++ * a * b + b ^ zero++++ := by
  dsimp only [pow, mul, add]
  rw [left_distrib, right_distrib, right_distrib, right_distrib, mul_comm b a]
  rw [add_assoc, add_assoc, add_assoc]
