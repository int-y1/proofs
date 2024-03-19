import Mathlib.Computability.TuringMachine
import Init.Data.Nat.Basic

/-!
# Turing machines

Original source: https://github.com/meithecatte/busycoq/blob/master/verify/TM.v
-/

open Turing

/-- The direction a Turing machine can step in. -/
notation "L" => Dir.left
notation "R" => Dir.right

-- We parametrize over...
variable {Q : Type u}     -- The type of states
variable {Sym : Type v}   -- The type of tape symbols
--variable {q₀ : Q}
--variable {s₀ : Sym}
--instance : Inhabited Sym := ⟨s₀⟩
variable [Inhabited Q]    -- The fact that `Q` is nonempty. Use `default` to get the inhabitant.
                          -- By convention, the starting state is used as the inhabitant.
variable [Inhabited Sym]  -- The fact that `Sym` is nonempty. Use `default` to get the inhabitant.
                          -- By convention, the blank symbol is used as the inhabitant.

def TM := Q × Sym → Option (Sym × Dir × Q)

variable (tm : @TM Q Sym)
variable (c c₁ c₂ c₃ : Q × Tape Sym)

/-- We define a notation for tapes, evocative of a Turing machine's head hovering over a particular
symbol. -/
local notation l " {{" s "}} " r => ⟨s, l, r⟩ -- Tape Sym

--infixl:67 " << " => fun s a ↦ ListBlank.cons a s
notation:67 s:67 " << " a:68 => ListBlank.cons a s -- ListBlank Sym
infixr:67 " >> " => ListBlank.cons -- ListBlank Sym

example (a b c d e : Sym) : Tape Sym :=
  (ListBlank.mk [] << a << b) {{c}} (d >> e >> ListBlank.mk [])

-- For the directed head formulation, we use the following:
set_option quotPrecheck false in
local notation l " <{{" q "}} " r => (q, (ListBlank.tail l) {{ListBlank.head l}} r) -- Q × Tape Sym
set_option quotPrecheck false in
local notation l " {{" q "}}> " r => (q, l {{ListBlank.head r}} (ListBlank.tail r)) -- Q × Tape Sym

/-- The small-step semantics of Turing machines. -/
def step : (Q × Tape Sym) → Option (Q × Tape Sym) :=
  fun ⟨q, ⟨s, l, r⟩⟩ ↦ match tm ⟨q, s⟩ with
    | none => none
    | some ⟨s', d, q'⟩ => some ⟨q', Tape.move d (l {{s'}} r)⟩

/-- `step`. The small-step semantics of Turing machines. -/
notation c " [" tm "]⊢ " c' => step tm c = some c'

/-- Executes `n` steps. -/
def stepNat : (n : ℕ) → (Q × Tape Sym) → Option (Q × Tape Sym) :=
  fun n c ↦ n.repeat (fun oc ↦ oc.bind (step tm)) (some c)

/-- `stepNat` executes `n` steps.

Unfortunately, the parser needs a character between `n` and `c'`. I picked `}`. -/
notation c " [" tm "]⊢^{" n "} " c' => stepNat tm n c = some c'

/-- `stepStar` executes an unspecified number of steps (the "eventually reaches" relation). -/
notation c " [" tm "]⊢* " c' => ∃ n, c [tm]⊢^{n} c'

/-- `stepPlus` executes an unspecified, but non-zero number of steps. -/
notation c " [" tm "]⊢⁺ " c' => ∃ n > 0, c [tm]⊢^{n} c'

/-- The Turing machine has halted if `step tm c` returns `none`. -/
def halted : Prop := step tm c = none

/-- The initial configuration of the machine. -/
def c₀ : Q × Tape Sym := ⟨default, (ListBlank.mk []) {{default}} (ListBlank.mk [])⟩

/-- A Turing machine halts if it eventually reaches a halting configuration. -/
def haltsIn (n : ℕ) := ∃ c', (c [tm]⊢^{n} c') ∧ halted tm c'

def halts := ∃ n, haltsIn tm c n


/-!
## Not sure where these lemmas should go
-/

/-- todo: why can't i find this in mathlib4? -/
lemma Nat.repeat_add (f : α → α) (n m : ℕ) (a : α) :
    Nat.repeat f (n+m) a = Nat.repeat f n (Nat.repeat f m a) := by
  match n with
  | 0 => rw [zero_add]; rfl
  | n+1 => rw [Nat.add_right_comm, Nat.repeat, Nat.repeat_add]; rfl

/- todo: why can't i find this in mathlib4?
lemma Nat.repeat_succ_eq_right (f : α → α) (n : ℕ) (a : α) :
    Nat.repeat f (n+1) a = Nat.repeat f n (f a) := by
  rw [Nat.repeat_add]; rfl
-/


/-!
## 1 hypothesis and 1 goal
-/

lemma step_stepNat (h : c₁ [tm]⊢ c₂) : c₁ [tm]⊢^{1} c₂ := h

lemma step_stepStar (h : c₁ [tm]⊢ c₂) : c₁ [tm]⊢* c₂ := by exists 1

lemma step_stepPlus (h : c₁ [tm]⊢ c₂) : c₁ [tm]⊢⁺ c₂ := by exists 1

lemma stepNat_step (h : c₁ [tm]⊢^{1} c₂) : c₁ [tm]⊢ c₂ := h

-- `stepNat_stepStar` is redundant by definition

-- The hypothesis that `c₁ ≠ c₂` doesn't really count.
lemma stepStar_stepPlus (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₁ ≠ c₂) : c₁ [tm]⊢⁺ c₂ := by
  obtain ⟨n, h₁⟩ := h₁
  refine' ⟨n, Nat.zero_lt_of_ne_zero _, h₁⟩
  rintro rfl
  rw [stepNat, Nat.repeat, Option.some.injEq] at h₁
  contradiction

lemma stepPlus_stepStar (h : c₁ [tm]⊢⁺ c₂) : c₁ [tm]⊢* c₂ := by
  obtain ⟨n, _, h⟩ := h; exists n

lemma halted_not_step (h : halted tm c₁) : ¬ c₁ [tm]⊢ c₂ := by
  rw [h]; simp

lemma not_halted_step (h : ¬ halted tm c₁) : ∃ c₂, c₁ [tm]⊢ c₂ := by
  match h' : step tm c₁ with
  | none => rw [halted] at h; contradiction
  | some c₂' => exists c₂'

lemma halted_halts (h : halted tm c) : halts tm c := by exists 0, c


/-!
## Lemmas to handle `stepNat`
-/

lemma stepNat_trans (n m : ℕ) (h₁ : c₁ [tm]⊢^{n} c₂) (h₂ : c₂ [tm]⊢^{m} c₃) :
    c₁ [tm]⊢^{n+m} c₃ := by
  rwa [Nat.add_comm, stepNat, Nat.repeat_add, ← stepNat, h₁, ← stepNat]

/-- todo: golf this proof -/
lemma stepNat_succ_stepNat_step (n : ℕ) (h : c₁ [tm]⊢^{n+1} c₃) :
    ∃ c₂, (c₁ [tm]⊢^{n} c₂) ∧ (c₂ [tm]⊢ c₃) := by
  match n with
  | 0 => exists c₁
  | n+1 =>
    rw [Nat.add_comm, stepNat, Nat.repeat_add, ← stepNat, Nat.repeat, Nat.repeat] at h
    match h₂ : stepNat tm (n + 1) c₁ with
    | none => rw [h₂, Option.none_bind] at h; contradiction
    | some c₂' => rw [h₂, Option.some_bind] at h; exists c₂'

/-- todo: golf this proof, it's pretty ugly -/
lemma stepNat_add (c₁ c₃ : Q × Tape Sym) (n m : ℕ) (h : c₁ [tm]⊢^{n+m} c₃) :
    ∃ c₂, (c₁ [tm]⊢^{n} c₂) ∧ (c₂ [tm]⊢^{m} c₃) := by
  match m with
  | 0 => exists c₃
  | m+1 =>
    rw [← Nat.add_assoc] at h
    have ⟨c₄, h₄₁, h₄₃⟩ := stepNat_succ_stepNat_step tm c₁ c₃ (n+m) h
    have ⟨c₂', h₄₁, h₄₂⟩ := stepNat_add c₁ c₄ n m h₄₁
    refine' ⟨c₂', h₄₁, _⟩
    rwa [Nat.add_comm, stepNat, Nat.repeat_add, ← stepNat, h₄₂, Nat.repeat, Nat.repeat,
      Option.some_bind]

lemma stepNat_succ_step_stepNat (n : ℕ) (h : c₁ [tm]⊢^{n+1} c₃) :
    ∃ c₂, (c₁ [tm]⊢ c₂) ∧ (c₂ [tm]⊢^{n} c₃) :=
  stepNat_add tm c₁ c₃ 1 n (add_comm 1 n ▸ h)

/-- When using `stepNat_add`, it is often more convenient to have the arithmetic show up as a
separate goal, to be easily discharged. -/
lemma stepNat_add₂ (c₁ c₃ : Q × Tape Sym) (n k₁ k₂ : ℕ) (h₁ : c₁ [tm]⊢^{n} c₃) (h₂ : n = k₁ + k₂) :
    ∃ c₂, (c₁ [tm]⊢^{k₁} c₂) ∧ (c₂ [tm]⊢^{k₂} c₃) :=
  stepNat_add tm c₁ c₃ k₁ k₂ (h₂ ▸ h₁)


/-!
## 2 similar hypotheses and 1 goal, or 1 hypothesis and 2 similar goals
-/

lemma step_deterministic (h₁ : c [tm]⊢ c₁) (h₂ : c [tm]⊢ c₂) : c₁ = c₂ := by
  rwa [h₁, Option.some.injEq] at h₂

lemma stepNat_deterministic (n : ℕ) (h₁ : c [tm]⊢^{n} c₁) (h₂ : c [tm]⊢^{n} c₂) : c₁ = c₂ := by
  rwa [h₁, Option.some.injEq] at h₂

lemma stepStar_trans (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢* c₃ := by
  obtain ⟨n, h₁⟩ := h₁
  obtain ⟨m, h₂⟩ := h₂
  exact ⟨n+m, stepNat_trans _ _ _ _ _ _ h₁ h₂⟩

lemma stepPlus_trans (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, h₁⟩ := h₁
  obtain ⟨m, h₂⟩ := h₂
  exact ⟨n+m, by simp [h₁], stepNat_trans _ _ _ _ _ _ h₁.2 h₂.2⟩


/-!
## 2 different hypotheses and 1 goal
-/

lemma step_haltsIn_succ (n : ℕ) (h₁ : c₁ [tm]⊢ c₂) (h₂ : haltsIn tm c₂ n) :
    haltsIn tm c₁ (n+1) := by
  obtain ⟨c₃, h₂₁, h₂₂⟩ := h₂
  refine' ⟨c₃, _, h₂₂⟩
  rw [Nat.add_comm]
  exact stepNat_trans _ _ _ _ _ _ h₁ h₂₁

lemma stepNat_haltsIn_add (n m : ℕ) (h₁ : c₁ [tm]⊢^{m} c₂) (h₂ : haltsIn tm c₂ n) :
    haltsIn tm c₁ (n+m) := by
  obtain ⟨c₃, h₂₁, h₂₂⟩ := h₂
  refine' ⟨c₃, _, h₂₂⟩
  rw [Nat.add_comm]
  exact stepNat_trans _ _ _ _ _ _ h₁ h₂₁

lemma step_halts (h₁ : c₁ [tm]⊢ c₂) (h₂ : halts tm c₂) : halts tm c₁ := by
  obtain ⟨n, h₂⟩ := h₂
  exact ⟨n+1, step_haltsIn_succ _ _ _ _ h₁ h₂⟩

lemma stepNat_halts (n : ℕ) (h₁ : c₁ [tm]⊢^{n} c₂) (h₂ : halts tm c₂) : halts tm c₁ := by
  obtain ⟨m, h₂⟩ := h₂
  exact ⟨m+n, stepNat_haltsIn_add _ _ _ _ _ h₁ h₂⟩

lemma stepStar_halts (h₁ : c₁ [tm]⊢* c₂) (h₂ : halts tm c₂) : halts tm c₁ := by
  obtain ⟨n, h₂⟩ := h₂
  obtain ⟨m, h₁⟩ := h₁
  exact ⟨n+m, stepNat_haltsIn_add _ _ _ _ _ h₁ h₂⟩

lemma stepPlus_halts (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : halts tm c₂) : halts tm c₁ :=
  stepStar_halts _ _ _ (stepPlus_stepStar _ _ _ h₁) h₂

lemma stepStar_stepPlus_stepPlus (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, h₁⟩ := h₁
  obtain ⟨m, h₂₁, h₂₂⟩ := h₂
  exact ⟨n+m, by simp [h₂₁], stepNat_trans _ _ _ _ _ _ h₁ h₂₂⟩

lemma step_stepPlus_stepPlus (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepStar_stepPlus_stepPlus _ _ _ _ (step_stepStar _ _ _ h₁) h₂

lemma stepStar_step_stepPlus (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢ c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepStar_stepPlus_stepPlus _ _ _ _ h₁ (step_stepPlus _ _ _ h₂)

lemma stepPlus_stepStar_stepPlus (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, h₁₁, h₁₂⟩ := h₁
  obtain ⟨m, h₂⟩ := h₂
  exact ⟨n+m, by simp [h₁₁], stepNat_trans _ _ _ _ _ _ h₁₂ h₂⟩

lemma step_stepStar_stepPlus (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus _ _ _ _ (step_stepPlus _ _ _ h₁) h₂

lemma stepPlus_step_stepPlus (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢ c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus _ _ _ _ h₁ (step_stepStar _ _ _ h₂)
