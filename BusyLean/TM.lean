import Mathlib.Computability.TuringMachine

/-!
# Turing machines

Original source: https://github.com/meithecatte/busycoq/blob/master/verify/TM.v

Notation precedences:
* 65: Left tape (`Turing.ListBlank Sym`). Right tape (`Turing.ListBlank Sym`).
      This is the same precedence as `++` from `Init.Notation`.
* 60: Configuration (`Turing.Tape Sym`).
* 50: `step*` notations, such as `* [tm]⊢ *`.
      This is the same precedence as `=` from `Init.Notation`.
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
--variable [Inhabited Q]    -- The fact that `Q` is nonempty. Use `default` to get the inhabitant.
--                          -- By convention, the starting state is used as the inhabitant.
--                          -- Most lemmas in this file didn't use `[Inhabited Q]`. Omit it.
variable [Inhabited Sym]  -- The fact that `Sym` is nonempty. Use `default` to get the inhabitant.
                          -- By convention, the blank symbol is used as the inhabitant.

def TM := Q × Sym → Option (Sym × Dir × Q)

variable (tm : @TM Q Sym)
variable (c c₁ c₂ c₃ : Q × Tape Sym)

/-- We define a notation for tapes, evocative of a Turing machine's head hovering over a particular
symbol. -/
notation3:60 l:65 " {{" s "}} " r:65 => Tape.mk s l r

-- Use precedence 65. This is the same precedence as `++` from `Init.Notation`.
notation3:65 s:65 " << " a:66 => ListBlank.cons a s -- No conflict.
notation3:65 a:66 " >> " s:65 => ListBlank.cons a s -- Conflicts with HAndThen.
notation3:65 s:65 " <+ " l:66 => ListBlank.append l s -- No conflict. WARNING: `l` is reversed.
notation3:65 l:66 " +> " s:65 => ListBlank.append l s -- No conflict.

/-- `0^∞ b a c {d} e f g 0^∞`. WARNING: `<+ l` appends the reverse of `l`. -/
example (a b c d e f g : Sym) : Tape Sym := default <+ [a, b] << c {{d}} [e, f] +> g >> default

-- For the directed head formulation, we use the following:
notation3:60 l:65 " <{{" q "}} " r:65 => (q, ListBlank.tail l {{ListBlank.head l}} r)
notation3:60 l:65 " {{" q "}}> " r:65 => (q, l {{ListBlank.head r}} ListBlank.tail r)

/-- The small-step semantics of Turing machines. -/
def step : (Q × Tape Sym) → Option (Q × Tape Sym) :=
  fun ⟨q, ⟨s, l, r⟩⟩ ↦ match tm ⟨q, s⟩ with
    | none => none
    | some ⟨s', d, q'⟩ => some ⟨q', Tape.move d (l {{s'}} r)⟩

/-- `step`. The small-step semantics of Turing machines. -/
notation3:50 c:60 " [" tm "]⊢ " c':60 => step tm c = some c'

/-- Executes `n` steps. -/
def stepNat : (n : ℕ) → (Q × Tape Sym) → Option (Q × Tape Sym) :=
  fun n c ↦ n.repeat (fun oc ↦ oc.bind (step tm)) (some c)

/-- `stepNat` executes `n` steps.

Unfortunately, the parser needs a character between `n` and `c'`. I picked `}`. -/
notation3:50 c:60 " [" tm "]⊢^{" n:65 "} " c':60 => stepNat tm n c = some c'

/-- `stepStar` executes an unspecified number of steps (the "eventually reaches" relation). -/
notation3:50 c:60 " [" tm "]⊢* " c':60 => ∃ n, c [tm]⊢^{n} c'

/-- `stepPlus` executes an unspecified, but non-zero number of steps. -/
notation3:50 c:60 " [" tm "]⊢⁺ " c':60 => ∃ n > 0, c [tm]⊢^{n} c'

/-- The Turing machine has halted if `step tm c` returns `none`. -/
def halted : Prop := step tm c = none

/-- The initial configuration of the machine. -/
def c₀ [Inhabited Q] : Q × Tape Sym := default

/-- A Turing machine halts if it eventually reaches a halting configuration. -/
def haltsIn (n : ℕ) := ∃ c', (c [tm]⊢^{n} c') ∧ halted tm c'

def halts := ∃ n, haltsIn tm c n


/-!
## Not sure where these lemmas should go
-/

/-- todo: why can't i find this in mathlib4? -/
lemma Nat.repeat_add (f : α → α) (n m : ℕ) (a : α) :
    (n+m).repeat f a = n.repeat f (m.repeat f a) := by
  match n with
  | 0 => rw [zero_add]; rfl
  | n+1 => rw [Nat.add_right_comm, Nat.repeat, Nat.repeat_add]; rfl


/-!
## 1 hypothesis and 1 goal
-/
variable {tm} {c c₁ c₂ c₃}

lemma step_stepNat (h : c₁ [tm]⊢ c₂) : c₁ [tm]⊢^{1} c₂ := h

lemma step_stepStar (h : c₁ [tm]⊢ c₂) : c₁ [tm]⊢* c₂ := by exists 1

lemma step_stepPlus (h : c₁ [tm]⊢ c₂) : c₁ [tm]⊢⁺ c₂ := by exists 1

lemma stepNat_step (h : c₁ [tm]⊢^{1} c₂) : c₁ [tm]⊢ c₂ := h

-- `stepNat_stepStar` is redundant by definition

-- The hypothesis that `c₁ ≠ c₂` doesn't really count.
lemma stepStar_stepPlus (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₁ ≠ c₂) : c₁ [tm]⊢⁺ c₂ := by
  obtain ⟨n, h₁⟩ := h₁
  refine ⟨n, Nat.zero_lt_of_ne_zero ?_, h₁⟩
  rintro rfl
  rw [stepNat, Nat.repeat, Option.some.injEq] at h₁
  contradiction

lemma stepPlus_stepStar (h : c₁ [tm]⊢⁺ c₂) : c₁ [tm]⊢* c₂ := by
  obtain ⟨n, -, h⟩ := h; exists n

lemma halted_not_step (h : halted tm c₁) : ¬c₁ [tm]⊢ c₂ := by
  rw [h]; simp

lemma not_halted_step (h : ¬halted tm c₁) : ∃ c₂, c₁ [tm]⊢ c₂ := by
  match h' : step tm c₁ with
  | none => rw [halted] at h; contradiction
  | some c₂' => exists c₂'

lemma halted_halts (h : halted tm c) : halts tm c := by exists 0, c

lemma haltsIn_stepNat (n : ℕ) (h₁ : haltsIn tm c₁ n) : ∃ c, c₁ [tm]⊢^{n} c := by
  obtain ⟨c₂, h₂, -⟩ := h₁; exact ⟨c₂, h₂⟩


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
    | none => rw [h₂, Option.bind_none] at h; contradiction
    | some c₂' => rw [h₂, Option.bind_some] at h; exists c₂'

/-- todo: golf this proof, it's pretty ugly -/
lemma stepNat_add {c₁ c₃ : Q × Tape Sym} (n m : ℕ) (h : c₁ [tm]⊢^{n+m} c₃) :
    ∃ c₂, (c₁ [tm]⊢^{n} c₂) ∧ (c₂ [tm]⊢^{m} c₃) := by
  match m with
  | 0 => exists c₃
  | m+1 =>
    rw [← Nat.add_assoc] at h
    have ⟨c₄, h₄₁, h₄₃⟩ := stepNat_succ_stepNat_step (n+m) h
    have ⟨c₂', h₄₁, h₄₂⟩ := stepNat_add _ _ h₄₁
    refine ⟨c₂', h₄₁, ?_⟩
    rwa [Nat.add_comm, stepNat, Nat.repeat_add, ← stepNat, h₄₂, Nat.repeat, Nat.repeat,
      Option.bind_some]

lemma stepNat_succ_step_stepNat (n : ℕ) (h : c₁ [tm]⊢^{n+1} c₃) :
    ∃ c₂, (c₁ [tm]⊢ c₂) ∧ (c₂ [tm]⊢^{n} c₃) :=
  stepNat_add 1 n (add_comm 1 n ▸ h)

/-- When using `stepNat_add`, it is often more convenient to have the arithmetic show up as a
separate goal, to be easily discharged. -/
lemma stepNat_add₂ {c₁ c₃ : Q × Tape Sym} (n k₁ k₂ : ℕ) (h₁ : c₁ [tm]⊢^{n} c₃) (h₂ : n = k₁ + k₂) :
    ∃ c₂, (c₁ [tm]⊢^{k₁} c₂) ∧ (c₂ [tm]⊢^{k₂} c₃) :=
  stepNat_add k₁ k₂ (h₂ ▸ h₁)

lemma stepNat_le_stepNat (n k : ℕ) (h₁ : c₁ [tm]⊢^{n} c₂) (h₂ : k ≤ n) : ∃ c, c₁ [tm]⊢^{k} c := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le h₂
  have ⟨c₂, hc₂, _⟩ := stepNat_add _ _ h₁
  exact ⟨c₂, hc₂⟩


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
  exact ⟨n+m, stepNat_trans _ _ h₁ h₂⟩

lemma stepPlus_trans (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, h₁⟩ := h₁
  obtain ⟨m, h₂⟩ := h₂
  exact ⟨n+m, Nat.add_pos_left h₁.1 _, stepNat_trans _ _ h₁.2 h₂.2⟩


/-!
## 2 different hypotheses and 1 goal
-/

lemma step_haltsIn_succ (n : ℕ) (h₁ : c₁ [tm]⊢ c₂) (h₂ : haltsIn tm c₂ n) :
    haltsIn tm c₁ (n+1) := by
  obtain ⟨c₃, h₂₁, h₂₂⟩ := h₂
  refine ⟨c₃, ?_, h₂₂⟩
  rw [Nat.add_comm]
  exact stepNat_trans _ _ h₁ h₂₁

lemma stepNat_haltsIn_add (n m : ℕ) (h₁ : c₁ [tm]⊢^{m} c₂) (h₂ : haltsIn tm c₂ n) :
    haltsIn tm c₁ (n+m) := by
  obtain ⟨c₃, h₂₁, h₂₂⟩ := h₂
  refine ⟨c₃, ?_, h₂₂⟩
  rw [Nat.add_comm]
  exact stepNat_trans _ _ h₁ h₂₁

lemma step_halts (h₁ : c₁ [tm]⊢ c₂) (h₂ : halts tm c₂) : halts tm c₁ := by
  obtain ⟨n, h₂⟩ := h₂
  exact ⟨n+1, step_haltsIn_succ _ h₁ h₂⟩

lemma stepNat_halts (n : ℕ) (h₁ : c₁ [tm]⊢^{n} c₂) (h₂ : halts tm c₂) : halts tm c₁ := by
  obtain ⟨m, h₂⟩ := h₂
  exact ⟨m+n, stepNat_haltsIn_add _ _ h₁ h₂⟩

lemma stepStar_halts (h₁ : c₁ [tm]⊢* c₂) (h₂ : halts tm c₂) : halts tm c₁ := by
  obtain ⟨n, h₂⟩ := h₂
  obtain ⟨m, h₁⟩ := h₁
  exact ⟨n+m, stepNat_haltsIn_add _ _ h₁ h₂⟩

lemma stepPlus_halts (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : halts tm c₂) : halts tm c₁ :=
  stepStar_halts (stepPlus_stepStar h₁) h₂

lemma stepStar_stepPlus_stepPlus (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, h₁⟩ := h₁
  obtain ⟨m, h₂₁, h₂₂⟩ := h₂
  exact ⟨n+m, Nat.add_pos_right _ h₂₁, stepNat_trans _ _ h₁ h₂₂⟩

lemma step_stepPlus_stepPlus (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepStar_stepPlus_stepPlus (step_stepStar h₁) h₂

lemma stepStar_step_stepPlus (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢ c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepStar_stepPlus_stepPlus h₁ (step_stepPlus h₂)

lemma stepPlus_stepStar_stepPlus (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, h₁₁, h₁₂⟩ := h₁
  obtain ⟨m, h₂⟩ := h₂
  exact ⟨n+m, Nat.add_pos_left h₁₁ _, stepNat_trans _ _ h₁₂ h₂⟩

lemma step_stepStar_stepPlus (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus (step_stepPlus h₁) h₂

lemma stepPlus_step_stepPlus (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢ c₃) : c₁ [tm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus h₁ (step_stepStar h₂)

-- todo: find a nicer proof
lemma stepPlus_split_step_stepStar (h : c₁ [tm]⊢⁺ c₃) : ∃ c₂, (c₁ [tm]⊢ c₂) ∧ (c₂ [tm]⊢* c₃) := by
  obtain ⟨n, h₁, h₂⟩ := h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt h₁
  rw [zero_add, add_comm] at h₂
  have ⟨c₂', h₃, h₄⟩ := stepNat_add _ _ h₂
  exact ⟨c₂', h₃, n, h₄⟩

-- todo: find a nicer proof
lemma stepPlus_split_stepStar_step (h : c₁ [tm]⊢⁺ c₃) : ∃ c₂, (c₁ [tm]⊢* c₂) ∧ (c₂ [tm]⊢ c₃) := by
  obtain ⟨n, h₁, h₂⟩ := h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt h₁
  rw [zero_add] at h₂
  have ⟨c₂', h₃, h₄⟩ := stepNat_add _ _ h₂
  exact ⟨c₂', ⟨n, h₃⟩, h₄⟩


/-!
## Misc
-/

lemma stepPlus_step (h : c₁ [tm]⊢⁺ c₂) : ∃ c, c₁ [tm]⊢ c := by
  have ⟨c', hc', _⟩ := stepPlus_split_step_stepStar h
  exact ⟨c', hc'⟩

lemma halted_not_stepPlus (h : halted tm c₁) : ¬c₁ [tm]⊢⁺ c₂ := by
  intro h'
  have ⟨c', h'⟩ := stepPlus_step h'
  rw [h] at h'
  contradiction

lemma haltsIn_gt_not_stepNat (n k : ℕ) (h₁ : haltsIn tm c₁ n) (h₂ : k > n) : ¬c₁ [tm]⊢^{k} c₂ := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h₂.le
  intro h₃
  have ⟨c', h₄, h₅⟩ := stepNat_add₂ _ _ _ h₃ hm
  obtain ⟨c'', h₄', h₅'⟩ := h₁
  rcases h₄' ▸ h₄
  exact halted_not_stepPlus h₅' ⟨m, Nat.pos_of_lt_add_right (hm ▸ h₂), h₅⟩

lemma haltsIn_stepNat_le (n k : ℕ) (h₁ : haltsIn tm c₁ n) (h₂ : c₁ [tm]⊢^{k} c₂) : k ≤ n :=
  le_of_not_gt fun h ↦ haltsIn_gt_not_stepNat _ _ h₁ h h₂

lemma haltsIn_le_stepNat (n k : ℕ) (h₁ : haltsIn tm c₁ n) (h₂ : k ≤ n) : ∃ c, c₁ [tm]⊢^{k} c := by
  have ⟨c, hc⟩ := haltsIn_stepNat _ h₁
  exact stepNat_le_stepNat _ _ hc h₂

/-- Stronger form of `haltsIn_stepNat_le`. -/
lemma haltsIn_stepNat_sub (n k : ℕ) (h₁ : haltsIn tm c₁ n) (h₂ : c₁ [tm]⊢^{k} c₂) :
    haltsIn tm c₂ (n-k) := by
  have ⟨c₃, h₄, h₅⟩ := h₁
  rw [← Nat.sub_add_cancel (haltsIn_stepNat_le _ _ h₁ h₂), add_comm] at h₄
  have ⟨c₂', h₂', h₆⟩ := stepNat_add _ _ h₄
  rcases h₂' ▸ h₂
  exists c₃

lemma stepNat_not_halts_not_halts (n : ℕ) (h₁ : c₁ [tm]⊢^{n} c₂) (h₂ : ¬halts tm c₂) :
    ¬halts tm c₁ :=
  fun ⟨m, hm⟩ ↦ h₂ ⟨m-n, haltsIn_stepNat_sub _ _ hm h₁⟩

lemma step_not_halts_not_halts (h₁ : c₁ [tm]⊢ c₂) (h₂ : ¬halts tm c₂) : ¬halts tm c₁ :=
  stepNat_not_halts_not_halts 1 h₁ h₂

lemma stepStar_not_halts_not_halts (h₁ : c₁ [tm]⊢* c₂) (h₂ : ¬halts tm c₂) : ¬halts tm c₁ :=
  let ⟨n, h₁⟩ := h₁; stepNat_not_halts_not_halts n h₁ h₂

lemma stepPlus_not_halts_not_halts (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : ¬halts tm c₂) : ¬halts tm c₁ :=
  let ⟨n, _, h₁⟩ := h₁; stepNat_not_halts_not_halts n h₁ h₂

lemma progress_nonhalt' (P : Q × Tape Sym → Prop) (h : ∀ c, P c → ∃ c', P c' ∧ c [tm]⊢⁺ c') :
    ∀ k c, P c → ¬haltsIn tm c k := by
  intro k
  induction' k using Nat.strongRecOn with k IH
  intro c hPc hcHalt
  have ⟨c', hc', ⟨l, hl0, hcl⟩⟩ := h c hPc
  refine IH (k-l) ?_ c' hc' ?_
  · have hlk := (haltsIn_stepNat_le _ _ hcHalt hcl)
    exact Nat.sub_lt (hlk.trans_lt' hl0) hl0
  · exact haltsIn_stepNat_sub _ _ hcHalt hcl

lemma progress_nonhalt (P : Q × Tape Sym → Prop) (h₁ : ∀ c, P c → ∃ c', P c' ∧ c [tm]⊢⁺ c')
    (h₂ : P c) : ¬halts tm c :=
  fun ⟨k, hHalt⟩ ↦ progress_nonhalt' P h₁ k c h₂ hHalt

lemma progress_nonhalt_simple {A : Type w} (C : A → Q × Tape Sym) (i₀ : A)
    (h : ∀ i, ∃ i', (C i) [tm]⊢⁺ C i') : ¬halts tm (C i₀) := by
  refine progress_nonhalt (fun c ↦ ∃ i, c = C i) ?_ ⟨i₀, rfl⟩
  intro c ⟨i, hi⟩
  have ⟨i', hi'⟩ := h i
  exact ⟨C i', ⟨i', rfl⟩, hi ▸ hi'⟩


/-!
## Tactics
-/

macro "finish" : tactic => `(tactic| (
  exists 0 <;> fail))
macro "step" : tactic => `(tactic| (
  try apply stepPlus_stepStar
  try simp only [ListBlank.head_cons]
  apply step_stepStar_stepPlus rfl
  simp only [Tape.move, ListBlank.head_cons, ListBlank.tail_cons]))
macro "execute" n:num : tactic => `(tactic| (
  iterate $n step
  finish))
