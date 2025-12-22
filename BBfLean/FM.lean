import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic.Cases
import Mathlib.Util.Notation3

/-!
# Fractran machines (FMs)

Original source: https://github.com/int-y1/proofs/blob/master/BusyLean/TM.lean

Notation precedences:
* 50: `step*` notations, such as `* [fm]⊢ *`.
      This is the same precedence as `=` from `Init.Notation`.
-/

-- We parametrize over...
variable {Q : Type u}     -- The type of states
--variable {q₀ : Q}
--variable [Inhabited Q]    -- The fact that `Q` is nonempty. Use `default` to get the inhabitant.
--                          -- By convention, the starting state is used as the inhabitant.
--                          -- Most lemmas in this file didn't use `[Inhabited Q]`. Omit it.

def FM := Q → Option Q

variable (fm : @FM Q)
variable (c c₁ c₂ c₃ : Q)

/-- `step`. The small-step semantics of Fractran machines. -/
notation3:50 c:60 " [" fm "]⊢ " c':60 => (fm : FM) c = some c'

/-- Executes `n` steps. -/
def stepNat : (n : ℕ) → Q → Option Q :=
  fun n c ↦ n.repeat (fun oc ↦ oc.bind fm) (some c)

/-- `stepNat` executes `n` steps.

Unfortunately, the parser needs a character between `n` and `c'`. I picked `}`. -/
notation3:50 c:60 " [" fm "]⊢^{" n:65 "} " c':60 => stepNat fm n c = some c'

/-- `stepStar` executes an unspecified number of steps (the "eventually reaches" relation). -/
notation3:50 c:60 " [" fm "]⊢* " c':60 => ∃ n, c [fm]⊢^{n} c'

/-- `stepPlus` executes an unspecified, but non-zero number of steps. -/
notation3:50 c:60 " [" fm "]⊢⁺ " c':60 => ∃ n > 0, c [fm]⊢^{n} c'

/-- The Fractran machine has halted if `fm c` returns `none`. -/
def halted : Prop := fm c = none

/-- A Fractran machine halts if it eventually reaches a halting configuration. -/
def haltsIn (n : ℕ) := ∃ c', (c [fm]⊢^{n} c') ∧ halted fm c'

def halts := ∃ n, haltsIn fm c n


/-!
## Not sure where these lemmas should go
-/

/-- todo: why can't i find this in mathlib4? -/
lemma Nat.repeat_add (f : α → α) (n m : ℕ) (a : α) :
    (n+m).repeat f a = n.repeat f (m.repeat f a) := by
  match n with
  | 0 => rw [Nat.zero_add]; rfl
  | n+1 => rw [Nat.add_right_comm, Nat.repeat, Nat.repeat_add]; rfl


/-!
## 1 hypothesis and 1 goal
-/
variable {fm} {c c₁ c₂ c₃}

lemma step_stepNat (h : c₁ [fm]⊢ c₂) : c₁ [fm]⊢^{1} c₂ := h

lemma step_stepStar (h : c₁ [fm]⊢ c₂) : c₁ [fm]⊢* c₂ := by exists 1

lemma step_stepPlus (h : c₁ [fm]⊢ c₂) : c₁ [fm]⊢⁺ c₂ := by exists 1

lemma stepNat_step (h : c₁ [fm]⊢^{1} c₂) : c₁ [fm]⊢ c₂ := h

-- `stepNat_stepStar` is redundant by definition

-- The hypothesis that `c₁ ≠ c₂` doesn't really count.
lemma stepStar_stepPlus (h₁ : c₁ [fm]⊢* c₂) (h₂ : c₁ ≠ c₂) : c₁ [fm]⊢⁺ c₂ := by
  obtain ⟨n, h₁⟩ := h₁
  refine ⟨n, Nat.zero_lt_of_ne_zero ?_, h₁⟩
  rintro rfl
  rw [stepNat, Nat.repeat, Option.some.injEq] at h₁
  contradiction

lemma stepPlus_stepStar (h : c₁ [fm]⊢⁺ c₂) : c₁ [fm]⊢* c₂ := by
  obtain ⟨n, -, h⟩ := h; exists n

lemma halted_not_step (h : halted fm c₁) : ¬c₁ [fm]⊢ c₂ := by
  rw [h]; simp

lemma not_halted_step (h : ¬halted fm c₁) : ∃ c₂, c₁ [fm]⊢ c₂ := by
  match h' : fm c₁ with
  | none => rw [halted] at h; contradiction
  | some c₂' => exists c₂'

lemma halted_halts (h : halted fm c) : halts fm c := by exists 0, c

lemma haltsIn_stepNat (n : ℕ) (h₁ : haltsIn fm c₁ n) : ∃ c, c₁ [fm]⊢^{n} c := by
  obtain ⟨c₂, h₂, -⟩ := h₁; exact ⟨c₂, h₂⟩


/-!
## Lemmas to handle `stepNat`
-/

lemma stepNat_trans (n m : ℕ) (h₁ : c₁ [fm]⊢^{n} c₂) (h₂ : c₂ [fm]⊢^{m} c₃) :
    c₁ [fm]⊢^{n+m} c₃ := by
  rwa [Nat.add_comm, stepNat, Nat.repeat_add, ← stepNat, h₁, ← stepNat]

/-- todo: golf this proof -/
lemma stepNat_succ_stepNat_step (n : ℕ) (h : c₁ [fm]⊢^{n+1} c₃) :
    ∃ c₂, (c₁ [fm]⊢^{n} c₂) ∧ (c₂ [fm]⊢ c₃) := by
  match n with
  | 0 => exists c₁
  | n+1 =>
    rw [Nat.add_comm, stepNat, Nat.repeat_add, ← stepNat, Nat.repeat, Nat.repeat] at h
    match h₂ : stepNat fm (n + 1) c₁ with
    | none => rw [h₂, Option.bind_none] at h; contradiction
    | some c₂' => rw [h₂, Option.bind_some] at h; exists c₂'

/-- todo: golf this proof, it's pretty ugly -/
lemma stepNat_add {c₁ c₃ : Q} (n m : ℕ) (h : c₁ [fm]⊢^{n+m} c₃) :
    ∃ c₂, (c₁ [fm]⊢^{n} c₂) ∧ (c₂ [fm]⊢^{m} c₃) := by
  match m with
  | 0 => exists c₃
  | m+1 =>
    rw [← Nat.add_assoc] at h
    have ⟨c₄, h₄₁, h₄₃⟩ := stepNat_succ_stepNat_step (n+m) h
    have ⟨c₂', h₄₁, h₄₂⟩ := stepNat_add _ _ h₄₁
    refine ⟨c₂', h₄₁, ?_⟩
    rwa [Nat.add_comm, stepNat, Nat.repeat_add, ← stepNat, h₄₂, Nat.repeat, Nat.repeat,
      Option.bind_some]

lemma stepNat_succ_step_stepNat (n : ℕ) (h : c₁ [fm]⊢^{n+1} c₃) :
    ∃ c₂, (c₁ [fm]⊢ c₂) ∧ (c₂ [fm]⊢^{n} c₃) :=
  stepNat_add 1 n (Nat.add_comm 1 n ▸ h)

/-- When using `stepNat_add`, it is often more convenient to have the arithmetic show up as a
separate goal, to be easily discharged. -/
lemma stepNat_add₂ {c₁ c₃ : Q} (n k₁ k₂ : ℕ) (h₁ : c₁ [fm]⊢^{n} c₃) (h₂ : n = k₁ + k₂) :
    ∃ c₂, (c₁ [fm]⊢^{k₁} c₂) ∧ (c₂ [fm]⊢^{k₂} c₃) :=
  stepNat_add k₁ k₂ (h₂ ▸ h₁)

lemma stepNat_le_stepNat (n k : ℕ) (h₁ : c₁ [fm]⊢^{n} c₂) (h₂ : k ≤ n) : ∃ c, c₁ [fm]⊢^{k} c := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le h₂
  have ⟨c₂, hc₂, _⟩ := stepNat_add _ _ h₁
  exact ⟨c₂, hc₂⟩


/-!
## 2 similar hypotheses and 1 goal, or 1 hypothesis and 2 similar goals
-/

lemma step_deterministic (h₁ : c [fm]⊢ c₁) (h₂ : c [fm]⊢ c₂) : c₁ = c₂ := by
  rwa [h₁, Option.some.injEq] at h₂

lemma stepNat_deterministic (n : ℕ) (h₁ : c [fm]⊢^{n} c₁) (h₂ : c [fm]⊢^{n} c₂) : c₁ = c₂ := by
  rwa [h₁, Option.some.injEq] at h₂

lemma stepStar_trans (h₁ : c₁ [fm]⊢* c₂) (h₂ : c₂ [fm]⊢* c₃) : c₁ [fm]⊢* c₃ := by
  obtain ⟨n, h₁⟩ := h₁
  obtain ⟨m, h₂⟩ := h₂
  exact ⟨n+m, stepNat_trans _ _ h₁ h₂⟩

lemma stepPlus_trans (h₁ : c₁ [fm]⊢⁺ c₂) (h₂ : c₂ [fm]⊢⁺ c₃) : c₁ [fm]⊢⁺ c₃ := by
  obtain ⟨n, h₁⟩ := h₁
  obtain ⟨m, h₂⟩ := h₂
  exact ⟨n+m, Nat.add_pos_left h₁.1 _, stepNat_trans _ _ h₁.2 h₂.2⟩


/-!
## 2 different hypotheses and 1 goal
-/

lemma step_haltsIn_succ (n : ℕ) (h₁ : c₁ [fm]⊢ c₂) (h₂ : haltsIn fm c₂ n) :
    haltsIn fm c₁ (n+1) := by
  obtain ⟨c₃, h₂₁, h₂₂⟩ := h₂
  refine ⟨c₃, ?_, h₂₂⟩
  rw [Nat.add_comm]
  exact stepNat_trans _ _ h₁ h₂₁

lemma stepNat_haltsIn_add (n m : ℕ) (h₁ : c₁ [fm]⊢^{m} c₂) (h₂ : haltsIn fm c₂ n) :
    haltsIn fm c₁ (n+m) := by
  obtain ⟨c₃, h₂₁, h₂₂⟩ := h₂
  refine ⟨c₃, ?_, h₂₂⟩
  rw [Nat.add_comm]
  exact stepNat_trans _ _ h₁ h₂₁

lemma step_halts (h₁ : c₁ [fm]⊢ c₂) (h₂ : halts fm c₂) : halts fm c₁ := by
  obtain ⟨n, h₂⟩ := h₂
  exact ⟨n+1, step_haltsIn_succ _ h₁ h₂⟩

lemma stepNat_halts (n : ℕ) (h₁ : c₁ [fm]⊢^{n} c₂) (h₂ : halts fm c₂) : halts fm c₁ := by
  obtain ⟨m, h₂⟩ := h₂
  exact ⟨m+n, stepNat_haltsIn_add _ _ h₁ h₂⟩

lemma stepStar_halts (h₁ : c₁ [fm]⊢* c₂) (h₂ : halts fm c₂) : halts fm c₁ := by
  obtain ⟨n, h₂⟩ := h₂
  obtain ⟨m, h₁⟩ := h₁
  exact ⟨n+m, stepNat_haltsIn_add _ _ h₁ h₂⟩

lemma stepPlus_halts (h₁ : c₁ [fm]⊢⁺ c₂) (h₂ : halts fm c₂) : halts fm c₁ :=
  stepStar_halts (stepPlus_stepStar h₁) h₂

lemma stepStar_stepPlus_stepPlus (h₁ : c₁ [fm]⊢* c₂) (h₂ : c₂ [fm]⊢⁺ c₃) : c₁ [fm]⊢⁺ c₃ := by
  obtain ⟨n, h₁⟩ := h₁
  obtain ⟨m, h₂₁, h₂₂⟩ := h₂
  exact ⟨n+m, Nat.add_pos_right _ h₂₁, stepNat_trans _ _ h₁ h₂₂⟩

lemma step_stepPlus_stepPlus (h₁ : c₁ [fm]⊢ c₂) (h₂ : c₂ [fm]⊢⁺ c₃) : c₁ [fm]⊢⁺ c₃ :=
  stepStar_stepPlus_stepPlus (step_stepStar h₁) h₂

lemma stepStar_step_stepPlus (h₁ : c₁ [fm]⊢* c₂) (h₂ : c₂ [fm]⊢ c₃) : c₁ [fm]⊢⁺ c₃ :=
  stepStar_stepPlus_stepPlus h₁ (step_stepPlus h₂)

lemma stepPlus_stepStar_stepPlus (h₁ : c₁ [fm]⊢⁺ c₂) (h₂ : c₂ [fm]⊢* c₃) : c₁ [fm]⊢⁺ c₃ := by
  obtain ⟨n, h₁₁, h₁₂⟩ := h₁
  obtain ⟨m, h₂⟩ := h₂
  exact ⟨n+m, Nat.add_pos_left h₁₁ _, stepNat_trans _ _ h₁₂ h₂⟩

lemma step_stepStar_stepPlus (h₁ : c₁ [fm]⊢ c₂) (h₂ : c₂ [fm]⊢* c₃) : c₁ [fm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus (step_stepPlus h₁) h₂

lemma stepPlus_step_stepPlus (h₁ : c₁ [fm]⊢⁺ c₂) (h₂ : c₂ [fm]⊢ c₃) : c₁ [fm]⊢⁺ c₃ :=
  stepPlus_stepStar_stepPlus h₁ (step_stepStar h₂)

-- todo: find a nicer proof
lemma stepPlus_split_step_stepStar (h : c₁ [fm]⊢⁺ c₃) : ∃ c₂, (c₁ [fm]⊢ c₂) ∧ (c₂ [fm]⊢* c₃) := by
  obtain ⟨n, h₁, h₂⟩ := h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt h₁
  rw [Nat.zero_add, Nat.add_comm] at h₂
  have ⟨c₂', h₃, h₄⟩ := stepNat_add _ _ h₂
  exact ⟨c₂', h₃, n, h₄⟩

-- todo: find a nicer proof
lemma stepPlus_split_stepStar_step (h : c₁ [fm]⊢⁺ c₃) : ∃ c₂, (c₁ [fm]⊢* c₂) ∧ (c₂ [fm]⊢ c₃) := by
  obtain ⟨n, h₁, h₂⟩ := h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt h₁
  rw [Nat.zero_add] at h₂
  have ⟨c₂', h₃, h₄⟩ := stepNat_add _ _ h₂
  exact ⟨c₂', ⟨n, h₃⟩, h₄⟩


/-!
## Misc
-/

lemma stepPlus_step (h : c₁ [fm]⊢⁺ c₂) : ∃ c, c₁ [fm]⊢ c := by
  have ⟨c', hc', _⟩ := stepPlus_split_step_stepStar h
  exact ⟨c', hc'⟩

lemma halted_not_stepPlus (h : halted fm c₁) : ¬c₁ [fm]⊢⁺ c₂ := by
  intro h'
  have ⟨c', h'⟩ := stepPlus_step h'
  rw [h] at h'
  contradiction

lemma haltsIn_gt_not_stepNat (n k : ℕ) (h₁ : haltsIn fm c₁ n) (h₂ : k > n) : ¬c₁ [fm]⊢^{k} c₂ := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h₂.le
  intro h₃
  have ⟨c', h₄, h₅⟩ := stepNat_add₂ _ _ _ h₃ hm
  obtain ⟨c'', h₄', h₅'⟩ := h₁
  rcases h₄' ▸ h₄
  exact halted_not_stepPlus h₅' ⟨m, Nat.pos_of_lt_add_right (hm ▸ h₂), h₅⟩

lemma haltsIn_stepNat_le (n k : ℕ) (h₁ : haltsIn fm c₁ n) (h₂ : c₁ [fm]⊢^{k} c₂) : k ≤ n :=
  le_of_not_gt fun h ↦ haltsIn_gt_not_stepNat _ _ h₁ h h₂

lemma haltsIn_le_stepNat (n k : ℕ) (h₁ : haltsIn fm c₁ n) (h₂ : k ≤ n) : ∃ c, c₁ [fm]⊢^{k} c := by
  have ⟨c, hc⟩ := haltsIn_stepNat _ h₁
  exact stepNat_le_stepNat _ _ hc h₂

/-- Stronger form of `haltsIn_stepNat_le`. -/
lemma haltsIn_stepNat_sub (n k : ℕ) (h₁ : haltsIn fm c₁ n) (h₂ : c₁ [fm]⊢^{k} c₂) :
    haltsIn fm c₂ (n-k) := by
  have ⟨c₃, h₄, h₅⟩ := h₁
  rw [← Nat.sub_add_cancel (haltsIn_stepNat_le _ _ h₁ h₂), Nat.add_comm] at h₄
  have ⟨c₂', h₂', h₆⟩ := stepNat_add _ _ h₄
  rcases h₂' ▸ h₂
  exists c₃

lemma stepNat_not_halts_not_halts (n : ℕ) (h₁ : c₁ [fm]⊢^{n} c₂) (h₂ : ¬halts fm c₂) :
    ¬halts fm c₁ :=
  fun ⟨m, hm⟩ ↦ h₂ ⟨m-n, haltsIn_stepNat_sub _ _ hm h₁⟩

lemma step_not_halts_not_halts (h₁ : c₁ [fm]⊢ c₂) (h₂ : ¬halts fm c₂) : ¬halts fm c₁ :=
  stepNat_not_halts_not_halts 1 h₁ h₂

lemma stepStar_not_halts_not_halts (h₁ : c₁ [fm]⊢* c₂) (h₂ : ¬halts fm c₂) : ¬halts fm c₁ :=
  let ⟨n, h₁⟩ := h₁; stepNat_not_halts_not_halts n h₁ h₂

lemma stepPlus_not_halts_not_halts (h₁ : c₁ [fm]⊢⁺ c₂) (h₂ : ¬halts fm c₂) : ¬halts fm c₁ :=
  let ⟨n, _, h₁⟩ := h₁; stepNat_not_halts_not_halts n h₁ h₂

lemma progress_nonhalt' (P : Q → Prop) (h : ∀ c, P c → ∃ c', P c' ∧ c [fm]⊢⁺ c') :
    ∀ k c, P c → ¬haltsIn fm c k := by
  intro k
  induction' k using Nat.strongRecOn with k IH
  intro c hPc hcHalt
  have ⟨c', hc', ⟨l, hl0, hcl⟩⟩ := h c hPc
  refine IH (k-l) ?_ c' hc' ?_
  · have hlk := (haltsIn_stepNat_le _ _ hcHalt hcl)
    exact Nat.sub_lt (hlk.trans_lt' hl0) hl0
  · exact haltsIn_stepNat_sub _ _ hcHalt hcl

lemma progress_nonhalt (P : Q → Prop) (h₁ : ∀ c, P c → ∃ c', P c' ∧ c [fm]⊢⁺ c')
    (h₂ : P c) : ¬halts fm c :=
  fun ⟨k, hHalt⟩ ↦ progress_nonhalt' P h₁ k c h₂ hHalt

lemma progress_nonhalt_simple {A : Type w} (C : A → Q) (i₀ : A)
    (h : ∀ i, ∃ i', (C i) [fm]⊢⁺ C i') : ¬halts fm (C i₀) := by
  refine progress_nonhalt (fun c ↦ ∃ i, c = C i) ?_ ⟨i₀, rfl⟩
  intro c ⟨i, hi⟩
  have ⟨i', hi'⟩ := h i
  exact ⟨C i', ⟨i', rfl⟩, hi ▸ hi'⟩


/-!
## Tactics
-/

macro "finish" : tactic => `(tactic| (
  exists 0 <;> fail))
macro "step" fm:ident : tactic => `(tactic| (
  try refine stepPlus_stepStar ?_ -- Use `refine`. `apply` is bad, it adds `.h` to the case name.
  apply step_stepStar_stepPlus (by (try unfold $fm); (try simp only); rfl)
  try simp only [Nat.succ_eq_add_one, Nat.reduceAdd]))
macro "execute" fm:ident n:num : tactic => `(tactic| (
  iterate $n step $fm
  finish))
