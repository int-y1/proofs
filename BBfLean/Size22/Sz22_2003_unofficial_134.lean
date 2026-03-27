import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #134: [1/45, 196/15, 3/7, 25/2, 21/5]

Vector representation:
```
 0 -2 -1  0
 2 -1 -1  2
 0  1  0 -1
-1  0  2  0
 0  1 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6

---

The canonical state is `(0, 0, m+2, 0)`. The transition splits by `m mod 4`:
- `m = 4k`:   `(0, 0, 4k+2, 0) ->+ (0, 0, 14k+5,  0)`
- `m = 4k+1`: `(0, 0, 4k+3, 0) ->+ (0, 0, 14k+6,  0)`
- `m = 4k+2`: `(0, 0, 4k+4, 0) ->+ (0, 0, 14k+17, 0)`
- `m = 4k+3`: `(0, 0, 4k+5, 0) ->+ (0, 0, 14k+13, 0)`

In all cases `c` strictly increases, so the machine never halts.

Phases:
1. Pairing: `(a, 0, m+1, d+1) ->* (a+2m+2, 0, 0, d+m+2)`
2. d-to-b:  `(a, 0, 0, d)    ->* (a, d, 0, 0)`
3. b-reduction (4 sub-lemmas by `b mod 4`)
4. a-to-c:  `(a, 0, c, 0)    ->* (0, 0, c+2a, 0)`
-/

namespace Sz22_2003_unofficial_134

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+2, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+2, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b+1, c, d+1⟩
  | _ => none

private theorem tuple_eq {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : ℕ}
    (h1 : a₁ = a₂) (h2 : b₁ = b₂) (h3 : c₁ = c₂) (h4 : d₁ = d₂) :
    (⟨a₁, b₁, c₁, d₁⟩ : Q) = ⟨a₂, b₂, c₂, d₂⟩ := by
  subst h1; subst h2; subst h3; subst h4; rfl

-- Phase 1: Pairing loop
-- (a, 0, m+1, d+1) ->* (a+2*m+2, 0, 0, d+m+2)
-- Each step: rule 3 (d+1 -> d, b -> b+1), then rule 2 (b=1, c -> c-1, a += 2, d += 2)
theorem pairing_loop : ∀ m a d,
    ⟨a, 0, m+1, d+1⟩ [fm]⊢* ⟨a+2*m+2, 0, 0, d+m+2⟩ := by
  intro m; induction' m with m ih <;> intro a d
  · step fm; step fm; finish
  · rw [show (⟨a, 0, (m+1)+1, d+1⟩ : Q) = ⟨a, 0, m+1+1, d+1⟩ from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a+2) (d+1))
    ring_nf; finish

-- Phase 2: d to b (generalized)
-- (a, b, 0, k) ->* (a, b+k, 0, 0)
theorem d_to_b_gen : ∀ k a b,
    ⟨a, b, 0, k⟩ [fm]⊢* ⟨a, b+k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · finish
  · step fm
    apply stepStar_trans (ih a (b+1))
    ring_nf; finish

-- Phase 2: d to b (special case b=0)
theorem d_to_b : ∀ k a,
    ⟨a, 0, 0, k⟩ [fm]⊢* ⟨a, k, 0, 0⟩ := by
  intro k a
  have h := d_to_b_gen k a 0
  simp at h
  exact h

-- Phase 4: a to c
-- (a, 0, c, 0) ->* (0, 0, c+2*a, 0)
theorem a_to_c : ∀ a c,
    ⟨a, 0, c, 0⟩ [fm]⊢* ⟨0, 0, c+2*a, 0⟩ := by
  intro a; induction' a with a ih <;> intro c
  · finish
  · step fm
    apply stepStar_trans (ih (c+2))
    ring_nf; finish

-- b-reduction: 3-step reduction by 4
-- (a+1, k+4, 0, 0) ->* (a, k, 0, 0)
theorem b_eat_4 : ⟨a+1, k+4, 0, 0⟩ [fm]⊢* ⟨a, k, 0, 0⟩ := by
  execute fm 3

-- b-reduction base: b=2
-- (a+1, 2, 0, 0) ->* (a, 0, 1, 0)
theorem b_red_2 : ⟨a+1, 2, 0, 0⟩ [fm]⊢* ⟨a, 0, 1, 0⟩ := by
  execute fm 2

-- b-reduction base: b=3
-- (a+1, 3, 0, 0) ->* (a+1, 0, 1, 0)
theorem b_red_3 : ⟨a+1, 3, 0, 0⟩ [fm]⊢* ⟨a+1, 0, 1, 0⟩ := by
  execute fm 7

-- b-reduction base: b=1
-- (a+1, 1, 0, 0) ->* (a+4, 3, 0, 0)
theorem b_red_1 : ⟨a+1, 1, 0, 0⟩ [fm]⊢* ⟨a+4, 3, 0, 0⟩ := by
  execute fm 7

-- b-reduction for b = 4k+2
-- (a+k+1, 4*k+2, 0, 0) ->* (a, 0, 1, 0)
theorem b_red_42 : ∀ k a,
    ⟨a+k+1, 4*k+2, 0, 0⟩ [fm]⊢* ⟨a, 0, 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro a
  · exact b_red_2
  · rw [show (⟨a+(k+1)+1, 4*(k+1)+2, 0, 0⟩ : Q) = ⟨(a+k+1)+1, (4*k+2)+4, 0, 0⟩
      from tuple_eq (by ring) (by ring) rfl rfl]
    exact stepStar_trans b_eat_4 (ih a)

-- b-reduction for b = 4(k+1)
-- (a+k+1, 4*(k+1), 0, 0) ->* (a, 0, 0, 0)
theorem b_red_4 : ∀ k a,
    ⟨a+k+1, 4*(k+1), 0, 0⟩ [fm]⊢* ⟨a, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a
  · execute fm 3
  · rw [show (⟨a+(k+1)+1, 4*((k+1)+1), 0, 0⟩ : Q) = ⟨(a+k+1)+1, (4*(k+1))+4, 0, 0⟩
      from tuple_eq (by ring) (by ring) rfl rfl]
    exact stepStar_trans b_eat_4 (ih a)

-- b-reduction for b = 4k+3
-- (a+k+1, 4*k+3, 0, 0) ->* (a+1, 0, 1, 0)
theorem b_red_43 : ∀ k a,
    ⟨a+k+1, 4*k+3, 0, 0⟩ [fm]⊢* ⟨a+1, 0, 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro a
  · exact b_red_3
  · rw [show (⟨a+(k+1)+1, 4*(k+1)+3, 0, 0⟩ : Q) = ⟨(a+k+1)+1, (4*k+3)+4, 0, 0⟩
      from tuple_eq (by ring) (by ring) rfl rfl]
    exact stepStar_trans b_eat_4 (ih a)

-- b-reduction for b = 4k+1
-- (a+k+1, 4*k+1, 0, 0) ->* (a+4, 0, 1, 0)
theorem b_red_41 : ∀ k a,
    ⟨a+k+1, 4*k+1, 0, 0⟩ [fm]⊢* ⟨a+4, 0, 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro a
  · exact stepStar_trans b_red_1 b_red_3
  · rw [show (⟨a+(k+1)+1, 4*(k+1)+1, 0, 0⟩ : Q) = ⟨(a+k+1)+1, (4*k+1)+4, 0, 0⟩
      from tuple_eq (by ring) (by ring) rfl rfl]
    exact stepStar_trans b_eat_4 (ih a)

-- Phase 1 combined: (0, 0, c+2, 0) ->* (2c+2, 0, 0, c+3)
theorem phase1 : ∀ c, ⟨0, 0, c+2, 0⟩ [fm]⊢* ⟨2*c+2, 0, 0, c+3⟩ := by
  intro c; cases c with
  | zero => execute fm 2
  | succ c =>
    step fm; step fm
    apply stepStar_trans (pairing_loop c 2 2)
    ring_nf; finish

-- Main transition mod 0: (0, 0, 4k+2, 0) ->+ (0, 0, 14k+5, 0)
theorem trans_mod0 : ⟨0, 0, 4*k+2, 0⟩ [fm]⊢⁺ ⟨0, 0, 14*k+5, 0⟩ := by
  rw [show (⟨0, 0, 4*k+2, 0⟩ : Q) = ⟨0, 0, 4*k+2, 0⟩ from rfl]
  -- First two steps to get stepPlus
  apply step_stepStar_stepPlus (by unfold fm; rfl : (⟨0, 0, 4*k+2, 0⟩ : Q) [fm]⊢ ⟨0, 1, 4*k+1, 1⟩)
  -- Now stepStar from (0, 1, 4k+1, 1) to target
  step fm
  -- After rule 2: (2, 0, 4k, 3)
  -- Phase 1 (pairing_loop): (2, 0, 4k, 3)
  -- If 4k = 0: (2, 0, 0, 3) -> d_to_b -> (2, 3, 0, 0)
  -- If 4k >= 1: pairing_loop then d_to_b
  cases k with
  | zero =>
    -- (2, 0, 0, 3): d_to_b -> (2, 3, 0, 0) -> b_red_3 -> (2, 0, 1, 0) -> a_to_c
    apply stepStar_trans (d_to_b 3 2)
    apply stepStar_trans b_red_3
    rw [show (⟨0+1+1, 0, 1, 0⟩ : Q) = ⟨2, 0, 1, 0⟩ from tuple_eq (by ring) rfl rfl rfl]
    exact a_to_c 2 1
  | succ k =>
    -- (2, 0, 4k+4, 3) = (2, 0, (4k+3)+1, 2+1)
    rw [show (⟨2, 0, 4*(k+1), 3⟩ : Q) = ⟨2, 0, (4*k+3)+1, 2+1⟩
      from tuple_eq rfl rfl (by ring) rfl]
    apply stepStar_trans (pairing_loop (4*k+3) 2 2)
    -- Result: (2+2*(4k+3)+2, 0, 0, 2+(4k+3)+2) = (8k+10, 0, 0, 4k+7)
    rw [show (⟨2+2*(4*k+3)+2, 0, 0, 2+(4*k+3)+2⟩ : Q) = ⟨8*k+10, 0, 0, 4*k+7⟩
      from tuple_eq (by ring) rfl rfl (by ring)]
    apply stepStar_trans (d_to_b (4*k+7) (8*k+10))
    -- b_red_43: (8k+10, 4k+7, 0, 0). b = 4k+7 = 4(k+1)+3. a = 8k+10.
    -- Need: a = a'+(k+1)+1 = a'+k+2. a' = 8k+10-k-2 = 7k+8.
    -- Result: (7k+9, 0, 1, 0).
    rw [show (⟨8*k+10, 4*k+7, 0, 0⟩ : Q) = ⟨(7*k+8)+(k+1)+1, 4*(k+1)+3, 0, 0⟩
      from tuple_eq (by ring) (by ring) rfl rfl]
    apply stepStar_trans (b_red_43 (k+1) (7*k+8))
    rw [show (⟨(7*k+8)+1, 0, 1, 0⟩ : Q) = ⟨7*k+9, 0, 1, 0⟩
      from tuple_eq (by ring) rfl rfl rfl]
    -- Phase 4: a_to_c
    have h := a_to_c (7*k+9) 1
    rw [show (⟨0, 0, 1+2*(7*k+9), 0⟩ : Q) = ⟨0, 0, 14*(k+1)+5, 0⟩
      from tuple_eq rfl rfl (by ring) rfl] at h
    exact h

-- Main transition mod 1: (0, 0, 4k+3, 0) ->+ (0, 0, 14k+6, 0)
theorem trans_mod1 : ⟨0, 0, 4*k+3, 0⟩ [fm]⊢⁺ ⟨0, 0, 14*k+6, 0⟩ := by
  -- Phase 1: (0, 0, 4k+3, 0) ->* (8k+4, 0, 0, 4k+4)
  apply step_stepStar_stepPlus (by unfold fm; rfl : (⟨0, 0, 4*k+3, 0⟩ : Q) [fm]⊢ ⟨0, 1, 4*k+2, 1⟩)
  step fm
  -- (2, 0, 4k+1, 3) = (2, 0, (4k)+1, 2+1)
  rw [show (⟨2, 0, 4*k+1, 3⟩ : Q) = ⟨2, 0, (4*k)+1, 2+1⟩ from tuple_eq rfl rfl (by ring) rfl]
  apply stepStar_trans (pairing_loop (4*k) 2 2)
  rw [show (⟨2+2*(4*k)+2, 0, 0, 2+(4*k)+2⟩ : Q) = ⟨8*k+4, 0, 0, 4*k+4⟩
    from tuple_eq (by ring) rfl rfl (by ring)]
  -- Phase 2: d_to_b
  apply stepStar_trans (d_to_b (4*k+4) (8*k+4))
  -- b = 4k+4 = 4(k+1). b_red_4: (a'+k+1, 4(k+1), 0, 0) ->* (a', 0, 0, 0)
  -- a = 8k+4 = (7k+3)+k+1. a' = 7k+3.
  rw [show (⟨8*k+4, 4*k+4, 0, 0⟩ : Q) = ⟨(7*k+3)+k+1, 4*(k+1), 0, 0⟩
    from tuple_eq (by ring) (by ring) rfl rfl]
  apply stepStar_trans (b_red_4 k (7*k+3))
  -- Phase 4: (7k+3, 0, 0, 0) -> (0, 0, 2*(7k+3), 0)
  have h := a_to_c (7*k+3) 0
  rw [show (⟨0, 0, 0+2*(7*k+3), 0⟩ : Q) = ⟨0, 0, 14*k+6, 0⟩
    from tuple_eq rfl rfl (by ring) rfl] at h
  exact h

-- Main transition mod 2: (0, 0, 4k+4, 0) ->+ (0, 0, 14k+17, 0)
theorem trans_mod2 : ⟨0, 0, 4*k+4, 0⟩ [fm]⊢⁺ ⟨0, 0, 14*k+17, 0⟩ := by
  apply step_stepStar_stepPlus (by unfold fm; rfl : (⟨0, 0, 4*k+4, 0⟩ : Q) [fm]⊢ ⟨0, 1, 4*k+3, 1⟩)
  step fm
  -- (2, 0, 4k+2, 3) = (2, 0, (4k+1)+1, 2+1)
  rw [show (⟨2, 0, 4*k+2, 3⟩ : Q) = ⟨2, 0, (4*k+1)+1, 2+1⟩ from tuple_eq rfl rfl (by ring) rfl]
  apply stepStar_trans (pairing_loop (4*k+1) 2 2)
  rw [show (⟨2+2*(4*k+1)+2, 0, 0, 2+(4*k+1)+2⟩ : Q) = ⟨8*k+6, 0, 0, 4*k+5⟩
    from tuple_eq (by ring) rfl rfl (by ring)]
  apply stepStar_trans (d_to_b (4*k+5) (8*k+6))
  -- b = 4k+5 = 4(k+1)+1. b_red_41: (a'+(k+1)+1, 4(k+1)+1, 0, 0) ->* (a'+4, 0, 1, 0)
  -- a = 8k+6 = a'+k+2. a' = 7k+4.
  rw [show (⟨8*k+6, 4*k+5, 0, 0⟩ : Q) = ⟨(7*k+4)+(k+1)+1, 4*(k+1)+1, 0, 0⟩
    from tuple_eq (by ring) (by ring) rfl rfl]
  apply stepStar_trans (b_red_41 (k+1) (7*k+4))
  rw [show (⟨(7*k+4)+4, 0, 1, 0⟩ : Q) = ⟨7*k+8, 0, 1, 0⟩ from tuple_eq (by ring) rfl rfl rfl]
  have h := a_to_c (7*k+8) 1
  rw [show (⟨0, 0, 1+2*(7*k+8), 0⟩ : Q) = ⟨0, 0, 14*k+17, 0⟩
    from tuple_eq rfl rfl (by ring) rfl] at h
  exact h

-- Main transition mod 3: (0, 0, 4k+5, 0) ->+ (0, 0, 14k+13, 0)
theorem trans_mod3 : ⟨0, 0, 4*k+5, 0⟩ [fm]⊢⁺ ⟨0, 0, 14*k+13, 0⟩ := by
  apply step_stepStar_stepPlus (by unfold fm; rfl : (⟨0, 0, 4*k+5, 0⟩ : Q) [fm]⊢ ⟨0, 1, 4*k+4, 1⟩)
  step fm
  -- (2, 0, 4k+3, 3) = (2, 0, (4k+2)+1, 2+1)
  rw [show (⟨2, 0, 4*k+3, 3⟩ : Q) = ⟨2, 0, (4*k+2)+1, 2+1⟩ from tuple_eq rfl rfl (by ring) rfl]
  apply stepStar_trans (pairing_loop (4*k+2) 2 2)
  rw [show (⟨2+2*(4*k+2)+2, 0, 0, 2+(4*k+2)+2⟩ : Q) = ⟨8*k+8, 0, 0, 4*k+6⟩
    from tuple_eq (by ring) rfl rfl (by ring)]
  apply stepStar_trans (d_to_b (4*k+6) (8*k+8))
  -- b = 4k+6 = 4(k+1)+2. b_red_42: (a'+(k+1)+1, 4(k+1)+2, 0, 0) ->* (a', 0, 1, 0)
  -- a = 8k+8 = a'+k+2. a' = 7k+6.
  rw [show (⟨8*k+8, 4*k+6, 0, 0⟩ : Q) = ⟨(7*k+6)+(k+1)+1, 4*(k+1)+2, 0, 0⟩
    from tuple_eq (by ring) (by ring) rfl rfl]
  apply stepStar_trans (b_red_42 (k+1) (7*k+6))
  have h := a_to_c (7*k+6) 1
  rw [show (⟨0, 0, 1+2*(7*k+6), 0⟩ : Q) = ⟨0, 0, 14*k+13, 0⟩
    from tuple_eq rfl rfl (by ring) rfl] at h
  exact h

private theorem progress_step (m : ℕ) :
    ∃ m', (⟨0, 0, m+2, 0⟩ : Q) [fm]⊢⁺ ⟨0, 0, m'+2, 0⟩ := by
  have hmod := Nat.div_add_mod m 4
  set q := m / 4
  set r := m % 4
  have hr : r < 4 := Nat.mod_lt m (by omega)
  interval_cases r
  · rw [show m = 4 * q from by omega]
    exact ⟨14*q+3, by
      rw [show (⟨0, 0, (14*q+3)+2, 0⟩ : Q) = ⟨0, 0, 14*q+5, 0⟩
        from tuple_eq rfl rfl (by ring) rfl]
      exact trans_mod0⟩
  · rw [show m = 4 * q + 1 from by omega]
    exact ⟨14*q+4, by
      rw [show (⟨0, 0, 4*q+1+2, 0⟩ : Q) = ⟨0, 0, 4*q+3, 0⟩
        from tuple_eq rfl rfl (by ring) rfl,
        show (⟨0, 0, (14*q+4)+2, 0⟩ : Q) = ⟨0, 0, 14*q+6, 0⟩
        from tuple_eq rfl rfl (by ring) rfl]
      exact trans_mod1⟩
  · rw [show m = 4 * q + 2 from by omega]
    exact ⟨14*q+15, by
      rw [show (⟨0, 0, 4*q+2+2, 0⟩ : Q) = ⟨0, 0, 4*q+4, 0⟩
        from tuple_eq rfl rfl (by ring) rfl,
        show (⟨0, 0, (14*q+15)+2, 0⟩ : Q) = ⟨0, 0, 14*q+17, 0⟩
        from tuple_eq rfl rfl (by ring) rfl]
      exact trans_mod2⟩
  · rw [show m = 4 * q + 3 from by omega]
    exact ⟨14*q+11, by
      rw [show (⟨0, 0, 4*q+3+2, 0⟩ : Q) = ⟨0, 0, 4*q+5, 0⟩
        from tuple_eq rfl rfl (by ring) rfl,
        show (⟨0, 0, (14*q+11)+2, 0⟩ : Q) = ⟨0, 0, 14*q+13, 0⟩
        from tuple_eq rfl rfl (by ring) rfl]
      exact trans_mod3⟩

private theorem nonhalt_canonical : ¬halts fm (⟨0, 0, 2, 0⟩ : Q) := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ m, q = ⟨0, 0, m+2, 0⟩)
  · intro c ⟨m, hq⟩; subst hq
    obtain ⟨m', hm'⟩ := progress_step m
    exact ⟨_, ⟨m', rfl⟩, hm'⟩
  · exact ⟨0, rfl⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply step_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0⟩)
  · rfl
  · exact nonhalt_canonical
