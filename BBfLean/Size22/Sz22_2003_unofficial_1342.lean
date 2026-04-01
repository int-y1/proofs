import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1342: [63/10, 25/33, 2/3, 11/7, 105/2]

Vector representation:
```
-1  2 -1  1  0
 0 -1  2  0 -1
 1 -1  0  0  0
 0  0  0 -1  1
-1  1  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1342

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d+1, e⟩
  | _ => none

-- R4 chain: drain d to e (b=0, c=0)
theorem r4_chain : ∀ k, ∀ a d, ⟨a, (0 : ℕ), (0 : ℕ), d + k, (0 : ℕ)⟩ [fm]⊢* ⟨a, (0 : ℕ), (0 : ℕ), d, k⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih a (d + 1))
    step fm
    ring_nf; finish

-- R3 chain: drain b to a (c=0, e=0)
theorem r3_chain : ∀ k, ∀ a b d, ⟨a, b + k, (0 : ℕ), d, (0 : ℕ)⟩ [fm]⊢* ⟨a + k, b, (0 : ℕ), d, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [Nat.add_succ b k]
    step fm  -- R3: (a+1, b+k, 0, d, 0)
    apply stepStar_trans (ih (a + 1) b d)
    ring_nf; finish

-- R2+R1+R1 round chain
theorem round_chain : ∀ k, ∀ a b d e,
    ⟨a + 2 * k, b + 1, (0 : ℕ), d, e + k⟩ [fm]⊢*
    ⟨a, b + 1 + 3 * k, (0 : ℕ), d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · simp; exists 0
  · rw [show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (a + 2) b d (e + 1))
    rw [show b + 1 + 3 * k = (b + 3 * k) + 1 from by ring]
    step fm  -- R2
    step fm  -- R1
    step fm  -- R1
    rw [show b + 3 * k + 4 = b + 1 + 3 * (k + 1) from by ring,
        show d + 2 * k + 2 = d + 2 * (k + 1) from by ring]
    finish

-- R2 drain: each step removes 1 from b and e, adds 2 to c
theorem r2_drain : ∀ k, ∀ b c d,
    ⟨(0 : ℕ), b + k, c, d, k⟩ [fm]⊢* ⟨(0 : ℕ), b, c + 2 * k, d, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · simp; exists 0
  · rw [Nat.add_succ b k]
    step fm  -- R2
    apply stepStar_trans (ih b (c + 2) d)
    ring_nf; finish

-- Spiral: R3+R1 pairs drain c, building b and d
theorem spiral : ∀ k, ∀ b d,
    ⟨(0 : ℕ), b + 1, k, d, (0 : ℕ)⟩ [fm]⊢* ⟨(0 : ℕ), b + 1 + k, (0 : ℕ), d + k, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · simp; exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm  -- R3: (1, b, k+1, d, 0)
    step fm  -- R1: (0, b+2, k, d+1, 0)
    apply stepStar_trans (ih (b + 1) (d + 1))
    ring_nf; finish

-- R5+R1 opening: (a+2, 0, 0, 0, e) → (a, 3, 0, 2, e)
theorem r5r1_open (a e : ℕ) :
    ⟨a + 2, (0 : ℕ), (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢⁺ ⟨a, (3 : ℕ), (0 : ℕ), (2 : ℕ), e⟩ := by
  step fm  -- R5: (a+1, 1, 1, 1, e)
  step fm  -- R1: (a, 3, 0, 2, e)
  finish

-- Even case: a = 2*m
theorem main_transition_even (m e : ℕ) (hle : 2 * m ≤ e) (hge : 4 * m ≥ e) :
    ⟨2 * m + 2, (0 : ℕ), (0 : ℕ), (0 : ℕ), e + 2⟩ [fm]⊢⁺
    ⟨2 * m + e + 5, (0 : ℕ), (0 : ℕ), (0 : ℕ), 2 * e + 6⟩ := by
  apply stepPlus_stepStar_stepPlus (r5r1_open (2 * m) (e + 2))
  -- State: (2*m, 3, 0, 2, e+2)
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 2 * m = 0 + 2 * m from by ring,
      show e + 2 = (e + 2 - m) + m from by omega]
  apply stepStar_trans (round_chain m 0 2 2 (e + 2 - m))
  rw [show 2 + 1 + 3 * m = (4 * m + 1 - e) + (e + 2 - m) from by omega,
      show 2 + 2 * m = 2 * m + 2 from by ring]
  apply stepStar_trans (r2_drain (e + 2 - m) (4 * m + 1 - e) 0 (2 * m + 2))
  rw [show 4 * m + 1 - e = (4 * m - e) + 1 from by omega,
      show 0 + 2 * (e + 2 - m) = 2 * e - 2 * m + 4 from by omega]
  apply stepStar_trans (spiral (2 * e - 2 * m + 4) (4 * m - e) (2 * m + 2))
  rw [show (4 * m - e) + 1 + (2 * e - 2 * m + 4) = 2 * m + e + 5 from by omega,
      show 2 * m + 2 + (2 * e - 2 * m + 4) = 2 * e + 6 from by omega]
  -- State: (0, 2*m+e+5, 0, 2*e+6, 0). Need to reach (2*m+e+5, 0, 0, 0, 2*e+6)
  rw [show (2 * m + e + 5 : ℕ) = 0 + (2 * m + e + 5) from by omega]
  apply stepStar_trans (r3_chain (2 * m + e + 5) 0 0 (2 * e + 6))
  rw [Nat.zero_add, show (2 * e + 6 : ℕ) = 0 + (2 * e + 6) from by omega]
  apply stepStar_trans (r4_chain (2 * e + 6) (2 * m + e + 5) 0)
  ring_nf; finish

-- Odd case: a = 2*m+1
theorem main_transition_odd (m e : ℕ) (hle : 2 * m + 1 ≤ e) (hge : 4 * m + 2 ≥ e) :
    ⟨2 * m + 3, (0 : ℕ), (0 : ℕ), (0 : ℕ), e + 2⟩ [fm]⊢⁺
    ⟨2 * m + e + 6, (0 : ℕ), (0 : ℕ), (0 : ℕ), 2 * e + 6⟩ := by
  apply stepPlus_stepStar_stepPlus (r5r1_open (2 * m + 1) (e + 2))
  -- State: (2*m+1, 3, 0, 2, e+2)
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 2 * m + 1 = 1 + 2 * m from by ring,
      show e + 2 = (e + 2 - m) + m from by omega]
  apply stepStar_trans (round_chain m 1 2 2 (e + 2 - m))
  -- State: (1, 3+3*m, 0, 2+2*m, e+2-m)
  rw [show 2 + 1 + 3 * m = (3 * m + 2) + 1 from by ring,
      show 2 + 2 * m = 2 * m + 2 from by ring,
      show e + 2 - m = (e + 1 - m) + 1 from by omega]
  -- Half step: R2 + R1
  step fm  -- R2
  step fm  -- R1
  -- State: (0, 3*m+4, 1, 2*m+3, e+1-m)
  rw [show 3 * m + 2 + 2 = (4 * m + 3 - e) + (e + 1 - m) from by omega,
      show 2 * m + 2 + 1 = 2 * m + 3 from by ring]
  apply stepStar_trans (r2_drain (e + 1 - m) (4 * m + 3 - e) 1 (2 * m + 3))
  rw [show 4 * m + 3 - e = (4 * m + 2 - e) + 1 from by omega,
      show 1 + 2 * (e + 1 - m) = 2 * e - 2 * m + 3 from by omega]
  apply stepStar_trans (spiral (2 * e - 2 * m + 3) (4 * m + 2 - e) (2 * m + 3))
  rw [show (4 * m + 2 - e) + 1 + (2 * e - 2 * m + 3) = 2 * m + e + 6 from by omega,
      show 2 * m + 3 + (2 * e - 2 * m + 3) = 2 * e + 6 from by omega]
  rw [show (2 * m + e + 6 : ℕ) = 0 + (2 * m + e + 6) from by omega]
  apply stepStar_trans (r3_chain (2 * m + e + 6) 0 0 (2 * e + 6))
  rw [Nat.zero_add, show (2 * e + 6 : ℕ) = 0 + (2 * e + 6) from by omega]
  apply stepStar_trans (r4_chain (2 * e + 6) (2 * m + e + 6) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 2, 0, 0, 0, e + 2⟩ ∧ a ≤ e ∧ 2 * a ≥ e)
  · intro c ⟨a, e, hq, hle, hge⟩
    subst hq
    rcases Nat.even_or_odd a with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [show m + m = 2 * m from by ring] at hm
      subst hm
      refine ⟨⟨2 * m + e + 5, 0, 0, 0, 2 * e + 6⟩,
        ⟨2 * m + e + 3, 2 * e + 4, rfl, by omega, by omega⟩,
        ?_⟩
      exact main_transition_even m e (by omega) (by omega)
    · rw [show 2 * m + 1 = 2 * m + 1 from rfl] at hm
      subst hm
      refine ⟨⟨2 * m + e + 6, 0, 0, 0, 2 * e + 6⟩,
        ⟨2 * m + e + 4, 2 * e + 4, rfl, by omega, by omega⟩,
        ?_⟩
      exact main_transition_odd m e (by omega) (by omega)
  · exact ⟨0, 0, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1342
