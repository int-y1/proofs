import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1849: [9/35, 1/363, 50/3, 11/5, 21/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  0  0 -2
 1 -1  2  0  0
 0  0 -1  0  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1849

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+2⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem drain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e + 2 * k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + 2 * (k + 1) = (e + 2 * k) + 2 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (d + 1) e)
    ring_nf; finish

theorem r1r1r3_loop_e0 : ∀ k, ∀ a b d,
    ⟨a, b, 2, d + 2 * k, 0⟩ [fm]⊢* ⟨a + k, b + 3 * k, 2, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) (b + 3) d)
    ring_nf; finish

theorem r1r1r3_loop_e1 : ∀ k, ∀ a b d,
    ⟨a, b, 2, d + 2 * k, 1⟩ [fm]⊢* ⟨a + k, b + 3 * k, 2, d, 1⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 1) (b + 3) d)
    ring_nf; finish

theorem r3_chain_e0 : ∀ k, ∀ a c,
    ⟨a, k, c, 0, 0⟩ [fm]⊢* ⟨a + k, 0, c + 2 * k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 1) (c + 2))
    ring_nf; finish

theorem r3_chain_e1 : ∀ k, ∀ a c,
    ⟨a, k, c, 0, 1⟩ [fm]⊢* ⟨a + k, 0, c + 2 * k, 0, 1⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 1) (c + 2))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ a e, ⟨a, 0, k, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm
    apply stepStar_trans (ih a (e + 1))
    ring_nf; finish

theorem spiral_even_e0 : ∀ k, ⟨a, 0, 2, 2 * k, 0⟩ [fm]⊢* ⟨a + 4 * k, 0, 6 * k + 2, 0, 0⟩ := by
  intro k
  rw [show 2 * k = 0 + 2 * k from by ring]
  apply stepStar_trans (r1r1r3_loop_e0 k a 0 0)
  rw [show (0 : ℕ) + 3 * k = 3 * k from by ring]
  apply stepStar_trans (r3_chain_e0 (3 * k) (a + k) 2)
  ring_nf; finish

theorem spiral_odd_e0 : ∀ k, ⟨a, 0, 2, 2 * k + 1, 0⟩ [fm]⊢* ⟨a + 4 * k + 2, 0, 6 * k + 5, 0, 0⟩ := by
  intro k
  rw [show 2 * k + 1 = 1 + 2 * k from by ring]
  apply stepStar_trans (r1r1r3_loop_e0 k a 0 1)
  rw [show (0 : ℕ) + 3 * k = 3 * k from by ring]
  step fm
  apply stepStar_trans (r3_chain_e0 (3 * k + 2) (a + k) 1)
  ring_nf; finish

theorem spiral_even_e1 : ∀ k, ⟨a, 0, 2, 2 * k, 1⟩ [fm]⊢* ⟨a + 4 * k, 0, 6 * k + 2, 0, 1⟩ := by
  intro k
  rw [show 2 * k = 0 + 2 * k from by ring]
  apply stepStar_trans (r1r1r3_loop_e1 k a 0 0)
  rw [show (0 : ℕ) + 3 * k = 3 * k from by ring]
  apply stepStar_trans (r3_chain_e1 (3 * k) (a + k) 2)
  ring_nf; finish

theorem spiral_odd_e1 : ∀ k, ⟨a, 0, 2, 2 * k + 1, 1⟩ [fm]⊢* ⟨a + 4 * k + 2, 0, 6 * k + 5, 0, 1⟩ := by
  intro k
  rw [show 2 * k + 1 = 1 + 2 * k from by ring]
  apply stepStar_trans (r1r1r3_loop_e1 k a 0 1)
  rw [show (0 : ℕ) + 3 * k = 3 * k from by ring]
  step fm
  apply stepStar_trans (r3_chain_e1 (3 * k + 2) (a + k) 1)
  ring_nf; finish

theorem inner_De_e0 : ⟨A + 1, 0, 0, 2 * k + 1, 0⟩ [fm]⊢⁺ ⟨A + 4 * k + 5, 0, 0, 0, 6 * k + 8⟩ := by
  step fm; step fm
  rw [show 2 * k + 2 = 2 * (k + 1) from by ring]
  apply stepStar_trans (spiral_even_e0 (k + 1) (a := A + 1))
  rw [show A + 1 + 4 * (k + 1) = A + 4 * k + 5 from by ring,
      show 6 * (k + 1) + 2 = 6 * k + 8 from by ring]
  apply stepStar_trans (r4_chain (6 * k + 8) (A + 4 * k + 5) 0)
  ring_nf; finish

theorem inner_Do_e0 : ⟨A + 1, 0, 0, 2 * k + 2, 0⟩ [fm]⊢⁺ ⟨A + 4 * k + 7, 0, 0, 0, 6 * k + 11⟩ := by
  step fm; step fm
  rw [show 2 * k + 3 = 2 * (k + 1) + 1 from by ring]
  apply stepStar_trans (spiral_odd_e0 (k + 1) (a := A + 1))
  rw [show A + 1 + 4 * (k + 1) + 2 = A + 4 * k + 7 from by ring,
      show 6 * (k + 1) + 5 = 6 * k + 11 from by ring]
  apply stepStar_trans (r4_chain (6 * k + 11) (A + 4 * k + 7) 0)
  ring_nf; finish

theorem inner_De_e1 : ⟨A + 1, 0, 0, 2 * k + 1, 1⟩ [fm]⊢⁺ ⟨A + 4 * k + 5, 0, 0, 0, 6 * k + 9⟩ := by
  step fm; step fm
  rw [show 2 * k + 2 = 2 * (k + 1) from by ring]
  apply stepStar_trans (spiral_even_e1 (k + 1) (a := A + 1))
  rw [show A + 1 + 4 * (k + 1) = A + 4 * k + 5 from by ring,
      show 6 * (k + 1) + 2 = 6 * k + 8 from by ring]
  apply stepStar_trans (r4_chain (6 * k + 8) (A + 4 * k + 5) 1)
  ring_nf; finish

theorem inner_Do_e1 : ⟨A + 1, 0, 0, 2 * k + 2, 1⟩ [fm]⊢⁺ ⟨A + 4 * k + 7, 0, 0, 0, 6 * k + 12⟩ := by
  step fm; step fm
  rw [show 2 * k + 3 = 2 * (k + 1) + 1 from by ring]
  apply stepStar_trans (spiral_odd_e1 (k + 1) (a := A + 1))
  rw [show A + 1 + 4 * (k + 1) + 2 = A + 4 * k + 7 from by ring,
      show 6 * (k + 1) + 5 = 6 * k + 11 from by ring]
  apply stepStar_trans (r4_chain (6 * k + 11) (A + 4 * k + 7) 1)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 5⟩) (by execute fm 10)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 1, 0, 0, 0, e⟩ ∧ 2 * a + 1 ≥ e ∧ e ≥ 5)
  · intro c ⟨a, e, hq, hinv, he5⟩; subst hq
    rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- e even: e = k + k = 2k
      rw [show k + k = 2 * k from by ring] at hk; subst hk
      have hak : a ≥ k := by omega
      obtain ⟨A, rfl⟩ : ∃ A, a = A + k := ⟨a - k, by omega⟩
      -- k >= 3 since e = 2k >= 6 (e >= 5 and even)
      -- After rcases k with _ | k, new k = old k - 1 >= 2
      rcases k with _ | k
      · omega
      · rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
        · rw [show j + j = 2 * j from by ring] at hj; subst hj
          refine ⟨⟨A + 4 * j + 5, 0, 0, 0, 6 * j + 8⟩,
            ⟨A + 4 * j + 4, 6 * j + 8, rfl, by omega, by omega⟩, ?_⟩
          rw [show A + (2 * j + 1) + 1 = (A + 1) + (2 * j + 1) from by ring,
              show 2 * (2 * j + 1) = 0 + 2 * (2 * j + 1) from by ring]
          exact stepStar_stepPlus_stepPlus (drain (2 * j + 1) (A + 1) 0 0)
            (by rw [show (0 : ℕ) + (2 * j + 1) = 2 * j + 1 from by ring]; exact inner_De_e0)
        · subst hj
          refine ⟨⟨A + 4 * j + 7, 0, 0, 0, 6 * j + 11⟩,
            ⟨A + 4 * j + 6, 6 * j + 11, rfl, by omega, by omega⟩, ?_⟩
          rw [show A + (2 * j + 1 + 1) + 1 = (A + 1) + (2 * j + 2) from by ring,
              show 2 * (2 * j + 1 + 1) = 0 + 2 * (2 * j + 2) from by ring]
          exact stepStar_stepPlus_stepPlus (drain (2 * j + 2) (A + 1) 0 0)
            (by rw [show (0 : ℕ) + (2 * j + 2) = 2 * j + 2 from by ring]; exact inner_Do_e0)
    · -- e odd: e = 2k + 1
      subst hk
      have hak : a ≥ k := by omega
      obtain ⟨A, rfl⟩ : ∃ A, a = A + k := ⟨a - k, by omega⟩
      -- k >= 2 since e = 2k+1 >= 5
      rcases k with _ | k
      · omega
      · rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
        · rw [show j + j = 2 * j from by ring] at hj; subst hj
          refine ⟨⟨A + 4 * j + 5, 0, 0, 0, 6 * j + 9⟩,
            ⟨A + 4 * j + 4, 6 * j + 9, rfl, by omega, by omega⟩, ?_⟩
          rw [show A + (2 * j + 1) + 1 = (A + 1) + (2 * j + 1) from by ring,
              show 2 * (2 * j + 1) + 1 = 1 + 2 * (2 * j + 1) from by ring]
          exact stepStar_stepPlus_stepPlus (drain (2 * j + 1) (A + 1) 0 1)
            (by rw [show (0 : ℕ) + (2 * j + 1) = 2 * j + 1 from by ring]; exact inner_De_e1)
        · subst hj
          refine ⟨⟨A + 4 * j + 7, 0, 0, 0, 6 * j + 12⟩,
            ⟨A + 4 * j + 6, 6 * j + 12, rfl, by omega, by omega⟩, ?_⟩
          rw [show A + (2 * j + 1 + 1) + 1 = (A + 1) + (2 * j + 2) from by ring,
              show 2 * (2 * j + 1 + 1) + 1 = 1 + 2 * (2 * j + 2) from by ring]
          exact stepStar_stepPlus_stepPlus (drain (2 * j + 2) (A + 1) 0 1)
            (by rw [show (0 : ℕ) + (2 * j + 2) = 2 * j + 2 from by ring]; exact inner_Do_e1)
  · exact ⟨2, 5, rfl, by omega, by omega⟩
