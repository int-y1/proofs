import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1936: [9/70, 275/7, 7/15, 2/11, 49/2]

Vector representation:
```
-1  2 -1 -1  0
 0  0  2 -1  1
 0 -1 -1  1  0
 1  0  0  0 -1
-1  0  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1936

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | _ => none

theorem r4_chain : ∀ k, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a + k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a := a + 1) (e := e)); ring_nf; finish

theorem r3r2_chain : ∀ k, ⟨0, b + k, c + 1, 0, e⟩ [fm]⊢* ⟨0, b, c + 1 + k, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing b c e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring, show c + 1 = (c + 0) + 1 from by ring]
    step fm; rw [show c + 0 = c from by ring]; step fm
    apply stepStar_trans (ih (b := b) (c := c + 1) (e := e + 1)); ring_nf; finish

theorem r3r1_chain : ∀ k, ⟨a + k, b + 1, c + 2 * k, 0, 0⟩ [fm]⊢* ⟨a, b + k + 1, c, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a b c
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a := a) (b := b + 1) (c := c)); ring_nf; finish

theorem loop_phase : ∀ j, ⟨j, b + 2, 1, 0, 1⟩ [fm]⊢* ⟨0, b + 2 + 2 * j, 1, 0, 1⟩ := by
  intro j; induction' j with j ih generalizing b
  · exists 0
  · step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (b := b + 2)); ring_nf; finish

theorem odd_phaseC : ⟨k + 3, k + 5, 3, 0, 0⟩ [fm]⊢* ⟨k, k + 8, 1, 0, 1⟩ := by
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; step fm; finish

theorem even_phaseC : ⟨k + 3, k + 6, 2, 0, 0⟩ [fm]⊢* ⟨k, k + 9, 1, 0, 1⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

theorem drain_r4 (N : ℕ) : ⟨0, N, 1, 0, 1⟩ [fm]⊢* ⟨N + 1, 0, N + 1, 0, 0⟩ := by
  have h1 : ⟨0, 0 + N, 0 + 1, 0, 1⟩ [fm]⊢* ⟨0, 0, 0 + 1 + N, 0, 1 + N⟩ :=
    r3r2_chain N (b := 0) (c := 0) (e := 1)
  simp only [Nat.zero_add] at h1
  have h2 : ⟨0, 0, N + 1, 0, 0 + (N + 1)⟩ [fm]⊢* ⟨0 + (N + 1), 0, N + 1, 0, 0⟩ :=
    r4_chain (N + 1) (a := 0) (c := N + 1) (e := 0)
  simp only [Nat.zero_add] at h2
  apply stepStar_trans h1
  rw [show 1 + N = N + 1 from by ring]
  exact h2

theorem odd_trans : ⟨2 * k + 7, 0, 2 * k + 7, 0, 0⟩ [fm]⊢⁺ ⟨3 * k + 9, 0, 3 * k + 9, 0, 0⟩ := by
  step fm; step fm; step fm
  rw [show (2 * k + 4 : ℕ) = (k + 3) + (k + 1) from by ring,
      show (4 : ℕ) = 3 + 1 from by ring,
      show (2 * k + 5 : ℕ) = 3 + 2 * (k + 1) from by ring]
  apply stepStar_trans (r3r1_chain (k + 1) (a := k + 3) (b := 3) (c := 3))
  rw [show 3 + (k + 1) + 1 = k + 5 from by ring]
  apply stepStar_trans (odd_phaseC (k := k))
  rw [show k + 8 = (k + 6) + 2 from by ring]
  apply stepStar_trans (loop_phase k (b := k + 6))
  rw [show k + 6 + 2 + 2 * k = 3 * k + 8 from by ring]
  apply stepStar_trans (drain_r4 (3 * k + 8))
  ring_nf; finish

theorem even_trans : ⟨2 * k + 8, 0, 2 * k + 8, 0, 0⟩ [fm]⊢⁺ ⟨3 * k + 10, 0, 3 * k + 10, 0, 0⟩ := by
  step fm; step fm; step fm
  rw [show (2 * k + 5 : ℕ) = (k + 3) + (k + 2) from by ring,
      show (4 : ℕ) = 3 + 1 from by ring,
      show (2 * k + 6 : ℕ) = 2 + 2 * (k + 2) from by ring]
  apply stepStar_trans (r3r1_chain (k + 2) (a := k + 3) (b := 3) (c := 2))
  rw [show 3 + (k + 2) + 1 = k + 6 from by ring]
  apply stepStar_trans (even_phaseC (k := k))
  rw [show k + 9 = (k + 7) + 2 from by ring]
  apply stepStar_trans (loop_phase k (b := k + 7))
  rw [show k + 7 + 2 + 2 * k = 3 * k + 9 from by ring]
  apply stepStar_trans (drain_r4 (3 * k + 9))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨11, 0, 11, 0, 0⟩)
  · execute fm 195
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨n, 0, n, 0, 0⟩ ∧ n ≥ 7)
  · intro c ⟨n, hq, hn⟩; subst hq
    rcases Nat.even_or_odd n with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 4 := ⟨K - 4, by omega⟩
      exact ⟨⟨3 * k + 10, 0, 3 * k + 10, 0, 0⟩,
        ⟨3 * k + 10, rfl, by omega⟩, even_trans⟩
    · subst hK
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 3 := ⟨K - 3, by omega⟩
      refine ⟨⟨3 * k + 9, 0, 3 * k + 9, 0, 0⟩,
        ⟨3 * k + 9, rfl, by omega⟩, ?_⟩
      show ⟨2 * (k + 3) + 1, 0, 2 * (k + 3) + 1, 0, 0⟩ [fm]⊢⁺ _
      rw [show 2 * (k + 3) + 1 = 2 * k + 7 from by ring]
      exact odd_trans
  · exact ⟨11, rfl, by omega⟩

end Sz22_2003_unofficial_1936
