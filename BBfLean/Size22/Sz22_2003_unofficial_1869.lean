import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1869: [9/35, 25/33, 22/5, 7/11, 605/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  2  0 -1
 1  0 -1  0  1
 0  0  0  1 -1
-1  0  1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1869

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | _ => none

theorem r3_chain : ∀ k, ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a + k, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem spiral : ∀ k, ⟨a, b + k, c + 1, 0, 0⟩ [fm]⊢* ⟨a + k, b, c + k + 1, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a b c
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show (b + k) + 1 = b + k + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a := a + 1) (c := c + 1))
    ring_nf; finish

theorem drain_round : ⟨a + 1, B, 0, D + 5, 0⟩ [fm]⊢* ⟨a, B + 8, 0, D, 0⟩ := by
  execute fm 8

theorem drain_loop : ∀ k, ⟨a + k, B, 0, D + 5 * k, 0⟩ [fm]⊢* ⟨a, B + 8 * k, 0, D, 0⟩ := by
  intro k; induction' k with k ih generalizing a B D
  · exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring,
        show D + 5 * (k + 1) = (D + 5) + 5 * k from by ring]
    apply stepStar_trans (ih (a := a + 1) (D := D + 5))
    rw [show B + 8 * k = B + 8 * k from rfl]
    apply stepStar_trans drain_round
    ring_nf; finish

theorem tail (C : ℕ) : ⟨a, B, C + 1, 0, 0⟩ [fm]⊢* ⟨a + 2 * B + C + 1, 0, 0, B + C + 1, 0⟩ := by
  rw [show B = 0 + B from by ring]
  apply stepStar_trans (spiral B (a := a) (b := 0) (c := C))
  simp only [Nat.zero_add]
  rw [show C + B + 1 = 0 + (B + C + 1) from by ring]
  apply stepStar_trans (r3_chain (B + C + 1) (a := a + B) (c := 0) (e := 0))
  apply stepStar_trans (r4_chain (B + C + 1) (a := a + B + (B + C + 1)) (d := 0) (e := 0))
  simp only [Nat.zero_add]
  ring_nf; finish

theorem macro_r1 (k : ℕ) : ⟨a + k + 1, 0, 0, 5 * k + 1, 0⟩ [fm]⊢⁺ ⟨a + 16 * k + 4, 0, 0, 8 * k + 4, 0⟩ := by
  rw [show 5 * k + 1 = 1 + 5 * k from by ring,
      show a + k + 1 = (a + 1) + k from by ring]
  apply stepStar_stepPlus_stepPlus
    (drain_loop k (a := a + 1) (B := 0) (D := 1))
  simp only [Nat.zero_add]
  step fm; step fm; step fm; step fm
  show ⟨a, 8 * k, 4, 0, 0⟩ [fm]⊢* _
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (tail 3 (a := a) (B := 8 * k))
  ring_nf; finish

theorem macro_r2 (k : ℕ) : ⟨a + k + 1, 0, 0, 5 * k + 2, 0⟩ [fm]⊢⁺ ⟨a + 16 * k + 7, 0, 0, 8 * k + 5, 0⟩ := by
  rw [show 5 * k + 2 = 2 + 5 * k from by ring,
      show a + k + 1 = (a + 1) + k from by ring]
  apply stepStar_stepPlus_stepPlus
    (drain_loop k (a := a + 1) (B := 0) (D := 2))
  simp only [Nat.zero_add]
  step fm; step fm; step fm; step fm; step fm
  show ⟨a, 8 * k + 2, 3, 0, 0⟩ [fm]⊢* _
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (tail 2 (a := a) (B := 8 * k + 2))
  ring_nf; finish

theorem macro_r3 (k : ℕ) : ⟨a + k + 1, 0, 0, 5 * k + 3, 0⟩ [fm]⊢⁺ ⟨a + 16 * k + 10, 0, 0, 8 * k + 6, 0⟩ := by
  rw [show 5 * k + 3 = 3 + 5 * k from by ring,
      show a + k + 1 = (a + 1) + k from by ring]
  apply stepStar_stepPlus_stepPlus
    (drain_loop k (a := a + 1) (B := 0) (D := 3))
  simp only [Nat.zero_add]
  step fm; step fm; step fm; step fm; step fm; step fm
  show ⟨a, 8 * k + 4, 2, 0, 0⟩ [fm]⊢* _
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (tail 1 (a := a) (B := 8 * k + 4))
  ring_nf; finish

theorem macro_r4 (k : ℕ) : ⟨a + k + 1, 0, 0, 5 * k + 4, 0⟩ [fm]⊢⁺ ⟨a + 16 * k + 13, 0, 0, 8 * k + 7, 0⟩ := by
  rw [show 5 * k + 4 = 4 + 5 * k from by ring,
      show a + k + 1 = (a + 1) + k from by ring]
  apply stepStar_stepPlus_stepPlus
    (drain_loop k (a := a + 1) (B := 0) (D := 4))
  simp only [Nat.zero_add]
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  show ⟨a + 1, 8 * k + 5, 2, 0, 0⟩ [fm]⊢* _
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (tail 1 (a := a + 1) (B := 8 * k + 5))
  ring_nf; finish

theorem macro_r0 (k : ℕ) : ⟨a + (k + 1) + 1, 0, 0, 5 * (k + 1), 0⟩ [fm]⊢⁺ ⟨a + 16 * k + 17, 0, 0, 8 * k + 11, 0⟩ := by
  rw [show 5 * (k + 1) = 0 + 5 * (k + 1) from by ring,
      show a + (k + 1) + 1 = (a + 1) + (k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus
    (drain_loop (k + 1) (a := a + 1) (B := 0) (D := 0))
  simp only [Nat.zero_add]
  rw [show 8 * (k + 1) = (8 * k + 6) + 2 from by ring]
  step fm; step fm; step fm
  show ⟨a, 8 * k + 6, 5, 0, 0⟩ [fm]⊢* _
  rw [show (5 : ℕ) = 4 + 1 from by ring]
  apply stepStar_trans (tail 4 (a := a) (B := 8 * k + 6))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨10, 0, 0, 6, 0⟩) (by execute fm 31)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ a ≥ d ∧ d ≥ 3)
  · intro c ⟨a, d, hq, ha, hd⟩; subst hq
    obtain ⟨k, rfl | rfl | rfl | rfl | rfl⟩ : ∃ k, d = 5 * k + 0 ∨ d = 5 * k + 1 ∨ d = 5 * k + 2 ∨ d = 5 * k + 3 ∨ d = 5 * k + 4 :=
      ⟨d / 5, by omega⟩
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, a = m + (k' + 1) + 1 := ⟨a - (k' + 1) - 1, by omega⟩
      refine ⟨_, ⟨m + 16 * k' + 17, 8 * k' + 11, rfl, by omega, by omega⟩, ?_⟩
      show ⟨m + (k' + 1) + 1, 0, 0, 5 * (k' + 1) + 0, 0⟩ [fm]⊢⁺ _
      rw [show 5 * (k' + 1) + 0 = 5 * (k' + 1) from by ring]
      exact macro_r0 k'
    · obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 1 := ⟨a - k - 1, by omega⟩
      exact ⟨_, ⟨m + 16 * k + 4, 8 * k + 4, rfl, by omega, by omega⟩, macro_r1 k⟩
    · obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 1 := ⟨a - k - 1, by omega⟩
      exact ⟨_, ⟨m + 16 * k + 7, 8 * k + 5, rfl, by omega, by omega⟩, macro_r2 k⟩
    · obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 1 := ⟨a - k - 1, by omega⟩
      exact ⟨_, ⟨m + 16 * k + 10, 8 * k + 6, rfl, by omega, by omega⟩, macro_r3 k⟩
    · obtain ⟨m, rfl⟩ : ∃ m, a = m + k + 1 := ⟨a - k - 1, by omega⟩
      exact ⟨_, ⟨m + 16 * k + 13, 8 * k + 7, rfl, by omega, by omega⟩, macro_r4 k⟩
  · exact ⟨10, 6, rfl, by omega, by omega⟩
