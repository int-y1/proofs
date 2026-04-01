import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1257: [5/6, 77/2, 8/35, 3/7, 14/11]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  1  1
 3  0 -1 -1  0
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1257

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- Move d to b via R4
theorem d_to_b : ∀ k, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d
  · exists 0
  · rw [Nat.add_succ d k]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- Opening: (0, d+1, 0, 0, e+1) ⊢⁺ (3, d, 0, 0, e)
theorem opening : ⟨0, d + 1, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨3, d, 0, 0, e⟩ := by
  step fm; step fm; step fm; finish

-- One spiral round: (3, b+4, c, 0, e+1) ⊢* (3, b, c+3, 0, e)
theorem spiral_one : ⟨3, b + 4, c, 0, e + 1⟩ [fm]⊢* ⟨3, b, c + 3, 0, e⟩ := by
  rw [show b + 4 = b + 1 + 1 + 1 + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm; step fm
  ring_nf; finish

-- Spiral chain: k rounds
theorem spiral_chain : ∀ k, ⟨3, b + 4 * k, c, 0, e + k⟩ [fm]⊢* ⟨3, b, c + 3 * k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing b c e
  · exists 0
  · rw [show b + 4 * (k + 1) = (b + 4) + 4 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b := b + 4) (e := e + 1))
    apply stepStar_trans (spiral_one (b := b) (c := c + 3 * k) (e := e))
    ring_nf; finish

-- drain_c: R3-R2-R2-R2 chain
theorem drain_c : ∀ k, ∀ c d e, ⟨0, 0, c + k, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + 1 + 2 * k, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = c + k + 1 from by ring]
    step fm; step fm; step fm; step fm
    rw [show d + 1 + 1 + 1 = (d + 2) + 1 from by ring,
        show e + 1 + 1 + 1 = e + 3 from by ring]
    apply stepStar_trans (ih c (d + 2) (e + 3))
    ring_nf; finish

-- End case r=0: (3, 0, c, 0, e) ⊢* (0, 0, 0, 2*c+3, e+3*c+3)
theorem end_r0 : ⟨3, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * c + 3, e + 3 * c + 3⟩ := by
  step fm; step fm; step fm
  show ⟨0, 0, c, 3, e + 3⟩ [fm]⊢* _
  rw [show c = 0 + c from by ring, show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (drain_c c 0 2 (e + 3))
  ring_nf; finish

-- End case r=1: (3, 1, c, 0, e) ⊢* (0, 0, 0, 2*c+4, e+3*c+5)
theorem end_r1 : ⟨3, 1, c, 0, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * c + 4, e + 3 * c + 5⟩ := by
  step fm; step fm; step fm
  show ⟨0, 0, c + 1, 2, e + 2⟩ [fm]⊢* _
  rw [show c + 1 = 0 + (c + 1) from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (drain_c (c + 1) 0 1 (e + 2))
  ring_nf; finish

-- End case r=2: (3, 2, c, 0, e) ⊢* (0, 0, 0, 2*c+5, e+3*c+7)
theorem end_r2 : ⟨3, 2, c, 0, e⟩ [fm]⊢* ⟨0, 0, 0, 2 * c + 5, e + 3 * c + 7⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm; step fm; step fm
  show ⟨0, 0, c + 2, 1, e + 1⟩ [fm]⊢* _
  rw [show c + 2 = 0 + (c + 2) from by ring, show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (drain_c (c + 2) 0 0 (e + 1))
  ring_nf; finish

-- End case r=3: (3, 3, c, 0, e+1) ⊢* (0, 0, 0, 2*c+8, e+3*c+10)
theorem end_r3 : ⟨3, 3, c, 0, e + 1⟩ [fm]⊢* ⟨0, 0, 0, 2 * c + 8, e + 3 * c + 10⟩ := by
  rw [show (3 : ℕ) = 1 + 1 + 1 from by ring]
  step fm; step fm; step fm; step fm; step fm
  show ⟨0, 0, c + 3, 2, e + 1⟩ [fm]⊢* _
  rw [show c + 3 = 0 + (c + 3) from by ring, show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (drain_c (c + 3) 0 1 (e + 1))
  ring_nf; finish

-- Full transition for d%4=0
theorem trans_r0 : ⟨0, 0, 0, 4 * n + 1, e + 4 * n + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * n + 3, e + 12 * n + 3⟩ := by
  rw [show 4 * n + 1 = 0 + (4 * n + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (4 * n + 1))
  simp only [Nat.zero_add]
  rw [show 4 * n + 1 = (4 * n) + 1 from by ring,
      show e + 4 * n + 1 = (e + 4 * n) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus opening
  rw [show e + 4 * n = (e + 3 * n) + n from by ring,
      show (4 * n : ℕ) = 0 + 4 * n from by ring]
  apply stepStar_trans (spiral_chain n (b := 0) (c := 0) (e := e + 3 * n))
  simp only [Nat.zero_add]
  apply stepStar_trans (end_r0 (c := 3 * n) (e := e + 3 * n))
  ring_nf; finish

-- Full transition for d%4=1
theorem trans_r1 : ⟨0, 0, 0, 4 * n + 2, e + 4 * n + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * n + 4, e + 12 * n + 6⟩ := by
  rw [show 4 * n + 2 = 0 + (4 * n + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (4 * n + 2))
  simp only [Nat.zero_add]
  rw [show 4 * n + 2 = (4 * n + 1) + 1 from by ring,
      show e + 4 * n + 2 = (e + 4 * n + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus opening
  rw [show e + 4 * n + 1 = (e + 3 * n + 1) + n from by ring,
      show 4 * n + 1 = 1 + 4 * n from by ring]
  apply stepStar_trans (spiral_chain n (b := 1) (c := 0) (e := e + 3 * n + 1))
  simp only [Nat.zero_add]
  apply stepStar_trans (end_r1 (c := 3 * n) (e := e + 3 * n + 1))
  ring_nf; finish

-- Full transition for d%4=2
theorem trans_r2 : ⟨0, 0, 0, 4 * n + 3, e + 4 * n + 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * n + 5, e + 12 * n + 9⟩ := by
  rw [show 4 * n + 3 = 0 + (4 * n + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (4 * n + 3))
  simp only [Nat.zero_add]
  rw [show 4 * n + 3 = (4 * n + 2) + 1 from by ring,
      show e + 4 * n + 3 = (e + 4 * n + 2) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus opening
  rw [show e + 4 * n + 2 = (e + 3 * n + 2) + n from by ring,
      show 4 * n + 2 = 2 + 4 * n from by ring]
  apply stepStar_trans (spiral_chain n (b := 2) (c := 0) (e := e + 3 * n + 2))
  simp only [Nat.zero_add]
  apply stepStar_trans (end_r2 (c := 3 * n) (e := e + 3 * n + 2))
  ring_nf; finish

-- Full transition for d%4=3
theorem trans_r3 : ⟨0, 0, 0, 4 * n + 4, e + 4 * n + 4⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * n + 8, e + 12 * n + 12⟩ := by
  rw [show 4 * n + 4 = 0 + (4 * n + 4) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (4 * n + 4))
  simp only [Nat.zero_add]
  rw [show 4 * n + 4 = (4 * n + 3) + 1 from by ring,
      show e + 4 * n + 4 = (e + 4 * n + 3) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus opening
  rw [show e + 4 * n + 3 = (e + 3 * n + 3) + n from by ring,
      show 4 * n + 3 = 3 + 4 * n from by ring]
  apply stepStar_trans (spiral_chain n (b := 3) (c := 0) (e := e + 3 * n + 3))
  simp only [Nat.zero_add]
  rw [show e + 3 * n + 3 = (e + 3 * n + 2) + 1 from by ring]
  apply stepStar_trans (end_r3 (c := 3 * n) (e := e + 3 * n + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d + 1, e + 1⟩ ∧ e ≥ d)
  · intro c ⟨d, e, hq, he⟩; subst hq
    obtain ⟨n, rfl | rfl | rfl | rfl⟩ : ∃ n, d = 4 * n ∨ d = 4 * n + 1 ∨ d = 4 * n + 2 ∨ d = 4 * n + 3 :=
      ⟨d / 4, by omega⟩
    · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 4 * n := ⟨e - 4 * n, by omega⟩
      exact ⟨⟨0, 0, 0, 6 * n + 3, e' + 12 * n + 3⟩,
        ⟨6 * n + 2, e' + 12 * n + 2, rfl, by omega⟩, trans_r0⟩
    · obtain ⟨e', rfl⟩ : ∃ e', e = e' + (4 * n + 1) := ⟨e - (4 * n + 1), by omega⟩
      exact ⟨⟨0, 0, 0, 6 * n + 4, e' + 12 * n + 6⟩,
        ⟨6 * n + 3, e' + 12 * n + 5, rfl, by omega⟩, trans_r1⟩
    · obtain ⟨e', rfl⟩ : ∃ e', e = e' + (4 * n + 2) := ⟨e - (4 * n + 2), by omega⟩
      exact ⟨⟨0, 0, 0, 6 * n + 5, e' + 12 * n + 9⟩,
        ⟨6 * n + 4, e' + 12 * n + 8, rfl, by omega⟩, trans_r2⟩
    · obtain ⟨e', rfl⟩ : ∃ e', e = e' + (4 * n + 3) := ⟨e - (4 * n + 3), by omega⟩
      exact ⟨⟨0, 0, 0, 6 * n + 8, e' + 12 * n + 12⟩,
        ⟨6 * n + 7, e' + 12 * n + 11, rfl, by omega⟩, trans_r3⟩
  · exact ⟨0, 0, rfl, by omega⟩
