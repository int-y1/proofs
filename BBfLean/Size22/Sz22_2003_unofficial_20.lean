import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #20: [1/135, 98/15, 3/7, 125/2, 3/5]

Vector representation:
```
 0 -3 -1  0
 1 -1 -1  2
 0  1  0 -1
-1  0  3  0
 0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_20

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+3, c+1, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+1, b, c, d+2⟩
  | ⟨a, b, c, d+1⟩ => some ⟨a, b+1, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+3, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- R3 repeated: d to b
theorem d_to_b : ∀ k, ∀ a b, ⟨a, b, 0, d + k⟩ [fm]⊢* ⟨a, b + k, 0, d⟩ := by
  intro k; induction' k with k h <;> intro a b
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _); ring_nf; finish

-- R4 repeated: a to c
theorem a_to_c : ∀ k, ∀ a c, ⟨a + k, 0, c, 0⟩ [fm]⊢* ⟨a, 0, c + 3 * k, 0⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _); ring_nf; finish

-- R3+R2 interleaved chain
theorem r3r2_chain : ∀ k, ∀ a d, ⟨a, 0, k, d + 1⟩ [fm]⊢* ⟨a + k, 0, 0, d + k + 1⟩ := by
  intro k; induction' k with k h <;> intro a d
  · exists 0
  step fm; step fm
  apply stepStar_trans (h (a + 1) (d + 1))
  ring_nf; finish

-- Drain chain: R4+R1+R1+R1 repeated
theorem drain_chain : ∀ k, ∀ a b, ⟨a + k, b + 9 * k, 0, 0⟩ [fm]⊢* ⟨a, b, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a b
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show b + 9 * (k + 1) = (b + 9 * k) + 9 from by ring]
  step fm; step fm; step fm; step fm
  exact h a b

-- Terminal b=8: (a+1, 8, 0, 0) ⊢* (a, 0, 2, 0)
theorem end_b8 (a : ℕ) : ⟨a + 1, 8, 0, 0⟩ [fm]⊢* ⟨a, 0, 2, 0⟩ := by
  execute fm 8

-- Terminal b=5: (a+1, 5, 0, 0) ⊢* (a+2, 0, 2, 0)
theorem end_b5 (a : ℕ) : ⟨a + 1, 5, 0, 0⟩ [fm]⊢* ⟨a + 2, 0, 2, 0⟩ := by
  execute fm 18

-- Terminal b=2: (a+1, 2, 0, 0) ⊢* (a+4, 0, 2, 0)
theorem end_b2 (a : ℕ) : ⟨a + 1, 2, 0, 0⟩ [fm]⊢* ⟨a + 4, 0, 2, 0⟩ := by
  execute fm 28

-- Main transition for c mod 9 = 2: (0, 0, 9k+2, 0) ⊢⁺ (0, 0, 24k+14, 0)
theorem trans_mod0 (k : ℕ) : ⟨0, 0, 9 * k + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 24 * k + 14, 0⟩ := by
  rw [show 9 * k + 2 = 9 * k + 0 + 2 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, (9 * k + 0 + 1) + 1, 0⟩ = some ⟨0, 1, 9 * k + 0 + 1, 0⟩; simp [fm]
  apply stepStar_trans
  · show ⟨0, 1, 9 * k + 0 + 1, 0⟩ [fm]⊢* ⟨1, 0, 9 * k + 0, 2⟩
    step fm; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨9 * k + 1, 0, 0, 9 * k + 2⟩)
  · convert r3r2_chain (9 * k + 0) 1 1 using 2; ring_nf
  apply stepStar_trans (c₂ := ⟨9 * k + 1, 9 * k + 2, 0, 0⟩)
  · have h := @d_to_b (d := 0) (9 * k + 2) (9 * k + 1) 0
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_trans (c₂ := ⟨8 * k + 1, 2, 0, 0⟩)
  · have h := drain_chain k (8 * k + 1) 2
    rw [show (8 * k + 1) + k = 9 * k + 1 from by ring,
        show 2 + 9 * k = 9 * k + 2 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨8 * k + 4, 0, 2, 0⟩)
  · rw [show 8 * k + 1 = (8 * k + 0) + 1 from by ring]
    have h := end_b2 (8 * k + 0)
    rw [show 8 * k + 0 + 4 = 8 * k + 4 from by ring] at h; exact h
  have h := a_to_c (8 * k + 4) 0 2
  simp only [Nat.zero_add] at h
  rw [show 2 + 3 * (8 * k + 4) = 24 * k + 14 from by ring] at h; exact h

-- Main transition for c mod 9 = 5: (0, 0, 9k+5, 0) ⊢⁺ (0, 0, 24k+17, 0)
theorem trans_mod1 (k : ℕ) : ⟨0, 0, 9 * k + 5, 0⟩ [fm]⊢⁺ ⟨0, 0, 24 * k + 17, 0⟩ := by
  rw [show 9 * k + 5 = (9 * k + 3) + 2 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, ((9 * k + 3) + 1) + 1, 0⟩ = some ⟨0, 1, (9 * k + 3) + 1, 0⟩; simp [fm]
  apply stepStar_trans
  · show ⟨0, 1, 9 * k + 3 + 1, 0⟩ [fm]⊢* ⟨1, 0, 9 * k + 3, 2⟩
    step fm; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨9 * k + 4, 0, 0, 9 * k + 5⟩)
  · convert r3r2_chain (9 * k + 3) 1 1 using 2; ring_nf
  apply stepStar_trans (c₂ := ⟨9 * k + 4, 9 * k + 5, 0, 0⟩)
  · have h := @d_to_b (d := 0) (9 * k + 5) (9 * k + 4) 0
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_trans (c₂ := ⟨8 * k + 4, 5, 0, 0⟩)
  · have h := drain_chain k (8 * k + 4) 5
    rw [show (8 * k + 4) + k = 9 * k + 4 from by ring,
        show 5 + 9 * k = 9 * k + 5 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨8 * k + 5, 0, 2, 0⟩)
  · rw [show 8 * k + 4 = (8 * k + 3) + 1 from by ring]
    have h := end_b5 (8 * k + 3)
    rw [show 8 * k + 3 + 2 = 8 * k + 5 from by ring] at h; exact h
  have h := a_to_c (8 * k + 5) 0 2
  simp only [Nat.zero_add] at h
  rw [show 2 + 3 * (8 * k + 5) = 24 * k + 17 from by ring] at h; exact h

-- Main transition for c mod 9 = 8: (0, 0, 9k+8, 0) ⊢⁺ (0, 0, 24k+20, 0)
theorem trans_mod2 (k : ℕ) : ⟨0, 0, 9 * k + 8, 0⟩ [fm]⊢⁺ ⟨0, 0, 24 * k + 20, 0⟩ := by
  rw [show 9 * k + 8 = (9 * k + 6) + 2 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, ((9 * k + 6) + 1) + 1, 0⟩ = some ⟨0, 1, (9 * k + 6) + 1, 0⟩; simp [fm]
  apply stepStar_trans
  · show ⟨0, 1, 9 * k + 6 + 1, 0⟩ [fm]⊢* ⟨1, 0, 9 * k + 6, 2⟩
    step fm; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨9 * k + 7, 0, 0, 9 * k + 8⟩)
  · convert r3r2_chain (9 * k + 6) 1 1 using 2; ring_nf
  apply stepStar_trans (c₂ := ⟨9 * k + 7, 9 * k + 8, 0, 0⟩)
  · have h := @d_to_b (d := 0) (9 * k + 8) (9 * k + 7) 0
    simp only [Nat.zero_add] at h; exact h
  apply stepStar_trans (c₂ := ⟨8 * k + 7, 8, 0, 0⟩)
  · have h := drain_chain k (8 * k + 7) 8
    rw [show (8 * k + 7) + k = 9 * k + 7 from by ring,
        show 8 + 9 * k = 9 * k + 8 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨8 * k + 6, 0, 2, 0⟩)
  · rw [show 8 * k + 7 = (8 * k + 6) + 1 from by ring]
    exact end_b8 (8 * k + 6)
  have h := a_to_c (8 * k + 6) 0 2
  simp only [Nat.zero_add] at h
  rw [show 2 + 3 * (8 * k + 6) = 24 * k + 20 from by ring] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 5, 0⟩) (by execute fm 11)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨0, 0, 3 * n + 2, 0⟩)
  · intro q ⟨n, hq⟩; subst hq
    rcases (show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 from by omega) with h | h | h
    · obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m := ⟨n / 3, by omega⟩
      exact ⟨⟨0, 0, 24 * m + 14, 0⟩, ⟨8 * m + 4, by ring_nf⟩, by rw [show 3 * (3 * m) + 2 = 9 * m + 2 from by ring]; exact trans_mod0 m⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m + 1 := ⟨n / 3, by omega⟩
      exact ⟨⟨0, 0, 24 * m + 17, 0⟩, ⟨8 * m + 5, by ring_nf⟩, by rw [show 3 * (3 * m + 1) + 2 = 9 * m + 5 from by ring]; exact trans_mod1 m⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m + 2 := ⟨n / 3, by omega⟩
      exact ⟨⟨0, 0, 24 * m + 20, 0⟩, ⟨8 * m + 6, by ring_nf⟩, by rw [show 3 * (3 * m + 2) + 2 = 9 * m + 8 from by ring]; exact trans_mod2 m⟩
  · exact ⟨1, by ring_nf⟩

end Sz22_2003_unofficial_20
