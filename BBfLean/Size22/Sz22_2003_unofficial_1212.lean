import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1212: [5/6, 539/2, 4/55, 9/11, 22/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1  0 -1
 0  2  0  0 -1
 1  0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1212

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- R4 chain: (0, b, 0, d, e+k) →* (0, b+2k, 0, d, e)
theorem e_to_b : ∀ k b d e, ⟨(0 : ℕ), b, (0 : ℕ), d, e + k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) d e)
    ring_nf; finish

-- Middle phase round: R5, R1, R3, R1, R1
-- (0, b+3, c, d+1, 0) →* (0, b, c+2, d, 0)
theorem middle_round : ⟨(0 : ℕ), b + 3, c, d + 1, (0 : ℕ)⟩ [fm]⊢* ⟨0, b, c + 2, d, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; finish

-- Middle phase chain: k rounds
theorem middle_chain : ∀ k b c d, ⟨(0 : ℕ), b + 3 * k, c, d + k, (0 : ℕ)⟩ [fm]⊢* ⟨0, b, c + 2 * k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show b + 3 * (k + 1) = (b + 3) + 3 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 3) c (d + 1))
    apply stepStar_trans (middle_round (b := b) (c := c + 2 * k) (d := d))
    rw [show c + 2 * k + 2 = c + 2 * (k + 1) from by ring]; exists 0

-- R3R2R2 chain: (0, 0, c+k, d, e+1) →* (0, 0, c, d+4k, e+k+1)
theorem r3r2r2_chain : ∀ k c d e, ⟨(0 : ℕ), (0 : ℕ), c + k, d, e + 1⟩ [fm]⊢* ⟨0, 0, c, d + 4 * k, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + 1 = e + 1 from rfl]
    step fm; step fm; step fm
    apply stepStar_trans (ih c (d + 4) (e + 1))
    ring_nf; finish

-- Tail r=0: (0, 0, c, d+1, 0) →⁺ (0, 0, 0, d+4c+2, c+2)
theorem tail_b0 (c d : ℕ) : ⟨(0 : ℕ), (0 : ℕ), c, d + 1, (0 : ℕ)⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 4 * c + 2, c + 2⟩ := by
  step fm; step fm
  rw [show c = 0 + c from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain c 0 (d + 2) 1)
  ring_nf; finish

-- Tail r=1: (0, 1, c, d+1, 0) →⁺ (0, 0, 0, d+4c+4, c+2)
theorem tail_b1 (c d : ℕ) : ⟨(0 : ℕ), (1 : ℕ), c, d + 1, (0 : ℕ)⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 4 * c + 4, c + 2⟩ := by
  step fm; step fm
  rw [show c + 1 = 0 + (c + 1) from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (c + 1) 0 d 0)
  ring_nf; finish

-- Tail r=2: (0, 2, c, d+1, 0) →⁺ (0, 0, 0, d+4c+6, c+2)
theorem tail_b2 (c d : ℕ) : ⟨(0 : ℕ), (2 : ℕ), c, d + 1, (0 : ℕ)⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 4 * c + 6, c + 2⟩ := by
  step fm; step fm; step fm; step fm; step fm
  rw [show c + 1 = 0 + (c + 1) from by ring,
      show d + 2 = d + 2 from rfl,
      show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (c + 1) 0 (d + 2) 0)
  ring_nf; finish

-- Transition for E%3=1: E = 3m+1, K = 2m
-- (0,0,0, G+2m+1, 3m+1) ⊢⁺ (0,0,0, G+16m+6, 4m+2)
theorem trans_mod1 (m G : ℕ) :
    ⟨(0 : ℕ), 0, 0, G + 2 * m + 1, 3 * m + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, G + 16 * m + 6, 4 * m + 2⟩ := by
  rw [show (3 : ℕ) * m + 1 = 0 + (3 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (3 * m + 1) 0 (G + 2 * m + 1) 0)
  rw [show 0 + 2 * (3 * m + 1) = 2 + 3 * (2 * m) from by ring,
      show G + 2 * m + 1 = G + 1 + 2 * m from by ring]
  apply stepStar_stepPlus_stepPlus (middle_chain (2 * m) 2 0 (G + 1))
  rw [show 0 + 2 * (2 * m) = 4 * m from by ring,
      show G + 1 = G + 0 + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (tail_b2 (4 * m) (G + 0))
  ring_nf; finish

-- Transition for E%3=2: E = 3m+2, K = 2m+1
-- (0,0,0, G+2m+2, 3m+2) ⊢⁺ (0,0,0, G+16m+12, 4m+4)
theorem trans_mod2 (m G : ℕ) :
    ⟨(0 : ℕ), 0, 0, G + 2 * m + 2, 3 * m + 2⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, G + 16 * m + 12, 4 * m + 4⟩ := by
  rw [show (3 : ℕ) * m + 2 = 0 + (3 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (3 * m + 2) 0 (G + 2 * m + 2) 0)
  rw [show 0 + 2 * (3 * m + 2) = 1 + 3 * (2 * m + 1) from by ring,
      show G + 2 * m + 2 = G + 1 + (2 * m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (middle_chain (2 * m + 1) 1 0 (G + 1))
  rw [show 0 + 2 * (2 * m + 1) = 4 * m + 2 from by ring,
      show G + 1 = G + 0 + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (tail_b1 (4 * m + 2) (G + 0))
  ring_nf; finish

-- Transition for E%3=0: E = 3(m+1), K = 2(m+1)
-- (0,0,0, G+2m+3, 3m+3) ⊢⁺ (0,0,0, G+16m+18, 4m+6)
theorem trans_mod0 (m G : ℕ) :
    ⟨(0 : ℕ), 0, 0, G + 2 * m + 3, 3 * m + 3⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, G + 16 * m + 18, 4 * m + 6⟩ := by
  rw [show (3 : ℕ) * m + 3 = 0 + (3 * m + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (3 * m + 3) 0 (G + 2 * m + 3) 0)
  rw [show 0 + 2 * (3 * m + 3) = 0 + 3 * (2 * m + 2) from by ring,
      show G + 2 * m + 3 = G + 1 + (2 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (middle_chain (2 * m + 2) 0 0 (G + 1))
  rw [show 0 + 2 * (2 * m + 2) = 4 * m + 4 from by ring,
      show G + 1 = G + 0 + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (tail_b0 (4 * m + 4) (G + 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D, E⟩ ∧ D ≥ E + 1 ∧ E ≥ 1)
  · intro q ⟨D, E, hq, hD, hE⟩; subst hq
    rcases (show E % 3 = 0 ∨ E % 3 = 1 ∨ E % 3 = 2 from by omega) with h | h | h
    · obtain ⟨m3, hm3⟩ : ∃ m3, E = 3 * m3 := ⟨E / 3, by omega⟩
      obtain ⟨m, rfl⟩ : ∃ m, m3 = m + 1 := ⟨m3 - 1, by omega⟩
      subst hm3
      obtain ⟨G, rfl⟩ : ∃ G, D = G + 2 * m + 3 := ⟨D - 2 * m - 3, by omega⟩
      exact ⟨⟨0, 0, 0, G + 16 * m + 18, 4 * m + 6⟩,
        ⟨G + 16 * m + 18, 4 * m + 6, rfl, by omega, by omega⟩,
        trans_mod0 m G⟩
    · obtain ⟨m, hm⟩ : ∃ m, E = 3 * m + 1 := ⟨E / 3, by omega⟩
      subst hm
      obtain ⟨G, rfl⟩ : ∃ G, D = G + 2 * m + 1 := ⟨D - 2 * m - 1, by omega⟩
      exact ⟨⟨0, 0, 0, G + 16 * m + 6, 4 * m + 2⟩,
        ⟨G + 16 * m + 6, 4 * m + 2, rfl, by omega, by omega⟩,
        trans_mod1 m G⟩
    · obtain ⟨m, hm⟩ : ∃ m, E = 3 * m + 2 := ⟨E / 3, by omega⟩
      subst hm
      obtain ⟨G, rfl⟩ : ∃ G, D = G + 2 * m + 2 := ⟨D - 2 * m - 2, by omega⟩
      exact ⟨⟨0, 0, 0, G + 16 * m + 12, 4 * m + 4⟩,
        ⟨G + 16 * m + 12, 4 * m + 4, rfl, by omega, by omega⟩,
        trans_mod2 m G⟩
  · exact ⟨2, 1, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1212
