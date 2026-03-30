import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #660: [35/6, 1573/2, 4/65, 3/7, 15/11]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  2  1
 2  0 -1  0  0 -1
 0  1  0 -1  0  0
 0  1  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_660

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+2, f+1⟩
  | ⟨a, b, c+1, d, e, f+1⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

-- R4 chain: (0, b, 0, d+k, e, f) →* (0, b+k, 0, d, e, f)
theorem d_to_b : ∀ k b d, ⟨(0 : ℕ), b, 0, d + k, e, f⟩ [fm]⊢* ⟨(0 : ℕ), b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [Nat.add_succ d k]; step fm
    apply stepStar_trans (ih (b + 1) d); ring_nf; finish

-- R1x2,R3 chain: (2, b+2k, c, D, e, f+k) →* (2, b, c+k, D+2k, e, f)
theorem r1r1r3_chain : ∀ k b c D f,
    ⟨(2 : ℕ), b + 2 * k, c, D, e, f + k⟩ [fm]⊢* ⟨(2 : ℕ), b, c + k, D + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b c D f
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c D (f + 1))
    step fm; step fm; step fm; ring_nf; finish

-- R3,R2,R2 drain: (0, 0, c+k, D, e, f+k) →* (0, 0, c, D, e+4k, f+2k)
theorem r3r2r2_chain : ∀ k c e f,
    ⟨(0 : ℕ), 0, c + k, D, e, f + k⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, D, e + 4 * k, f + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · exists 0
  · rw [show c + (k + 1) = (c + 1) + k from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    apply stepStar_trans (ih (c + 1) e (f + 1))
    rw [show f + 1 + 2 * k = (f + 2 * k) + 1 from by ring]
    step fm; step fm; step fm; ring_nf; finish

-- R4 ⊢⁺: at least one R4 step
theorem d_to_b_plus : ∀ k b d,
    ⟨(0 : ℕ), b, 0, d + k + 1, e, f⟩ [fm]⊢⁺ ⟨(0 : ℕ), b + k + 1, 0, d, e, f⟩ := by
  intro k b d; step fm
  apply stepStar_trans (d_to_b k (b + 1) d); ring_nf; finish

-- Odd transition: (0,0,0,2k+1,4k²+12k+7,2k+2) →⁺ (0,0,0,2k+2,4k²+16k+14,2k+3)
theorem trans_odd (k : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * k + 1, 4 * k ^ 2 + 12 * k + 7, 2 * k + 2⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, 2 * k + 2, 4 * k ^ 2 + 16 * k + 14, 2 * k + 3⟩ := by
  -- R4 x (2k+1) → ⊢⁺
  rw [show (2 * k + 1 : ℕ) = 0 + 2 * k + 1 from by ring]
  apply stepPlus_stepStar_stepPlus
    (d_to_b_plus (2 * k) 0 0 (e := 4 * k ^ 2 + 12 * k + 7) (f := 2 * k + 2))
  rw [show 0 + 2 * k + 1 = 2 * k + 1 from by ring]
  -- now: (0, 2k+1, 0, 0, E, 2k+2) ⊢* target
  -- R5 + R3 + R1R1R3 chain + R2x2 + R3R2R2 drain
  -- R5: needs (e+1) pattern. E = 4k²+12k+7.
  -- R3: needs (c+1, f+1) pattern.
  -- Use rw to expose the +1 patterns, then step fm.
  rw [show (4 * k ^ 2 + 12 * k + 7 : ℕ) = (4 * k ^ 2 + 12 * k + 6) + 1 from by ring]
  apply stepStar_trans (by step fm; finish :
    ⟨(0 : ℕ), 2 * k + 1, 0, 0, (4 * k ^ 2 + 12 * k + 6) + 1, 2 * k + 2⟩ [fm]⊢*
    ⟨(0 : ℕ), 2 * k + 2, 1, 0, 4 * k ^ 2 + 12 * k + 6, 2 * k + 2⟩)
  -- R3: needs c+1=1 and f+1. f = 2k+2 = (2k+1)+1
  rw [show (2 * k + 2 : ℕ) = (2 * k + 1) + 1 from by ring]
  apply stepStar_trans (by step fm; finish :
    ⟨(0 : ℕ), 2 * k + 2, 1, 0, 4 * k ^ 2 + 12 * k + 6, (2 * k + 1) + 1⟩ [fm]⊢*
    ⟨(2 : ℕ), 2 * k + 2, 0, 0, 4 * k ^ 2 + 12 * k + 6, 2 * k + 1⟩)
  -- R1R1R3 chain (k+1 rounds)
  rw [show (2 * k + 2 : ℕ) = 0 + 2 * (k + 1) from by ring,
      show (2 * k + 1 : ℕ) = k + (k + 1) from by omega]
  apply stepStar_trans (r1r1r3_chain (k + 1) 0 0 0 k (e := 4 * k ^ 2 + 12 * k + 6))
  rw [show 0 + (k + 1) = k + 1 from by ring,
      show 0 + 2 * (k + 1) = 2 * k + 2 from by ring]
  -- R2 x 2: (2, 0, k+1, 2k+2, E, k) → (0, 0, k+1, 2k+2, E+4, k+2)
  apply stepStar_trans (by step fm; step fm; ring_nf; finish :
    ⟨(2 : ℕ), 0, k + 1, 2 * k + 2, 4 * k ^ 2 + 12 * k + 6, k⟩ [fm]⊢*
    ⟨(0 : ℕ), 0, k + 1, 2 * k + 2, 4 * k ^ 2 + 12 * k + 10, k + 2⟩)
  -- R3R2R2 drain (k+1 rounds)
  rw [show (k + 1 : ℕ) = 0 + (k + 1) from by ring,
      show (k + 2 : ℕ) = 1 + (k + 1) from by omega]
  apply stepStar_trans (r3r2r2_chain (k + 1) 0 (4 * k ^ 2 + 12 * k + 10) 1 (D := 2 * k + 2))
  ring_nf; finish

-- Even transition: (0,0,0,2k+2,4k²+16k+14,2k+3) →⁺ (0,0,0,2k+3,4k²+20k+23,2k+4)
theorem trans_even (k : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * k + 2, 4 * k ^ 2 + 16 * k + 14, 2 * k + 3⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, 2 * k + 3, 4 * k ^ 2 + 20 * k + 23, 2 * k + 4⟩ := by
  -- R4 x (2k+2) → ⊢⁺
  rw [show (2 * k + 2 : ℕ) = 0 + (2 * k + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus
    (d_to_b_plus (2 * k + 1) 0 0 (e := 4 * k ^ 2 + 16 * k + 14) (f := 2 * k + 3))
  rw [show 0 + (2 * k + 1) + 1 = 2 * k + 2 from by ring]
  -- now: (0, 2k+2, 0, 0, E, 2k+3) ⊢* target
  -- R5
  rw [show (4 * k ^ 2 + 16 * k + 14 : ℕ) = (4 * k ^ 2 + 16 * k + 13) + 1 from by ring]
  apply stepStar_trans (by step fm; finish :
    ⟨(0 : ℕ), 2 * k + 2, 0, 0, (4 * k ^ 2 + 16 * k + 13) + 1, 2 * k + 3⟩ [fm]⊢*
    ⟨(0 : ℕ), 2 * k + 3, 1, 0, 4 * k ^ 2 + 16 * k + 13, 2 * k + 3⟩)
  -- R3
  rw [show (2 * k + 3 : ℕ) = (2 * k + 2) + 1 from by ring]
  apply stepStar_trans (by step fm; finish :
    ⟨(0 : ℕ), (2 * k + 2) + 1, 1, 0, 4 * k ^ 2 + 16 * k + 13, (2 * k + 2) + 1⟩ [fm]⊢*
    ⟨(2 : ℕ), (2 * k + 2) + 1, 0, 0, 4 * k ^ 2 + 16 * k + 13, 2 * k + 2⟩)
  -- R1R1R3 chain (k+1 rounds)
  rw [show (2 * k + 2 + 1 : ℕ) = 1 + 2 * (k + 1) from by ring,
      show (2 * k + 2 : ℕ) = (k + 1) + (k + 1) from by omega]
  apply stepStar_trans (r1r1r3_chain (k + 1) 1 0 0 (k + 1) (e := 4 * k ^ 2 + 16 * k + 13))
  rw [show 0 + (k + 1) = k + 1 from by ring,
      show 0 + 2 * (k + 1) = 2 * k + 2 from by ring]
  -- R1 (a=2, b=1) + R2 (a=1, b=0): (2,1,k+1,2k+2,E,k+1) → (0,0,k+2,2k+3,E+2,k+2)
  apply stepStar_trans (by step fm; step fm; ring_nf; finish :
    ⟨(2 : ℕ), 1, k + 1, 2 * k + 2, 4 * k ^ 2 + 16 * k + 13, k + 1⟩ [fm]⊢*
    ⟨(0 : ℕ), 0, k + 2, 2 * k + 3, 4 * k ^ 2 + 16 * k + 15, k + 2⟩)
  -- R3R2R2 drain (k+2 rounds)
  rw [show (k + 2 : ℕ) = 0 + (k + 2) from by ring]
  apply stepStar_trans (r3r2r2_chain (k + 2) 0 (4 * k ^ 2 + 16 * k + 15) 0 (D := 2 * k + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 7, 2⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, n ≥ 1 ∧ q = ⟨0, 0, 0, n, n ^ 2 + 4 * n + 2, n + 1⟩)
  · intro c ⟨n, hn, hq⟩; subst hq
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [show k + k = 2 * k from by ring] at hk
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      subst hk
      refine ⟨⟨0, 0, 0, 2 * k + 3, (2 * k + 3) ^ 2 + 4 * (2 * k + 3) + 2, 2 * k + 4⟩,
        ⟨2 * k + 3, by omega, by ring_nf⟩, ?_⟩
      convert trans_even k using 1; ring_nf
    · subst hk
      refine ⟨⟨0, 0, 0, 2 * k + 2, (2 * k + 2) ^ 2 + 4 * (2 * k + 2) + 2, 2 * k + 3⟩,
        ⟨2 * k + 2, by omega, by ring_nf⟩, ?_⟩
      convert trans_odd k using 1; ring_nf
  · exact ⟨1, by omega, by ring_nf⟩
