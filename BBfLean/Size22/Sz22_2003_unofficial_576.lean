import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #576: [35/6, 11/2, 4/55, 3/7, 28/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  1
 2  0 -1  0 -1
 0  1  0 -1  0
 2  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_576

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [show d + (k + 1) = d + k + 1 from by ring]
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- R1R1R3 chain
theorem r1r1r3_chain : ∀ k b c d, ⟨2, b+2*k, c, d, e+k⟩ [fm]⊢* ⟨2, b, c+k, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro b c d
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R2R2R3 drain
theorem r2r2r3_drain : ∀ k c d e, ⟨2, 0, c+k, d, e⟩ [fm]⊢* ⟨2, 0, c, d, e+k⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Even chain+drain: (2, 2*m, 0, 1, 2*m) ⊢⁺ (1, 0, 0, 2*m+1, 2*m+1)
theorem even_middle (m : ℕ) : ⟨2, 2*m, 0, 1, 2*m⟩ [fm]⊢⁺ ⟨1, 0, 0, 2*m+1, 2*m+1⟩ := by
  have h1 : ⟨2, 2*m, 0, 1, 2*m⟩ [fm]⊢* ⟨2, 0, m, 2*m+1, m⟩ := by
    convert @r1r1r3_chain m m 0 0 1 using 2
    all_goals ring_nf
  apply stepStar_stepPlus_stepPlus h1
  have h2 : ⟨2, 0, m, 2*m+1, m⟩ [fm]⊢* ⟨2, 0, 0, 2*m+1, 2*m⟩ := by
    convert @r2r2r3_drain m 0 (2*m+1) m using 2
    all_goals ring_nf
  apply stepStar_stepPlus_stepPlus h2
  step fm; ring_nf; finish

-- Odd chain+drain: (2, 2*m+1, 0, 1, 2*m+1) ⊢⁺ (1, 0, 0, 2*m+2, 2*m+2)
theorem odd_middle (m : ℕ) : ⟨2, 2*m+1, 0, 1, 2*m+1⟩ [fm]⊢⁺ ⟨1, 0, 0, 2*m+2, 2*m+2⟩ := by
  have h1 : ⟨2, 2*m+1, 0, 1, 2*m+1⟩ [fm]⊢* ⟨2, 1, m, 2*m+1, m+1⟩ := by
    convert @r1r1r3_chain (m+1) m 1 0 1 using 2
    all_goals ring_nf
  apply stepStar_stepPlus_stepPlus h1
  -- R1, R2, R3
  step fm; step fm
  rw [show (2:ℕ) * m + 1 + 1 = 2 * m + 2 from by ring]
  step fm
  -- State: (2, 0, m, 2*m+2, m+1) ⊢⁺ (1, 0, 0, 2*m+2, 2*m+2)
  have hd : ⟨2, 0, m, 2*m+2, m+1⟩ [fm]⊢* ⟨2, 0, 0, 2*m+2, 2*m+1⟩ := by
    convert @r2r2r3_drain m 0 (2*m+2) (m+1) using 2
    all_goals ring_nf
  apply stepStar_trans hd
  step fm; ring_nf; finish

-- Full cycle: (1, 0, 0, n+1, n+1) →⁺ (1, 0, 0, n+2, n+2)
theorem full_cycle : ⟨1, 0, 0, n+1, n+1⟩ [fm]⊢⁺ ⟨1, 0, 0, n+2, n+2⟩ := by
  -- R2
  step fm
  -- R4 chain
  have h_d2b : ⟨0, 0, 0, n+1, n+1+1⟩ [fm]⊢* ⟨0, n+1, 0, 0, n+1+1⟩ := by
    convert @d_to_b 0 (n+1+1) (n+1) 0 using 2
    all_goals ring_nf
  apply stepStar_trans h_d2b
  -- R5
  step fm
  -- Parity split
  rcases Nat.even_or_odd (n + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- EVEN: n+1 = m+m
    rw [show m + m = 2 * m from by ring] at hm
    rw [hm]
    apply stepStar_trans (stepPlus_stepStar (even_middle m))
    have : n + 2 = 2 * m + 1 := by omega
    rw [this]; finish
  · -- ODD: n+1 = 2*m+1
    rw [hm]
    apply stepStar_trans (stepPlus_stepStar (odd_middle m))
    have : n + 2 = 2 * m + 2 := by omega
    rw [this]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 1, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨1, 0, 0, n+1, n+1⟩) 0
  intro n; exists n+1; exact full_cycle

end Sz22_2003_unofficial_576
