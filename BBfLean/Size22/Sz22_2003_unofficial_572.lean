import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #572: [35/6, 11/2, 4/55, 3/7, 12/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  1
 2  0 -1  0 -1
 0  1  0 -1  0
 2  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_572

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- R3R2R2 chain: convert c to e
theorem r3r2r2_chain : ∀ k c e, ⟨0, 0, c+k, d, e+1⟩ [fm]⊢* ⟨0, 0, c, d, e+k+1⟩ := by
  intro k; induction' k with k h <;> intro c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R1R1R3 chain with b=0
theorem r1r1r3_b0 : ∀ k c d e, ⟨2, 2*k, c, d, e+k⟩ [fm]⊢* ⟨2, 0, c+k, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show 2 * (k + 1) = 2 * k + 2 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R1R1R3 chain with b=1
theorem r1r1r3_b1 : ∀ k c d e, ⟨2, 1+2*k, c, d, e+k⟩ [fm]⊢* ⟨2, 1, c+k, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show 1 + 2 * (k + 1) = (1 + 2 * k) + 2 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Combined b=0 phase: R1R1R3 + R2R2 + R3R2R2
theorem phase_b0 : ⟨2, 2*(K+1), 0, 0, K+(K+1)⟩ [fm]⊢* ⟨0, 0, 0, 2*(K+1), 2*K+3⟩ := by
  apply stepStar_trans (r1r1r3_b0 (K+1) 0 0 K)
  step fm; step fm
  apply stepStar_trans (r3r2r2_chain (d := 0+2*(K+1)) (K+1) 0 (K+1))
  ring_nf; finish

-- Combined b=1 phase: R1R1R3 + R1 + R2 + R3R2R2
theorem phase_b1 : ⟨2, 1+2*(K+1), 0, 0, (K+1)+(K+1)⟩ [fm]⊢* ⟨0, 0, 0, 2*(K+1)+1, 2*K+4⟩ := by
  apply stepStar_trans (r1r1r3_b1 (K+1) 0 0 (K+1))
  step fm; step fm
  rw [show 0+(K+1)+1 = 0+(K+2) from by ring]
  apply stepStar_trans (r3r2r2_chain (d := 0+2*(K+1)+1) (K+2) 0 (K+1))
  ring_nf; finish

-- Even n transition: n = K+K
theorem even_trans : ⟨0, 0, 0, K+K+1, K+K+2⟩ [fm]⊢⁺ ⟨0, 0, 0, K+K+2, K+K+3⟩ := by
  rw [show K+K+1 = 0 + (K+K+1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (d := 0) (e := K+K+2) _ 0)
  rw [show (0 : ℕ) + (K+K+1) = K+K+1 from by ring]
  step fm
  rw [show K+K+2 = 2*(K+1) from by ring,
      show K+K+1 = K + (K+1) from by ring]
  apply stepStar_trans phase_b0
  ring_nf; finish

-- Odd n transition: n = 2*K+1
theorem odd_trans : ⟨0, 0, 0, 2*K+2, 2*K+3⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*K+3, 2*K+4⟩ := by
  rw [show 2*K+2 = 0 + (2*K+2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (d := 0) (e := 2*K+3) _ 0)
  rw [show (0 : ℕ) + (2*K+2) = 2*K+2 from by ring]
  step fm
  rw [show 2*K+3 = 1+2*(K+1) from by ring,
      show 2*K+2 = (K+1) + (K+1) from by ring]
  apply stepStar_trans phase_b1
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩)
  · execute fm 7
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n+1, n+2⟩) 0
  intro n
  rcases Nat.even_or_odd n with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- n even: n = K + K
    subst hK
    exists K+K+1
    rw [show K+K+1+1 = K+K+2 from by ring,
        show K+K+1+2 = K+K+3 from by ring]
    exact even_trans
  · -- n odd: n = 2*K + 1
    subst hK
    exists 2*K+2
    rw [show 2*K+1+1 = 2*K+2 from by ring,
        show 2*K+1+2 = 2*K+3 from by ring,
        show (2*K+2)+1 = 2*K+3 from by ring,
        show (2*K+2)+2 = 2*K+4 from by ring]
    exact odd_trans
