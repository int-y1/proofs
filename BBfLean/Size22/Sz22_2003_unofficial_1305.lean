import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1305: [63/10, 121/2, 4/33, 5/7, 15/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  0  2
 2 -1  0  0 -1
 0  0  1 -1  0
 0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1305

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 chain: transfer d to c.
theorem d_to_c : ∀ k c, ⟨0, 0, c, k, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro c; exists 0
  · intro c; step fm
    apply stepStar_trans (ih (c + 1)); ring_nf; finish

-- R3,R2,R2 chain: drain b, net e += 3 per round.
theorem r3r2r2_chain : ∀ k d e, ⟨0, k, 0, d, e + k⟩ [fm]⊢* ⟨0, 0, 0, d, e + 4 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show e + k + 2 + 2 = (e + 4) + k from by ring]
    apply stepStar_trans (ih d (e + 4))
    ring_nf; finish

-- Consume c (even): R1,R1,R3 rounds drain c by 2 each.
theorem consume_even : ∀ k b d f, ⟨2, b, 2 * k, d, f + k⟩ [fm]⊢* ⟨0, b + 3 * k, 0, d + 2 * k, f + 4⟩ := by
  intro k; induction' k with k ih <;> intro b d f
  · step fm; step fm; ring_nf; finish
  · rw [show 2 * (k + 1) = (2 * k) + 1 + 1 from by ring,
        show f + (k + 1) = (f + k) + 1 from by ring]
    step fm; step fm
    rw [show b + 2 + 2 = (b + 3) + 1 from by ring,
        show d + 1 + 1 = d + 2 from by ring]
    step fm
    apply stepStar_trans (ih (b + 3) (d + 2) f)
    ring_nf; finish

-- Consume c (odd): same rounds, last iteration is R1,R2.
theorem consume_odd : ∀ k b d f, ⟨2, b, 2 * k + 1, d, f + k⟩ [fm]⊢* ⟨0, b + 3 * k + 2, 0, d + 2 * k + 1, f + 2⟩ := by
  intro k; induction' k with k ih <;> intro b d f
  · step fm; step fm; ring_nf; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring,
        show f + (k + 1) = (f + k) + 1 from by ring]
    step fm; step fm
    rw [show b + 2 + 2 = (b + 3) + 1 from by ring,
        show d + 1 + 1 = d + 2 from by ring]
    step fm
    apply stepStar_trans (ih (b + 3) (d + 2) f)
    ring_nf; finish

-- Odd n case.
theorem main_odd (k : ℕ) :
    ⟨0, 0, 2 * k + 1, 0, 2 * (2 * k + 2) ^ 2⟩ [fm]⊢⁺
    ⟨0, 0, 2 * k + 2, 0, 2 * (2 * k + 3) ^ 2⟩ := by
  rw [show 2 * (2 * k + 2) ^ 2 = (8 * k ^ 2 + 15 * k + 6) + (k + 1) + 1 from by ring]
  step fm
  rw [show 8 * k ^ 2 + 15 * k + 6 + (k + 1) = (8 * k ^ 2 + 15 * k + 5) + (k + 1) + 1 from by ring]
  step fm
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) from by ring]
  apply stepStar_trans (consume_even (k + 1) 0 0 (8 * k ^ 2 + 15 * k + 5))
  rw [show 0 + 3 * (k + 1) = 3 * k + 3 from by ring,
      show 0 + 2 * (k + 1) = 2 * k + 2 from by ring,
      show 8 * k ^ 2 + 15 * k + 5 + 4 = (8 * k ^ 2 + 12 * k + 6) + (3 * k + 3) from by ring]
  apply stepStar_trans (r3r2r2_chain (3 * k + 3) (2 * k + 2) (8 * k ^ 2 + 12 * k + 6))
  rw [show 8 * k ^ 2 + 12 * k + 6 + 4 * (3 * k + 3) = 2 * (2 * k + 3) ^ 2 from by ring]
  apply stepStar_trans (d_to_c (2 * k + 2) 0 (e := 2 * (2 * k + 3) ^ 2))
  ring_nf; finish

-- Even n case.
theorem main_even (k : ℕ) :
    ⟨0, 0, 2 * k + 2, 0, 2 * (2 * k + 3) ^ 2⟩ [fm]⊢⁺
    ⟨0, 0, 2 * k + 3, 0, 2 * (2 * k + 4) ^ 2⟩ := by
  rw [show 2 * (2 * k + 3) ^ 2 = (8 * k ^ 2 + 23 * k + 16) + (k + 1) + 1 from by ring]
  step fm
  rw [show 8 * k ^ 2 + 23 * k + 16 + (k + 1) = (8 * k ^ 2 + 23 * k + 15) + (k + 1) + 1 from by ring]
  step fm
  rw [show 2 * k + 2 + 1 = 2 * (k + 1) + 1 from by ring]
  apply stepStar_trans (consume_odd (k + 1) 0 0 (8 * k ^ 2 + 23 * k + 15))
  rw [show 0 + 3 * (k + 1) + 2 = 3 * k + 5 from by ring,
      show 0 + 2 * (k + 1) + 1 = 2 * k + 3 from by ring,
      show 8 * k ^ 2 + 23 * k + 15 + 2 = (8 * k ^ 2 + 20 * k + 12) + (3 * k + 5) from by ring]
  apply stepStar_trans (r3r2r2_chain (3 * k + 5) (2 * k + 3) (8 * k ^ 2 + 20 * k + 12))
  rw [show 8 * k ^ 2 + 20 * k + 12 + 4 * (3 * k + 5) = 2 * (2 * k + 4) ^ 2 from by ring]
  apply stepStar_trans (d_to_c (2 * k + 3) 0 (e := 2 * (2 * k + 4) ^ 2))
  ring_nf; finish

-- Combined transition with parity dispatch.
theorem main_trans (n : ℕ) :
    ⟨0, 0, n + 1, 0, 2 * (n + 2) ^ 2⟩ [fm]⊢⁺ ⟨0, 0, n + 2, 0, 2 * (n + 3) ^ 2⟩ := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    exact main_odd k
  · subst hk
    rw [show 2 * k + 1 + 1 = 2 * k + 2 from by ring,
        show 2 * k + 1 + 2 = 2 * k + 3 from by ring,
        show 2 * k + 1 + 3 = 2 * k + 4 from by ring]
    exact main_even k

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 8⟩)
  · execute fm 12
  · rw [show (8 : ℕ) = 2 * (0 + 2) ^ 2 from by norm_num]
    apply progress_nonhalt_simple (fm := fm) (A := ℕ)
      (fun n ↦ ⟨0, 0, n + 1, 0, 2 * (n + 2) ^ 2⟩) 0
    intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1305
