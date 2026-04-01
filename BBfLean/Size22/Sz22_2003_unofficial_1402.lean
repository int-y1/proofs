import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1402: [7/15, 1/77, 54/7, 11/9, 175/2]

Vector representation:
```
 0 -1 -1  1  0
 0  0  0 -1 -1
 1  3  0 -1  0
 0 -2  0  0  1
-1  0  2  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1402

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+3, c, d, e⟩
  | ⟨a, b+2, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d+1, e⟩
  | _ => none

-- R1 chain: drain b and c into d
theorem r1_chain : ∀ k, ∀ a b c d, ⟨a, b + k, c + k, d, 0⟩ [fm]⊢* ⟨a, b, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c d
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a b c (d + 1)); ring_nf; finish

-- R3 chain: drain d, accumulate a and b
theorem r3_chain : ∀ k, ∀ a b d, ⟨a, b, 0, d + k, 0⟩ [fm]⊢* ⟨a + k, b + 3 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 1) (b + 3) d); ring_nf; finish

-- R4 chain: pair off b into e
theorem r4_chain : ∀ k, ∀ a b e, ⟨a, b + 2 * k, 0, 0, e⟩ [fm]⊢* ⟨a, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih a b (e + 1)); ring_nf; finish

-- R2 chain: drain d and e together
theorem r2_chain : ∀ k, ∀ a c d e, ⟨a, 0, c, d + k, e + k⟩ [fm]⊢* ⟨a, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a c d e); ring_nf; finish

-- R5+R2 chain: drain a while building c, ending with d=1
theorem r5_r2_chain : ∀ k, ∀ c, ⟨k + 1, 0, c, 0, k⟩ [fm]⊢* ⟨0, 0, c + 2 * k + 2, 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · step fm; ring_nf; finish
  · step fm; step fm
    apply stepStar_trans (ih (c + 2)); ring_nf; finish

-- General mixing: (a, 3, c, d, 0) ⊢* (a+c+d, 2c+3d+3, 0, 0, 0)
theorem mixing_gen : ∀ c, ∀ a d, ⟨a, 3, c, d, 0⟩ [fm]⊢* ⟨a + c + d, 2 * c + 3 * d + 3, 0, 0, 0⟩ := by
  intro c; induction' c using Nat.strongRecOn with c ih; intro a d
  rcases c with _ | _ | _ | c
  · rw [show d = 0 + d from by ring]
    apply stepStar_trans (r3_chain d a 3 0)
    ring_nf; finish
  · rw [show (3 : ℕ) = 2 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (r1_chain 1 a 2 0 d)
    rw [show d + 1 = 0 + (d + 1) from by ring]
    apply stepStar_trans (r3_chain (d + 1) a 2 0)
    ring_nf; finish
  · rw [show (3 : ℕ) = 1 + 2 from by ring, show (2 : ℕ) = 0 + 2 from by ring]
    apply stepStar_trans (r1_chain 2 a 1 0 d)
    rw [show d + 2 = 0 + (d + 2) from by ring]
    apply stepStar_trans (r3_chain (d + 2) a 1 0)
    ring_nf; finish
  · rw [show c + 1 + 1 + 1 = c + 3 from by omega,
        show (3 : ℕ) = 0 + 3 from by ring]
    apply stepStar_trans (r1_chain 3 a 0 c d)
    rw [show d + 3 = (d + 2) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c (by omega) (a + 1) (d + 2))
    ring_nf; finish

-- R5+R1+R2x2: opening of drain phase
theorem opening_drain (n : ℕ) :
    ⟨n + 2, 1, 0, 0, n + 2⟩ [fm]⊢* ⟨n + 1, 0, 1, 0, n⟩ := by
  step fm; step fm
  rw [show (2 : ℕ) = 0 + 2 from by ring]
  apply stepStar_trans (r2_chain 2 (n + 1) 1 0 n)
  ring_nf; finish

-- Main transition: (0, 0, n+2, 1, 0) ⊢⁺ (0, 0, 2n+5, 1, 0)
theorem main_trans (n : ℕ) :
    ⟨0, 0, n + 2, 1, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * n + 5, 1, 0⟩ := by
  step fm
  apply stepStar_trans (mixing_gen (n + 2) 1 0)
  rw [show 2 * (n + 2) + 3 * 0 + 3 = 1 + 2 * (n + 3) from by ring,
      show 1 + (n + 2) + 0 = n + 3 from by ring]
  apply stepStar_trans (r4_chain (n + 3) (n + 3) 1 0)
  rw [show (0 : ℕ) + (n + 3) = n + 3 from by ring,
      show n + 3 = (n + 1) + 2 from by ring]
  apply stepStar_trans (opening_drain (n + 1))
  rw [show n + 1 + 1 = n + 2 from by ring]
  apply stepStar_trans (r5_r2_chain (n + 1) 1)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 1, 0⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n + 2, 1, 0⟩) 0
  intro n; exact ⟨2 * n + 3, main_trans n⟩

end Sz22_2003_unofficial_1402
