import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1486: [7/15, 54/77, 11/3, 5/121, 21/2]

Vector representation:
```
 0 -1 -1  1  0
 1  3  0 -1 -1
 0 -1  0  0  1
 0  0  1  0 -2
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1486

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

theorem b_to_e : ∀ k, ∀ a e, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm
    apply stepStar_trans (ih a (e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ a c e, ⟨a, 0, c, 0, e + 2 * k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show e + 2 * (k + 1) = e + 2 * k + 2 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e)
    ring_nf; finish

theorem r5r1_chain : ∀ k, ∀ a c d, ⟨a + k, 0, c + k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a c (d + 2))
    ring_nf; finish

theorem r2r3_drain : ∀ D, ∀ a b, ⟨a, b, 0, D + 1, 1⟩ [fm]⊢* ⟨a + D + 1, b + 2 * (D + 1) + 1, 0, 0, 0⟩ := by
  intro D; induction' D with D ih <;> intro a b
  · step fm; ring_nf; finish
  · step fm; step fm
    apply stepStar_trans (ih (a + 1) (b + 2))
    ring_nf; finish

-- (F+1, 0, 0, 0, 7) ⊢⁺ (F+4, 0, 0, 0, 7)
theorem trans_k0 : ⟨F + 1, 0, 0, 0, 7⟩ [fm]⊢⁺ ⟨F + 4, 0, 0, 0, 7⟩ := by
  -- R4×3, R5, R1, R2, R1×2, R3: 9 explicit steps
  step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm; step fm
  -- now at (F+1, 0, 0, 3, 1) with ⊢* goal
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  apply stepStar_trans (r2r3_drain 2 (F + 1) 0)
  -- now at (F+4, 7, 0, 0, 0)
  rw [show F + 1 + 2 + 1 = F + 4 from by ring,
      show 0 + 2 * (2 + 1) + 1 = 7 from by ring]
  exact b_to_e 7 (F + 4) 0

-- (F+K'+2, 0, 0, 0, 2K'+9) ⊢⁺ (F+2K'+6, 0, 0, 0, 4K'+11)
theorem trans_k1 (F K' : ℕ) : (⟨F + K' + 2, 0, 0, 0, 2 * K' + 9⟩ : Q) [fm]⊢⁺ ⟨F + 2 * K' + 6, 0, 0, 0, 4 * K' + 11⟩ := by
  -- R4: 1 step, then chain the rest
  rw [show 2 * K' + 9 = 1 + 2 * (K' + 4) from by ring]
  step fm
  apply stepStar_trans
  · show ⟨F + K' + 2, 0, 1, 0, 1 + 2 * (K' + 3)⟩ [fm]⊢* ⟨F + K' + 2, 0, 1 + (K' + 3), 0, 1⟩
    exact r4_chain (K' + 3) (F + K' + 2) 1 1
  rw [show 1 + (K' + 3) = K' + 4 from by ring]
  -- (F+K'+2, 0, K'+4, 0, 1). R5, R1, R2, R1×3: 6 steps
  step fm; step fm; step fm; step fm; step fm; step fm
  -- (F+K'+2, 0, K', 4, 0)
  -- R5+R1 chain: K' pairs
  apply stepStar_trans
  · rw [show F + K' + 1 + 1 = (F + 2) + K' from by ring]
    have := r5r1_chain K' (F + 2) 0 4
    simp only [Nat.zero_add] at this
    exact this
  -- (F+2, 0, 0, 4+2K', 0). R5, R3
  rw [show 4 + 2 * K' = 2 * K' + 4 from by ring]
  step fm; step fm
  -- (F+1, 0, 0, 2K'+5, 1)
  rw [show 2 * K' + 4 + 1 = (2 * K' + 4) + 1 from by ring]
  apply stepStar_trans (r2r3_drain (2 * K' + 4) (F + 1) 0)
  rw [show F + 1 + (2 * K' + 4) + 1 = F + 2 * K' + 6 from by ring,
      show 0 + 2 * ((2 * K' + 4) + 1) + 1 = 4 * K' + 11 from by ring]
  have := b_to_e (4 * K' + 11) (F + 2 * K' + 6) 0
  simp only [Nat.zero_add] at this
  exact this

theorem main_trans (F K : ℕ) : (⟨F + K + 1, 0, 0, 0, 2 * K + 7⟩ : Q) [fm]⊢⁺ ⟨F + 2 * K + 4, 0, 0, 0, 4 * K + 7⟩ := by
  rcases K with _ | K'
  · exact trans_k0
  · rw [show F + (K' + 1) + 1 = F + K' + 2 from by ring,
        show 2 * (K' + 1) + 7 = 2 * K' + 9 from by ring,
        show F + 2 * (K' + 1) + 4 = F + 2 * K' + 6 from by ring,
        show 4 * (K' + 1) + 7 = 4 * K' + 11 from by ring]
    exact trans_k1 F K'

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := (⟨7, 0, 0, 0, 15⟩ : Q))
  · execute fm 72
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ (⟨p.1 + p.2 + 1, 0, 0, 0, 2 * p.2 + 7⟩ : Q)) ⟨2, 4⟩
  intro ⟨F, K⟩
  refine ⟨⟨F + 3, 2 * K⟩, ?_⟩
  show (F + K + 1, 0, 0, 0, 2 * K + 7) [fm]⊢⁺ (F + 3 + 2 * K + 1, 0, 0, 0, 2 * (2 * K) + 7)
  rw [show F + 3 + 2 * K + 1 = F + 2 * K + 4 from by ring,
      show 2 * (2 * K) + 7 = 4 * K + 7 from by ring]
  exact main_trans F K
