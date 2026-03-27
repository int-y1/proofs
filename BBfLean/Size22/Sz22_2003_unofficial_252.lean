import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #252: [14/15, 1/154, 63/2, 77/3, 10/7]

Vector representation:
```
 1 -1 -1  1  0
-1  0  0 -1 -1
-1  2  0  1  0
 0 -1  0  1  1
 1  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_252

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R4 chain: converts b to d and e
theorem r4_chain : ∀ k, ∀ b d e,
    ⟨0, b+k, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d+k, e+k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    have hs : fm ⟨0, (b + k) + 1, 0, d, e⟩ = some ⟨0, b + k, 0, d + 1, e + 1⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar hs)
    have := ih b (d + 1) (e + 1)
    rw [show d + 1 + k = d + (k + 1) from by ring,
        show e + 1 + k = e + (k + 1) from by ring] at this
    exact this

-- R5/R2 alternating: each pair does d-=2, e-=1, c+=1
theorem r5r2_chain : ∀ k, ∀ c d,
    ⟨0, 0, c, d+2*k, k⟩ [fm]⊢* ⟨0, 0, c+k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · simp; exists 0
  · rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    have hs1 : fm ⟨0, 0, c, (d + 2 * k) + 2, k + 1⟩ =
        some ⟨1, 0, c + 1, d + 2 * k + 1, k + 1⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar hs1)
    have hs2 : fm ⟨1, 0, c + 1, d + 2 * k + 1, k + 1⟩ =
        some ⟨0, 0, c + 1, d + 2 * k, k⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar hs2)
    have := ih (c + 1) d
    rw [show c + 1 + k = c + (k + 1) from by ring] at this
    exact this

-- R3/R1/R1 chain: each triple does a+=1, c-=2, d+=3
theorem r3r1r1_chain : ∀ k, ∀ a c d,
    ⟨a+1, 0, c+2*k, d, 0⟩ [fm]⊢* ⟨a+k+1, 0, c, d+3*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · simp; exists 0
  · rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring]
    apply stepStar_trans (ih a (c + 2) d)
    rw [show a + k + 1 = (a + k) + 1 from by ring]
    have hs1 : fm ⟨(a + k) + 1, 0, c + 2, d + 3 * k, 0⟩ =
        some ⟨a + k, 2, c + 2, d + 3 * k + 1, 0⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar hs1)
    have hs2 : fm ⟨a + k, 2, c + 2, d + 3 * k + 1, 0⟩ =
        some ⟨a + k + 1, 1, c + 1, d + 3 * k + 2, 0⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar hs2)
    have hs3 : fm ⟨a + k + 1, 1, c + 1, d + 3 * k + 2, 0⟩ =
        some ⟨a + k + 2, 0, c, d + 3 * k + 3, 0⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar hs3)
    rw [show a + k + 2 = a + (k + 1) + 1 from by ring,
        show d + 3 * k + 3 = d + 3 * (k + 1) from by ring]
    finish

-- Handle c=1 tail: R3/R1/R3
theorem c1_tail (a d : ℕ) : ⟨a+1, 0, 1, d, 0⟩ [fm]⊢* ⟨a, 3, 0, d+3, 0⟩ := by
  have hs1 : fm ⟨a + 1, 0, 1, d, 0⟩ = some ⟨a, 2, 1, d + 1, 0⟩ := by simp [fm]
  apply stepStar_trans (step_stepStar hs1)
  have hs2 : fm ⟨a, 2, 1, d + 1, 0⟩ = some ⟨a + 1, 1, 0, d + 2, 0⟩ := by simp [fm]
  apply stepStar_trans (step_stepStar hs2)
  have hs3 : fm ⟨a + 1, 1, 0, d + 2, 0⟩ = some ⟨a, 3, 0, d + 3, 0⟩ := by simp [fm]
  exact step_stepStar hs3

-- R3 chain: converts a to b
theorem r3_chain : ∀ k, ∀ a b d,
    ⟨a+k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b+2*k, 0, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · simp; exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    have hs : fm ⟨(a + k) + 1, b, 0, d, 0⟩ = some ⟨a + k, b + 2, 0, d + 1, 0⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar hs)
    have := ih a (b + 2) (d + 1)
    rw [show b + 2 + 2 * k = b + 2 * (k + 1) from by ring,
        show d + 1 + k = d + (k + 1) from by ring] at this
    exact this

-- Phase 3 init: (0, 0, c+1, d+1, 0) ⊢⁺ (2, 0, c, d+3, 0)
theorem phase3_init (c d : ℕ) : ⟨0, 0, c+1, d+1, 0⟩ [fm]⊢⁺ ⟨2, 0, c, d+3, 0⟩ := by
  have hs1 : fm ⟨0, 0, c + 1, d + 1, 0⟩ = some ⟨1, 0, c + 2, d, 0⟩ := by simp [fm]
  have hs2 : fm ⟨1, 0, c + 2, d, 0⟩ = some ⟨0, 2, c + 2, d + 1, 0⟩ := by simp [fm]
  have hs3 : fm ⟨0, 2, c + 2, d + 1, 0⟩ = some ⟨1, 1, c + 1, d + 2, 0⟩ := by simp [fm]
  have hs4 : fm ⟨1, 1, c + 1, d + 2, 0⟩ = some ⟨2, 0, c, d + 3, 0⟩ := by simp [fm]
  exact ⟨4, by omega, by
    show stepNat fm 4 ⟨0, 0, c + 1, d + 1, 0⟩ = some ⟨2, 0, c, d + 3, 0⟩
    simp [stepNat, Nat.repeat, Option.bind, hs1, hs2, hs3, hs4]⟩

-- Main transition for even b: (0, 2*m+2, 0, d+2*m+3, 0) ⊢⁺ (0, 2*m+5, 0, d+4*m+7, 0)
theorem main_trans_even (m d : ℕ) :
    ⟨0, 2*m+2, 0, d+2*m+3, 0⟩ [fm]⊢⁺ ⟨0, 2*m+5, 0, d+4*m+7, 0⟩ := by
  -- Phase 1: R4 chain, 2m+2 steps
  rw [show 2 * m + 2 = 0 + (2 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * m + 2) 0 (d + 2 * m + 3) 0)
  simp only [Nat.zero_add]
  -- Now at (0, 0, 0, d+4m+5, 2m+2)
  -- Phase 2: R5/R2 chain, 2m+2 pairs
  rw [show d + 2 * m + 3 + (2 * m + 2) = (d + 1) + 2 * (2 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r5r2_chain (2 * m + 2) 0 (d + 1))
  simp only [Nat.zero_add]
  -- Now at (0, 0, 2m+2, d+1, 0)
  -- Phase 3 init: (0, 0, (2m+1)+1, d+1, 0) -> (2, 0, 2m+1, d+3, 0)
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (phase3_init (2 * m + 1) d)
  -- Now at (2, 0, 2m+1, d+3, 0)
  have h1 : ⟨2, 0, 2*m+1, d+3, 0⟩ [fm]⊢* ⟨m+2, 0, 1, d+3+3*m, 0⟩ := by
    have := r3r1r1_chain m 1 1 (d + 3)
    rw [show 1 + 2 * m = 2 * m + 1 from by ring,
        show 1 + m + 1 = m + 2 from by ring,
        show 1 + 1 = 2 from rfl] at this
    exact this
  apply stepStar_trans h1
  -- c1_tail: (m+2, 0, 1, d+3+3m, 0) -> (m+1, 3, 0, d+3m+6, 0)
  rw [show m + 2 = (m + 1) + 1 from by ring]
  apply stepStar_trans (c1_tail (m + 1) (d + 3 + 3 * m))
  -- r3_chain (m+1): (m+1, 3, 0, d+3m+6, 0) -> (0, 2m+5, 0, d+4m+7, 0)
  rw [show (m + 1 : ℕ) = 0 + (m + 1) from by ring]
  apply stepStar_trans (r3_chain (m + 1) 0 3 (d + 3 + 3 * m + 3))
  rw [show 3 + 2 * (m + 1) = 2 * m + 5 from by ring,
      show d + 3 + 3 * m + 3 + (m + 1) = d + 4 * m + 7 from by ring]
  finish

-- Main transition for odd b: (0, 2*m+3, 0, d+2*m+4, 0) ⊢⁺ (0, 2*m+6, 0, d+4*m+9, 0)
theorem main_trans_odd (m d : ℕ) :
    ⟨0, 2*m+3, 0, d+2*m+4, 0⟩ [fm]⊢⁺ ⟨0, 2*m+6, 0, d+4*m+9, 0⟩ := by
  -- Phase 1: R4 chain, 2m+3 steps
  rw [show 2 * m + 3 = 0 + (2 * m + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * m + 3) 0 (d + 2 * m + 4) 0)
  simp only [Nat.zero_add]
  -- Phase 2: R5/R2 chain
  rw [show d + 2 * m + 4 + (2 * m + 3) = (d + 1) + 2 * (2 * m + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (r5r2_chain (2 * m + 3) 0 (d + 1))
  simp only [Nat.zero_add]
  -- Now at (0, 0, 2m+3, d+1, 0)
  -- Phase 3 init: (0, 0, (2m+2)+1, d+1, 0) -> (2, 0, 2m+2, d+3, 0)
  rw [show 2 * m + 3 = (2 * m + 2) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (phase3_init (2 * m + 2) d)
  -- Now at (2, 0, 2m+2, d+3, 0)
  have h1 : ⟨2, 0, 2*m+2, d+3, 0⟩ [fm]⊢* ⟨m+3, 0, 0, d+3+3*(m+1), 0⟩ := by
    have := r3r1r1_chain (m + 1) 1 0 (d + 3)
    rw [show 0 + 2 * (m + 1) = 2 * m + 2 from by ring,
        show 1 + (m + 1) + 1 = m + 3 from by ring,
        show 1 + 1 = 2 from rfl] at this
    exact this
  apply stepStar_trans h1
  -- r3_chain (m+3): (m+3, 0, 0, d+3+3*(m+1), 0) -> (0, 2m+6, 0, d+4m+9, 0)
  rw [show m + 3 = 0 + (m + 3) from by ring]
  apply stepStar_trans (r3_chain (m + 3) 0 0 (d + 3 + 3 * (m + 1)))
  simp only [Nat.zero_add]
  rw [show 2 * (m + 3) = 2 * m + 6 from by ring,
      show d + 3 + 3 * (m + 1) + (m + 3) = d + 4 * m + 9 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 5, 0, 7, 0⟩) (by execute fm 25)
  -- Use ℕ × ℕ × Bool as index: (n, d, parity) where
  -- C(n, d, false) = (0, 2n+2, 0, d+2n+3, 0)  (even b = 2n+2)
  -- C(n, d, true)  = (0, 2n+3, 0, d+2n+4, 0)  (odd b = 2n+3)
  -- Initial state (0, 5, 0, 7, 0) = (0, 2*1+3, 0, 1+2*1+4, 0) = C(1, 1, true)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × Bool)
    (fun ⟨n, d, p⟩ ↦ if p then ⟨0, 2*n+3, 0, d+2*n+4, 0⟩ else ⟨0, 2*n+2, 0, d+2*n+3, 0⟩)
    ⟨1, 1, true⟩
  intro ⟨n, d, p⟩
  rcases p with _ | _
  · -- even case: C(n, d, false) = (0, 2n+2, 0, d+2n+3, 0) -> (0, 2n+5, 0, d+4n+7, 0)
    -- = (0, 2(n+1)+3, 0, (d+2n+3)+(2(n+1)+4)-...) hmm, need to match C(n+1, d', true)
    -- (0, 2n+5, 0, d+4n+7, 0) = (0, 2*(n+1)+3, 0, d'+2*(n+1)+4, 0) where d' = d+4n+7-2n-6 = d+2n+1
    exact ⟨⟨n+1, d+2*n+1, true⟩, by
      show ⟨0, 2*n+2, 0, d+2*n+3, 0⟩ [fm]⊢⁺
        ⟨0, 2*(n+1)+3, 0, (d+2*n+1)+2*(n+1)+4, 0⟩
      rw [show 2 * (n + 1) + 3 = 2 * n + 5 from by ring,
          show (d + 2 * n + 1) + 2 * (n + 1) + 4 = d + 4 * n + 7 from by ring]
      exact main_trans_even n d⟩
  · -- odd case: C(n, d, true) = (0, 2n+3, 0, d+2n+4, 0) -> (0, 2n+6, 0, d+4n+9, 0)
    -- = (0, 2*(n+2), 0, d'+2*(n+2)+3, 0) where d' = d+4n+9-2n-7 = d+2n+2
    -- Wait: 2*(n+2) = 2n+4, but we need 2n+6. Hmm.
    -- 2n+6 = 2*(n+2)+2, even. So C(n+2, d', false) = (0, 2*(n+2)+2, 0, d'+2*(n+2)+3, 0)
    -- d' = d+4n+9 - 2*(n+2) - 3 = d+4n+9 - 2n - 7 = d+2n+2
    exact ⟨⟨n+2, d+2*n+2, false⟩, by
      show ⟨0, 2*n+3, 0, d+2*n+4, 0⟩ [fm]⊢⁺
        ⟨0, 2*(n+2)+2, 0, (d+2*n+2)+2*(n+2)+3, 0⟩
      rw [show 2 * (n + 2) + 2 = 2 * n + 6 from by ring,
          show (d + 2 * n + 2) + 2 * (n + 2) + 3 = d + 4 * n + 9 from by ring]
      exact main_trans_odd n d⟩

end Sz22_2003_unofficial_252
