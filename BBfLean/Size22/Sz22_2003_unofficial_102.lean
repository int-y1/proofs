import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #102: [1/30, 4/77, 63/2, 5/7, 242/5]

Vector representation:
```
-1 -1 -1  0  0
 2  0  0 -1 -1
-1  2  0  1  0
 0  0  1 -1  0
 1  0 -1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_102

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

-- R4 repeated: convert d to c
theorem d_to_c : ∀ k, ∀ b c d, ⟨0, b, c, d+k, 0⟩ [fm]⊢* ⟨0, b, c+k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R5/R1 chain: alternating R5 and R1
-- Each iteration: R5 then R1 (consuming 1 from b and 2 from c, producing 2 to e)
-- Final: one R5 (consuming last c, producing 2 to e and 1 to a)
theorem r5r1_chain : ∀ k, ∀ b e, ⟨0, b+k, 2*k+1, 0, e⟩ [fm]⊢* ⟨1, b, 0, 0, e+2*k+2⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · step fm; ring_nf; finish
  -- Need to massage into form for step
  have hc : 2 * (k + 1) + 1 = (2 * k + 2) + 1 := by ring
  have hb : b + (k + 1) = (b + k) + 1 := by ring
  rw [hc, hb]
  step fm -- R5: (1, (b+k)+1, 2*k+2, 0, e+2) -- but with c+1 pattern matching
  -- After R5, we have: (1, b+k+1, 2*k+2, 0, e+2)
  -- Now R1 fires since a≥1, b≥1 (b+k+1≥1), c≥1 (2*k+2≥1)
  -- R1: (0, b+k, 2*k+1, 0, e+2)
  have hc2 : 2 * k + 2 = (2 * k + 1) + 1 := by ring
  rw [hc2]
  step fm -- R1
  apply stepStar_trans (ih b (e + 2))
  ring_nf; finish

-- R3/R2 chain: alternating R3 and R2
-- Each pair: (A+1, B, 0, 0, E+1) → R3 → (A, B+2, 0, 1, E+1) → R2 → (A+2, B+2, 0, 0, E)
-- Do step first then IH
theorem r3r2_chain : ∀ k, ∀ a b e, ⟨a+1, b, 0, 0, e+k⟩ [fm]⊢* ⟨a+1+k, b+2*k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  -- (a+1, b, 0, 0, (e+k)+1)
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  -- R3: a+1 ≥ 1, so R3 fires: (a, b+2, 0, 1, (e+k)+1)
  step fm
  -- R2: d=1≥1, e=(e+k)+1≥1, so R2 fires: (a+2, b+2, 0, 0, e+k)
  step fm
  -- Now at (a+2, b+2, 0, 0, e+k) = ((a+1)+1, b+2, 0, 0, e+k)
  apply stepStar_trans (ih (a + 1) (b + 2) e)
  ring_nf; finish

-- R3 drain: convert a to b and d (when c=0, e=0)
theorem a_drain : ∀ k, ∀ a b d, ⟨a+k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b+2*k, 0, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [← Nat.add_assoc]
  step fm -- R3: (a+k, b+2, 0, d+1, 0)
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Main transition: (0, b+n+2, 0, 2n+1, 0) →⁺ (0, b+8n+12, 0, 2n+3, 0)
theorem main_trans (n b : ℕ) :
    ⟨0, b+n+2, 0, 2*n+1, 0⟩ [fm]⊢⁺ ⟨0, b+8*n+12, 0, 2*n+3, 0⟩ := by
  -- Phase 1: d_to_c: →* (0, b+n+2, 2n+1, 0, 0)
  apply stepStar_stepPlus_stepPlus
  · have h := d_to_c (2*n+1) (b+n+2) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: r5r1_chain: →* (1, b+2, 0, 0, 2n+2)
  apply stepStar_stepPlus_stepPlus
  · have h := r5r1_chain n (b+2) 0
    simp only [Nat.zero_add, show (b + 2) + n = b + n + 2 from by ring] at h
    exact h
  -- R3: (1, b+2, 0, 0, 2n+2) → (0, b+4, 0, 1, 2n+2)
  step fm
  -- R2: (0, b+4, 0, 1, 2n+2) → (2, b+4, 0, 0, 2n+1)
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
  step fm
  -- Phase 3: r3r2_chain: (2, b+4, 0, 0, 2n+1) →* (2n+3, b+4n+6, 0, 0, 0)
  apply stepStar_trans
  · have h := r3r2_chain (2*n+1) 1 (b+4) 0
    simp only [Nat.zero_add,
               show 1 + 1 + (2 * n + 1) = 2 * n + 3 from by ring,
               show (b + 4) + 2 * (2 * n + 1) = b + 4 * n + 6 from by ring] at h
    exact h
  -- Phase 4: a_drain: (2n+3, b+4n+6, 0, 0, 0) →* (0, b+8n+12, 0, 2n+3, 0)
  have h := a_drain (2*n+3) 0 (b+4*n+6) 0
  simp only [Nat.zero_add,
             show (b + 4 * n + 6) + 2 * (2 * n + 3) = b + 8 * n + 12 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 2, 0, 1, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, b⟩ ↦ ⟨0, b+n+2, 0, 2*n+1, 0⟩) ⟨0, 0⟩
  intro ⟨n, b⟩
  refine ⟨⟨n+1, b+7*n+9⟩, ?_⟩
  show ⟨0, b+n+2, 0, 2*n+1, 0⟩ [fm]⊢⁺ ⟨0, (b+7*n+9)+(n+1)+2, 0, 2*(n+1)+1, 0⟩
  simp only [show (b + 7 * n + 9) + (n + 1) + 2 = b + 8 * n + 12 from by ring,
             show 2 * (n + 1) + 1 = 2 * n + 3 from by ring]
  exact main_trans n b

end Sz22_2003_unofficial_102
