import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1187: [5/6, 49/2, 44/35, 9/11, 6/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  1
 0  2  0  0 -1
 1  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1187

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R1R1R3: one round (2, b+2, k, b+k+2, k+1) →3→ (2, b, k+1, b+k+1, k+2)
-- Induction on b (even steps b = 2m → 0).
theorem r1r1r3_chain : ∀ m, ∀ k, ⟨2, 2 * m + 2, k, 2 * m + k + 2, k + 1⟩ [fm]⊢*
    ⟨2, 0, k + m + 1, k + m + 1, k + m + 2⟩ := by
  intro m; induction' m with m ih <;> intro k
  · -- m=0: (2, 2, k, k+2, k+1). Need d = k+2 = (k+1)+1 for R3.
    step fm; step fm; step fm; ring_nf; finish
  · -- m+1: (2, 2m+4, k, 2m+k+4, k+1)
    -- After R1: (1, 2m+3, k+1, 2m+k+4, k+1)
    -- After R1: (0, 2m+2, k+2, 2m+k+4, k+1)
    -- After R3: (2, 2m+2, k+1, 2m+k+3, k+2)
    -- = (2, 2*(m+1), k+1, 2*(m+1)+(k+1), (k+1)+1) ← matches ih (k+1)
    -- But Lean normalizes 2*(m+1)+2 as 2*m+2+1+1 via Nat.succ.
    -- Actually the succ case has goal with 2*(m+1)+2 and 2*(m+1)+k+2.
    -- Let's use omega to convert.
    have h1 : 2 * (m + 1) + 2 = (2 * m + 2) + 1 + 1 := by omega
    have h2 : 2 * (m + 1) + k + 2 = (2 * m + k + 2) + 1 + 1 := by omega
    rw [h1, h2]
    step fm; step fm
    have h3 : 2 * m + k + 2 + 1 = 2 * m + (k + 1) + 2 := by omega
    have h4 : k + 1 + 1 = (k + 1) + 1 := by omega
    rw [h3, h4]
    step fm
    apply stepStar_trans (ih (k + 1))
    ring_nf; finish

-- R2R2R3 chain: (2, 0, c, d, e) →* (2, 0, 0, d + 3*c, e + c)
theorem r2r2r3_chain : ∀ c d e, ⟨2, 0, c, d, e⟩ [fm]⊢* ⟨2, 0, 0, d + 3 * c, e + c⟩ := by
  intro c; induction' c with c ih <;> intro d e
  · exists 0
  · step fm; step fm; step fm
    apply stepStar_trans (ih (d + 3) (e + 1))
    ring_nf; finish

-- R4 chain: (0, b, 0, d, k) →* (0, b + 2*k, 0, d, 0)
theorem r4_chain : ∀ k b d, ⟨0, b, 0, d, k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 2) d)
    ring_nf; finish

-- n=0: (0, 0, 0, 2, 0) →⁺ (0, 2, 0, 4, 0)
theorem trans_zero : ⟨0, 0, 0, 2, 0⟩ [fm]⊢⁺ ⟨0, 2, 0, 4, 0⟩ := by
  execute fm 6

-- Main transition: (0, 2*(n+1), 0, 2*(n+1)+2, 0) →⁺ (0, 4*n+6, 0, 4*n+8, 0)
theorem main_trans : ∀ n, ⟨0, 2 * (n + 1), 0, 2 * (n + 1) + 2, 0⟩ [fm]⊢⁺
    ⟨0, 4 * n + 6, 0, 4 * n + 8, 0⟩ := by
  intro n
  -- R5
  have h1 : 2 * (n + 1) + 2 = (2 * (n + 1) + 1) + 1 := by omega
  rw [h1]
  step fm
  -- (1, 2n+3, 0, 2n+3, 0). R1.
  have h2 : 2 * (n + 1) + 1 = (2 * n + 2) + 1 := by omega
  rw [h2]
  step fm
  -- (0, 2n+2, 1, 2n+3, 0). R3.
  have h3 : 2 * n + 2 + 1 = (2 * n + 2) + 1 := by omega
  rw [h3]
  step fm
  -- (2, 2n+2, 0, 2n+2, 1). Apply r1r1r3_chain with m=n, k=0.
  -- Need: (2, 2*n+2, 0, 2*n+0+2, 0+1)
  rw [show (2 * n + 2 : ℕ) = 2 * n + 0 + 2 from by omega,
      show (1 : ℕ) = 0 + 1 from by omega]
  apply stepStar_trans (r1r1r3_chain n 0)
  -- (2, 0, n+1, n+1, n+2)
  rw [show 0 + n + 1 = n + 1 from by omega,
      show 0 + n + 2 = n + 2 from by omega]
  -- r2r2r3_chain
  apply stepStar_trans (r2r2r3_chain (n + 1) (n + 1) (n + 2))
  -- (2, 0, 0, 4n+4, 2n+3)
  have h5 : n + 1 + 3 * (n + 1) = 4 * n + 4 := by omega
  have h6 : n + 2 + (n + 1) = 2 * n + 3 := by omega
  rw [h5, h6]
  -- R2, R2
  step fm; step fm
  have h7 : 4 * n + 4 + 2 + 2 = 4 * n + 8 := by omega
  rw [h7]
  -- r4_chain
  apply stepStar_trans (r4_chain (2 * n + 3) 0 (4 * n + 8))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 2 * n, 0, 2 * n + 2, 0⟩) 0
  intro n
  rcases n with _ | n
  · exact ⟨1, trans_zero⟩
  · refine ⟨2 * n + 3, ?_⟩
    rw [show 2 * (2 * n + 3) = 4 * n + 6 from by ring,
        show 4 * n + 6 + 2 = 4 * n + 8 from by ring]
    exact main_trans n

end Sz22_2003_unofficial_1187
