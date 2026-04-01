import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1388: [63/10, 8/33, 77/2, 5/7, 3/5]

Vector representation:
```
-1  2 -1  1  0
 3 -1  0  0 -1
-1  0  0  1  1
 0  0  1 -1  0
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1388

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R3 drain (b=0, c=0): each step a-=1, d+=1, e+=1
theorem r3_drain : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a d e; exists 0
  · intro a d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 1))
    ring_nf; finish

-- R4 transfer (a=0, b=0): each step d-=1, c+=1
theorem d_to_c : ∀ k c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih
  · intro c d e; exists 0
  · intro c d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    ring_nf; finish

-- R2+R1x3 chain: K rounds
theorem r2r1x3_chain : ∀ K B C D E,
    ⟨0, B + 1, C + 3 * K, D, E + K⟩ [fm]⊢* ⟨0, B + 5 * K + 1, C, D + 3 * K, E⟩ := by
  intro K; induction' K with K ih
  · intro B C D E; exists 0
  · intro B C D E
    rw [show C + 3 * (K + 1) = C + 3 * K + 3 from by ring,
        show E + (K + 1) = E + K + 1 from by ring]
    step fm; step fm; step fm; step fm
    apply stepStar_trans (ih (B + 5) C (D + 3) E)
    ring_nf; finish

-- R2 drain (c=0): each step a+=3, b-=1, e-=1
theorem r2_drain : ∀ k A B D, ⟨A, B + k, 0, D, k⟩ [fm]⊢* ⟨A + 3 * k, B, 0, D, 0⟩ := by
  intro k; induction' k with k ih
  · intro A B D; exists 0
  · intro A B D
    rw [show B + (k + 1) = (B + k) + 1 from by ring,
        show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (A + 3) B D)
    ring_nf; finish

-- R3+R2 drain: alternating R3 then R2, consuming b
theorem r3r2_drain : ∀ B A D,
    ⟨A + 1, B, 0, D, 0⟩ [fm]⊢* ⟨A + 1 + 2 * B, 0, 0, D + B, 0⟩ := by
  intro B; induction' B with B ih
  · intro A D; exists 0
  · intro A D
    rw [show (B + 1 : ℕ) = B + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (A + 2) (D + 1))
    ring_nf; finish

-- Main transition using K, p, r where a = K+p+2, d = r+1, p+r = 2K+3
-- so a+d = K+p+r+3 = K+2K+3+3 = 3K+6.
-- The chain uses K rounds, and p+1 ≥ 1 ensures R2 fires in residual phase.
theorem main_trans (K p r : ℕ) (hpr : p + r = 2 * K + 3) :
    ⟨K + p + 2, 0, 0, r + 1, 0⟩ [fm]⊢⁺
    ⟨4 * K + 4 * p + 3 * r + 10, 0, 0, 2 * K + 2 * p + 3 * r + 5, 0⟩ := by
  -- First step: R3 to get ⊢⁺
  step fm
  -- Now at (K+p+1, 0, 0, r+2, 1), goal is ⊢*
  -- Phase 1 cont: remaining R3 drain (K+p+1 steps)
  rw [show K + p + 1 = 0 + (K + p + 1) from by ring]
  apply stepStar_trans (r3_drain (K + p + 1) 0 (r + 2) 1)
  -- (0, 0, 0, r+2+K+p+1, 1+K+p+1) = (0, 0, 0, K+p+r+3, K+p+2)
  rw [show r + 2 + (K + p + 1) = 0 + (K + p + r + 3) from by ring,
      show 1 + (K + p + 1) = K + p + 2 from by ring]
  -- Phase 2: R4 transfer
  apply stepStar_trans (d_to_c (K + p + r + 3) 0 0 (K + p + 2))
  -- (0, 0, K+p+r+3, 0, K+p+2)
  rw [show 0 + (K + p + r + 3) = (K + p + r + 2) + 1 from by ring,
      show K + p + 2 = (K + p + 1) + 1 from by ring]
  -- Phase 3: R5 then R2
  step fm; step fm
  -- (3, 0, K+p+r+2, 0, K+p+1)
  -- K+p+r+2 = K+2K+3+2 = 3K+5 = (3K+2)+3
  rw [show K + p + r + 2 = (3 * K + 2) + 3 from by omega,
      show (3 : ℕ) = 2 + 1 from rfl]
  -- Phase 4: R1x3
  step fm; step fm; step fm
  -- (0, 6, 3K+2, 3, K+p+1)
  -- 3K+2 = 2 + 3K. K+p+1 = (p+1) + K
  rw [show 3 * K + 2 = 2 + 3 * K from by ring,
      show (6 : ℕ) = 5 + 1 from rfl,
      show K + p + 1 = (p + 1) + K from by ring]
  -- Phase 5: R2+R1x3 chain (K rounds)
  apply stepStar_trans (r2r1x3_chain K 5 2 3 (p + 1))
  -- (0, 5K+6, 2, 3K+3, p+1)
  rw [show 5 + 5 * K + 1 = (5 * K + 5) + 1 from by ring,
      show 3 + 3 * K = 3 * K + 3 from by ring,
      show p + 1 = p + 1 from rfl]
  -- Phase 6: R2 + R1x2 (3 steps)
  step fm  -- R2: (3, 5K+5, 2, 3K+3, p)
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  step fm; step fm  -- R1 x2: (1, 5K+9, 0, 3K+5, p)
  -- Phase 7: R2 drain (p steps)
  -- (1, 5K+9, 0, 3K+5, p) = (1, (5K+9-p)+p, 0, 3K+5, p)
  -- But 5K+9-p ≥ 0 since p ≤ 2K+3 ≤ 5K+9.
  -- We use: 5K+9 = (3K+r+6) + p since r = 2K+3-p, so 3K+r+6 = 3K+(2K+3-p)+6 = 5K+9-p.
  rw [show 5 * K + 9 = (3 * K + r + 6) + p from by omega]
  apply stepStar_trans (r2_drain p 1 (3 * K + r + 6) (3 * K + 5))
  -- (1+3p, 3K+r+6, 0, 3K+5, 0)
  -- Phase 8: R3+R2 drain (3K+r+6 rounds)
  rw [show 1 + 3 * p = (3 * p) + 1 from by ring]
  apply stepStar_trans (r3r2_drain (3 * K + r + 6) (3 * p) (3 * K + 5))
  -- ((3p)+1+2(3K+r+6), 0, 0, 3K+5+(3K+r+6), 0)
  -- = (3p+6K+2r+13, 0, 0, 6K+r+11, 0)
  -- Target: (4K+4p+3r+10, 0, 0, 2K+2p+3r+5, 0)
  -- With p+r=2K+3:
  --   3p+6K+2r+13 = 3p+6K+2(2K+3-p)+13 = 3p+6K+4K+6-2p+13 = p+10K+19
  --   4K+4p+3r+10 = 4K+4p+3(2K+3-p)+10 = 4K+4p+6K+9-3p+10 = p+10K+19 ✓
  --   6K+r+11 = 6K+(2K+3-p)+11 = 8K+14-p
  --   2K+2p+3r+5 = 2K+2p+3(2K+3-p)+5 = 2K+2p+6K+9-3p+5 = 8K+14-p ✓
  have h1 : 3 * p + 1 + 2 * (3 * K + r + 6) = 4 * K + 4 * p + 3 * r + 10 := by omega
  have h2 : 3 * K + 5 + (3 * K + r + 6) = 2 * K + 2 * p + 3 * r + 5 := by omega
  rw [h1, h2]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨11, 0, 0, 4, 0⟩) (by execute fm 20)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ K p r, q = ⟨K + p + 2, 0, 0, r + 1, 0⟩ ∧ p + r = 2 * K + 3)
  · intro c ⟨K, p, r, hq, hpr⟩; subst hq
    -- Next state: (4K+4p+3r+10, 0, 0, 2K+2p+3r+5, 0)
    -- Need K', p', r' with: K'+p'+2 = 4K+4p+3r+10, r'+1 = 2K+2p+3r+5, p'+r' = 2K'+3
    -- K' = 6K+9, p' = 4K+p+8, r' = 2K+2p+3r+4 = 2K+2p+3(2K+3-p)+4 = 8K-p+13
    -- But to avoid subtraction, express r' = 8K+13-p... need p ≤ 8K+13.
    -- p ≤ p+r = 2K+3 ≤ 8K+13. OK.
    -- Actually let's compute r' differently: r' = 2K'+3-p' = 2(6K+9)+3-(4K+p+8) = 12K+21-4K-p-8 = 8K-p+13
    -- We can also express: 2K+2p+3r+5 = r'+1, so r' = 2K+2p+3r+4.
    -- And K'+p'+2 = 4K+4p+3r+10, K' = 6K+9 → p' = 4K+4p+3r+10-6K-9-2 = -2K+4p+3r-1
    -- Using r = 2K+3-p: p' = -2K+4p+6K+9-3p-1 = 4K+p+8
    -- Check: p'+r' = (4K+p+8)+(2K+2p+3r+4) = 6K+3p+3r+12 = 6K+3(2K+3)+12 = 12K+21 = 2(6K+9)+3 = 2K'+3. ✓
    refine ⟨⟨4*K+4*p+3*r+10, 0, 0, 2*K+2*p+3*r+5, 0⟩,
      ⟨6*K+9, 4*K+p+8, 2*K+2*p+3*r+4, ?_, ?_⟩, main_trans K p r hpr⟩
    · -- state equality: K'+p'+2 = 4K+4p+3r+10 and r'+1 = 2K+2p+3r+5
      -- K' = 6K+9, p' = 4K+p+8: (6K+9)+(4K+p+8)+2 = 10K+p+19
      -- Target a = 4K+4p+3r+10. With r = 2K+3-p: 4K+4p+6K+9-3p+10 = 10K+p+19. ✓
      -- r' = 2K+2p+3r+4: r'+1 = 2K+2p+3r+5. ✓
      show (4*K+4*p+3*r+10, 0, 0, 2*K+2*p+3*r+5, 0) =
        ((6*K+9) + (4*K+p+8) + 2, 0, 0, (2*K+2*p+3*r+4) + 1, 0)
      congr 1; omega
    · -- p'+r' = 2K'+3
      -- (4K+p+8)+(2K+2p+3r+4) = 6K+3p+3r+12 = 6K+3(p+r)+12 = 6K+3(2K+3)+12 = 12K+21
      -- 2(6K+9)+3 = 12K+21. ✓
      omega
  · -- Initial: (11, 0, 0, 4, 0) = (K+p+2, 0, 0, r+1, 0) with K=3, p=6, r=3
    exact ⟨3, 6, 3, rfl, by omega⟩

end Sz22_2003_unofficial_1388
