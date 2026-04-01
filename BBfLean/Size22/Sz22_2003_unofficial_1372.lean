import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1372: [63/10, 4/77, 363/2, 5/3, 7/11]

Vector representation:
```
-1  2 -1  1  0
 2  0  0 -1 -1
-1  1  0  0  2
 0 -1  1  0  0
 0  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1372

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+2⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

theorem r4_chain : ∀ k, ⟨0, b + k, c, 0, e⟩ [fm]⊢* ⟨0, b, c + k, 0, e⟩ := by
  intro k; induction' k with k ih generalizing b c
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b) (c := c + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ⟨a + k, b, 0, 0, e⟩ [fm]⊢* ⟨a, b + k, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a b e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1) (e := e + 2))
    ring_nf; finish

-- R1R1R2 interleaved chain: each round does R1, R1, R2
-- b += 4, c -= 2, d += 1, e -= 1 per round
theorem r1r1r2_chain : ∀ k, ∀ b c d e,
    ⟨2, b, c + 2 * k, d, e + k⟩ [fm]⊢* ⟨2, b + 4 * k, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 4) c (d + 1) e)
    ring_nf; finish

-- R2 drain: consume matching d,e pairs
theorem r2_drain : ∀ k, ∀ a b d e,
    ⟨a, b, 0, d + k, e + k⟩ [fm]⊢* ⟨a + 2 * k, b, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) b d e)
    ring_nf; finish

-- R3R2R2 chain: each round does R3, R2, R2
-- a += 3, b += 1, d -= 2 per round
theorem r3r2r2_chain : ∀ k, ∀ a b d,
    ⟨a + 1, b, 0, d + 2 * k, 0⟩ [fm]⊢* ⟨a + 3 * k + 1, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show d + 2 * (k + 1) = (d + 2 * k) + 1 + 1 from by ring]
    step fm; step fm; step fm
    show ⟨(a + 3) + 1, b + 1, 0, d + 2 * k, 0⟩ [fm]⊢* _
    apply stepStar_trans (ih (a + 3) (b + 1) d)
    ring_nf; finish

-- R3 then R2: handle d=1 leftover
theorem r3_r2_leftover : ⟨a + 1, b, 0, 1, 0⟩ [fm]⊢* ⟨a + 2, b + 1, 0, 0, 1⟩ := by
  step fm; step fm; finish

-- Combined R1R1R2 chain starting from specific initial state, plus R1 and R2 drain
-- From (2, 0, C, 0, E) where C = 1 + 2*K, E = F + K
-- Through: chain K rounds → R1 → R2 drain F rounds
-- To: (2*F+1, 4*K+2, 0, K+1-F, 0) but we express K+1-F = D+1 where K = F+D
theorem chain_r1_drain (F D : ℕ) :
    ⟨2, 0, 1 + 2 * (F + D), 0, F + (F + D)⟩ [fm]⊢*
    ⟨2 * F + 1, 4 * F + 4 * D + 2, 0, D + 1, 0⟩ := by
  apply stepStar_trans (r1r1r2_chain (F + D) 0 1 0 F)
  step fm
  rw [show (1, 0 + 4 * (F + D) + 2, 0, 0 + (F + D) + 1, F) =
    ((1 : ℕ), 0 + 4 * (F + D) + 2, (0 : ℕ), (D + 1) + F, (0 : ℕ) + F) from by
      simp only [Nat.zero_add]; congr 1; congr 1; ring_nf]
  apply stepStar_trans (r2_drain F 1 (0 + 4 * (F + D) + 2) (D + 1) 0)
  ring_nf; finish

-- Drain even D: r3r2r2 chain + r3 chain + r4 chain
theorem drain_even (D A B : ℕ) :
    ⟨A + 1, B, 0, 2 * D, 0⟩ [fm]⊢* ⟨0, 0, A + B + 4 * D + 1, 0, 2 * A + 6 * D + 2⟩ := by
  rw [show (2 * D : ℕ) = 0 + 2 * D from by ring]
  apply stepStar_trans (r3r2r2_chain D A B 0)
  rw [show A + 3 * D + 1 = 0 + (A + 3 * D + 1) from by ring]
  apply stepStar_trans (r3_chain (A + 3 * D + 1) (a := 0) (b := B + D) (e := 0))
  rw [show B + D + (A + 3 * D + 1) = 0 + (A + B + 4 * D + 1) from by ring,
      show 0 + 2 * (A + 3 * D + 1) = 2 * A + 6 * D + 2 from by ring]
  apply stepStar_trans (r4_chain (A + B + 4 * D + 1) (b := 0) (c := 0) (e := 2 * A + 6 * D + 2))
  ring_nf; finish

-- Drain odd D: r3r2r2 chain + r3_r2_leftover + r3 chain + r4 chain
theorem drain_odd (D A B : ℕ) :
    ⟨A + 1, B, 0, 2 * D + 1, 0⟩ [fm]⊢* ⟨0, 0, A + B + 4 * D + 3, 0, 2 * A + 6 * D + 5⟩ := by
  rw [show 2 * D + 1 = 1 + 2 * D from by ring]
  apply stepStar_trans (r3r2r2_chain D A B 1)
  apply stepStar_trans (r3_r2_leftover (a := A + 3 * D) (b := B + D))
  rw [show A + 3 * D + 2 = 0 + (A + 3 * D + 2) from by ring]
  apply stepStar_trans (r3_chain (A + 3 * D + 2) (a := 0) (b := B + D + 1) (e := 1))
  rw [show B + D + 1 + (A + 3 * D + 2) = 0 + (A + B + 4 * D + 3) from by ring,
      show 1 + 2 * (A + 3 * D + 2) = 2 * A + 6 * D + 5 from by ring]
  apply stepStar_trans (r4_chain (A + B + 4 * D + 3) (b := 0) (c := 0) (e := 2 * A + 6 * D + 5))
  ring_nf; finish

-- Main transition when D is even: D_actual = D+1 is odd, use drain_odd
theorem main_trans_Deven (F m : ℕ) :
    ⟨0, 0, 2 * F + 4 * m + 1, 0, 2 * F + 2 * m + 2⟩ [fm]⊢⁺
    ⟨0, 0, 6 * F + 12 * m + 5, 0, 4 * F + 6 * m + 5⟩ := by
  -- Phase 1: R5 + R2 (gives ⊢⁺)
  step fm; step fm
  -- State: (2, 0, 2*F+4*m+1, 0, 2*F+2*m)
  -- Rewrite to match chain_r1_drain input
  rw [show (2 * F + 4 * m + 1 : ℕ) = 1 + 2 * (F + 2 * m) from by ring,
      show (2 * F + 2 * m : ℕ) = F + (F + 2 * m) from by ring]
  -- Apply combined chain + R1 + drain
  apply stepStar_trans (chain_r1_drain F (2 * m))
  -- State: (2*F+1, 4*F+4*(2*m)+2, 0, 2*m+1, 0)
  rw [show 4 * F + 4 * (2 * m) + 2 = 4 * F + 8 * m + 2 from by ring]
  apply stepStar_trans (drain_odd m (2 * F) (4 * F + 8 * m + 2))
  ring_nf; finish

-- Main transition when D is odd: D_actual = D+1 is even, use drain_even
theorem main_trans_Dodd (F m : ℕ) :
    ⟨0, 0, 2 * F + 4 * m + 3, 0, 2 * F + 2 * m + 3⟩ [fm]⊢⁺
    ⟨0, 0, 6 * F + 12 * m + 11, 0, 4 * F + 6 * m + 8⟩ := by
  step fm; step fm
  rw [show (2 * F + 4 * m + 3 : ℕ) = 1 + 2 * (F + 2 * m + 1) from by ring,
      show (2 * F + 2 * m + 1 : ℕ) = F + (F + 2 * m + 1) from by ring]
  apply stepStar_trans (chain_r1_drain F (2 * m + 1))
  -- State: (2*F+1, 4*F+4*(2*m+1)+2, 0, 2*m+2, 0)
  rw [show 4 * F + 4 * (2 * m + 1) + 2 = 4 * F + 8 * m + 6 from by ring,
      show 2 * m + 1 + 1 = 2 * (m + 1) from by ring]
  apply stepStar_trans (drain_even (m + 1) (2 * F) (4 * F + 8 * m + 6))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 2⟩)
  · execute fm 2
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, 0, 2 * p.1 + 2 * p.2 + 1, 0, 2 * p.1 + p.2 + 2⟩) ⟨0, 0⟩
  intro ⟨F, D⟩
  rcases Nat.even_or_odd D with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    refine ⟨⟨F + 1, 2 * F + 6 * m + 1⟩, ?_⟩
    change ⟨0, 0, 2 * F + 2 * (2 * m) + 1, 0, 2 * F + 2 * m + 2⟩ [fm]⊢⁺
      ⟨0, 0, 2 * (F + 1) + 2 * (2 * F + 6 * m + 1) + 1, 0,
       2 * (F + 1) + (2 * F + 6 * m + 1) + 2⟩
    rw [show 2 * F + 2 * (2 * m) + 1 = 2 * F + 4 * m + 1 from by ring,
        show 2 * (F + 1) + 2 * (2 * F + 6 * m + 1) + 1 = 6 * F + 12 * m + 5 from by ring,
        show 2 * (F + 1) + (2 * F + 6 * m + 1) + 2 = 4 * F + 6 * m + 5 from by ring]
    exact main_trans_Deven F m
  · subst hm
    refine ⟨⟨F + 1, 2 * F + 6 * m + 4⟩, ?_⟩
    change ⟨0, 0, 2 * F + 2 * (2 * m + 1) + 1, 0, 2 * F + (2 * m + 1) + 2⟩ [fm]⊢⁺
      ⟨0, 0, 2 * (F + 1) + 2 * (2 * F + 6 * m + 4) + 1, 0,
       2 * (F + 1) + (2 * F + 6 * m + 4) + 2⟩
    rw [show 2 * F + 2 * (2 * m + 1) + 1 = 2 * F + 4 * m + 3 from by ring,
        show 2 * F + (2 * m + 1) + 2 = 2 * F + 2 * m + 3 from by ring,
        show 2 * (F + 1) + 2 * (2 * F + 6 * m + 4) + 1 = 6 * F + 12 * m + 11 from by ring,
        show 2 * (F + 1) + (2 * F + 6 * m + 4) + 2 = 4 * F + 6 * m + 8 from by ring]
    exact main_trans_Dodd F m

end Sz22_2003_unofficial_1372
