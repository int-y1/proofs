import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1791: [9/10, 44/21, 91/2, 5/11, 15/13]

Vector representation:
```
-1  2 -1  0  0  0
 2 -1  0 -1  1  0
-1  0  0  1  0  1
 0  0  1  0 -1  0
 0  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1791

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d+1, e, f⟩ => some ⟨a+2, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

theorem e_to_c : ∀ k c, ⟨0, 0, c, d, e + k, f⟩ [fm]⊢* ⟨0, 0, c + k, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  · rw [Nat.add_succ e k]; step fm
    apply stepStar_trans (ih (c + 1)); ring_nf; finish

theorem r3_drain : ∀ k d f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d + k, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (d + 1) (f + 1)); ring_nf; finish

theorem r1r2_chain : ∀ k c d e, ⟨2, b, c + 2 * k, d + k, e, f⟩ [fm]⊢* ⟨2, b + 3 * k, c, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (c + 2) (d + 1) e)
    step fm; step fm; step fm; ring_nf; finish

theorem r2_drain_aux : ∀ j a e, ⟨a, B + j, 0, j, e, f⟩ [fm]⊢* ⟨a + 2 * j, B, 0, 0, e + j, f⟩ := by
  intro j; induction' j with j ih <;> intro a e
  · exists 0
  · rw [show B + (j + 1) = (B + j) + 1 from by ring,
        show (j + 1 : ℕ) = j + 1 from rfl]
    apply stepStar_trans
      (step_stepStar (show ⟨a, (B + j) + 1, 0, j + 1, e, f⟩ [fm]⊢ ⟨a + 2, B + j, 0, j, e + 1, f⟩ from by simp [fm]))
    apply stepStar_trans (ih (a + 2) (e + 1))
    ring_nf; finish

theorem r3r2_alt : ∀ k a e f, ⟨a + 1, B + k, 0, 0, e, f⟩ [fm]⊢* ⟨a + k + 1, B, 0, 0, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a e f
  · exists 0
  · rw [show B + (k + 1) = (B + k) + 1 from by ring]
    apply stepStar_trans
      (step_stepStar (show ⟨a + 1, (B + k) + 1, 0, 0, e, f⟩ [fm]⊢ ⟨a, (B + k) + 1, 0, 1, e, f + 1⟩ from by simp [fm]))
    apply stepStar_trans
      (step_stepStar (show ⟨a, (B + k) + 1, 0, 1, e, f + 1⟩ [fm]⊢ ⟨a + 2, B + k, 0, 0, e + 1, f + 1⟩ from by simp [fm]))
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (e + 1) (f + 1))
    ring_nf; finish

-- Combined: R1R2 chain k rounds + R2 drain j steps (even case).
-- (2, 0, 2k, j+k, E, F) →* (2j+2, 3k-j, 0, 0, E+k+j, F) when j <= 3k.
-- We hardcode B₀ = 0 to avoid issues.
theorem spiral_even_zero (h : j ≤ 3 * k) :
    ⟨2, 0, 2 * k, j + k, e, f⟩ [fm]⊢* ⟨2 * j + 2, 3 * k - j, 0, 0, e + k + j, f⟩ := by
  rw [show 2 * k = 0 + 2 * k from by ring,
      show (0 : ℕ) = 0 from rfl]
  apply stepStar_trans (r1r2_chain k 0 j e (b := 0))
  rw [show 0 + 3 * k = (3 * k - j) + j from by omega]
  apply stepStar_trans (r2_drain_aux (B := 3 * k - j) (f := f) j 2 (e + k))
  ring_nf; finish

-- Combined: R1R2 chain k rounds + R1 + R2 drain j steps (odd case).
-- (2, 0, 2k+1, j+k, E, F) →* (2j+1, 3k-j+2, 0, 0, E+k+j, F) when j <= 3k+2.
theorem spiral_odd_zero (h : j ≤ 3 * k + 2) :
    ⟨2, 0, 2 * k + 1, j + k, e, f⟩ [fm]⊢* ⟨2 * j + 1, 3 * k + 2 - j, 0, 0, e + k + j, f⟩ := by
  rw [show 2 * k + 1 = 1 + 2 * k from by ring,
      show (0 : ℕ) = 0 from rfl]
  apply stepStar_trans (r1r2_chain k 1 j e (b := 0))
  apply stepStar_trans
    (step_stepStar (show ⟨2, 0 + 3 * k, 1, j, e + k, f⟩ [fm]⊢ ⟨1, 0 + 3 * k + 2, 0, j, e + k, f⟩ from by simp [fm]))
  rw [show 0 + 3 * k + 2 = (3 * k + 2 - j) + j from by omega]
  apply stepStar_trans (r2_drain_aux (B := 3 * k + 2 - j) (f := f) j 1 (e + k))
  ring_nf; finish

-- Main transition: (0,0,0,D+1,E,F+1) →⁺ (0,0,0,D+E+3,2E+3,F+3E+5).
-- We use explicit parameters to avoid ℕ subtraction issues.
-- Even E case: E = 2K. Spiral odd with k=K, j=D-K.
-- After spiral: a=2(D-K)+1, b=3K+2-(D-K)=4K-D+2, e'=D+1.
-- Then R3R2 alt b times, then R3 drain a+b times.
-- Odd E case: E = 2K+1. Spiral even with k=K+1, j=D-K-1.
-- After spiral: a=2(D-K-1)+2=2D-2K, b=3(K+1)-(D-K-1)=4K-D+4, e'=D+1.
-- Then R3R2 alt b times, then R3 drain a+b times.

-- Helper: from (A+1, B, 0, 0, E, F) with B ≥ 0, drain all to canonical.
-- R3R2 alt B times: (A+B+1, 0, 0, 0, E+B, F+B).
-- R3 drain A+B+1 times: (0, 0, 0, A+B+1, E+B, F+B+A+B+1).
theorem alt_drain (A B E F : ℕ) :
    ⟨A + 1, B, 0, 0, E, F⟩ [fm]⊢* ⟨0, 0, 0, A + B + 1, E + B, F + A + 2 * B + 1⟩ := by
  rw [show (B : ℕ) = 0 + B from by ring]
  apply stepStar_trans (r3r2_alt (B := 0) B A E F)
  rw [show A + B + 1 = 0 + (A + B + 1) from by ring]
  apply stepStar_trans (r3_drain (A + B + 1) 0 (F + B))
  ring_nf; finish

theorem main_trans (hE : E ≤ 2 * D) (hD : D ≤ 2 * E + 2) :
    ⟨0, 0, 0, D + 1, E, F + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, D + E + 3, 2 * E + 3, F + 3 * E + 5⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show E = 0 + E from by ring]; exact e_to_c E 0
  apply step_stepStar_stepPlus
    (show ⟨0, 0, 0 + E, D + 1, 0, F + 1⟩ [fm]⊢ ⟨0, 1, 0 + E + 1, D + 1, 0, F⟩ from by simp [fm])
  apply stepStar_trans
    (step_stepStar (show ⟨0, 1, 0 + E + 1, D + 1, 0, F⟩ [fm]⊢ ⟨2, 0, 0 + E + 1, D, 1, F⟩ from by simp [fm]))
  rcases Nat.even_or_odd E with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- E = K+K (even)
    subst hK
    rw [show 0 + (K + K) + 1 = 2 * K + 1 from by ring,
        show D = (D - K) + K from by omega]
    have hj : D - K ≤ 3 * K + 2 := by omega
    apply stepStar_trans (spiral_odd_zero hj)
    -- After spiral: (2*(D-K)+1, 3*K+2-(D-K), 0, 0, 1+K+(D-K), F)
    -- = (2D-2K+1, 4K-D+2, 0, 0, D+1, F)
    -- Use alt_drain with A = 2D-2K, B = 4K-D+2 (but these involve ℕ subtraction).
    -- A + 1 = 2(D-K)+1, B = 3K+2-(D-K).
    -- A + B + 1 = 2(D-K)+1 + 3K+2-(D-K) = D+3K+3-K = need to compute.
    -- Actually: 2(D-K)+1 + (3K+2-(D-K)) = 2D-2K+1+3K+2-D+K = D+2K+3.
    -- E + B = D+1 + (3K+2-(D-K)) = D+1+4K-D+2 = 4K+3 = 2(K+K)+3 = 2E+3.
    -- F + A + 2B + 1 = F + (2D-2K) + 2(4K-D+2) + 1 = F + 2D-2K+8K-2D+4+1 = F+6K+5 = F+3(2K)+5 = F+3E+5.
    apply stepStar_trans (alt_drain (2 * (D - K)) (3 * K + 2 - (D - K)) (1 + K + (D - K)) F)
    have hDK : D - K + K = D := by omega
    have hDK2 : D - K ≤ 3 * K + 2 := hj
    have h1 : 2 * (D - K) + (3 * K + 2 - (D - K)) + 1 = D - K + K + (K + K) + 3 := by omega
    have h2 : 1 + K + (D - K) + (3 * K + 2 - (D - K)) = 2 * (K + K) + 3 := by omega
    have h3 : F + 2 * (D - K) + 2 * (3 * K + 2 - (D - K)) + 1 = F + 3 * (K + K) + 5 := by omega
    rw [h1, h2, h3, hDK]; finish
  · -- E = 2K+1 (odd)
    subst hK
    rw [show 0 + (2 * K + 1) + 1 = 2 * (K + 1) from by ring,
        show D = (D - K - 1) + (K + 1) from by omega]
    have hj : D - K - 1 ≤ 3 * (K + 1) := by omega
    apply stepStar_trans (spiral_even_zero hj)
    apply stepStar_trans (alt_drain (2 * (D - K - 1) + 1) (3 * (K + 1) - (D - K - 1)) (1 + (K + 1) + (D - K - 1)) F)
    have hDK : D - K - 1 + (K + 1) = D := by omega
    have hDK2 : D - K - 1 ≤ 3 * (K + 1) := hj
    have h1 : (2 * (D - K - 1) + 1) + (3 * (K + 1) - (D - K - 1)) + 1 = D - K - 1 + (K + 1) + (2 * K + 1) + 3 := by omega
    have h2 : 1 + (K + 1) + (D - K - 1) + (3 * (K + 1) - (D - K - 1)) = 2 * (2 * K + 1) + 3 := by omega
    have h3 : F + (2 * (D - K - 1) + 1) + 2 * (3 * (K + 1) - (D - K - 1)) + 1 = F + 3 * (2 * K + 1) + 5 := by omega
    rw [h1, h2, h3, hDK]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 0, 1⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E F, q = ⟨0, 0, 0, D + 1, E, F + 1⟩ ∧ E ≤ 2 * D ∧ D ≤ 2 * E + 2)
  · intro c ⟨D, E, F, hq, hE, hD⟩; subst hq
    refine ⟨⟨0, 0, 0, D + E + 3, 2 * E + 3, F + 3 * E + 5⟩,
      ⟨D + E + 2, 2 * E + 3, F + 3 * E + 4, ?_, ?_, ?_⟩, main_trans hE hD⟩
    · ring_nf
    · omega
    · omega
  · exact ⟨0, 0, 0, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1791
