import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1873: [9/35, 275/6, 2/5, 7/11, 165/2]

Vector representation:
```
 0  2 -1 -1  0
-1 -1  2  0  1
 1  0 -1  0  0
 0  0  0  1 -1
-1  1  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1873

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e+1⟩
  | _ => none

theorem r4_chain : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d := d + 1))
    ring_nf; finish

theorem r3_chain : ∀ k, ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a + k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a c
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1))
    ring_nf; finish

theorem r1r1r2_loop : ∀ k, ⟨A + k, B, 2, D + 2 * k, E⟩ [fm]⊢* ⟨A, B + 3 * k, 2, D, E + k⟩ := by
  intro k; induction' k with k ih generalizing A B D E
  · exists 0
  · rw [show A + (k + 1) = (A + 1) + k from by ring,
        show D + 2 * (k + 1) = (D + 2) + 2 * k from by ring]
    apply stepStar_trans (ih (A := A + 1) (D := D + 2))
    step fm; step fm; step fm; ring_nf; finish

theorem r2_step : ⟨a + 1, b + 1, c, 0, e⟩ [fm]⊢ ⟨a, b, c + 2, 0, e + 1⟩ := by
  simp [fm]

theorem r2_drain : ∀ k, ⟨a + k, b + k, c, 0, e⟩ [fm]⊢* ⟨a, b, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a b c e
  · exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring,
        show b + (k + 1) = (b + 1) + k from by ring]
    apply stepStar_trans (ih (a := a + 1) (b := b + 1))
    exact step_stepStar r2_step

theorem r3r2_alt : ∀ k, ⟨0, k, c + 1, 0, e⟩ [fm]⊢* ⟨0, 0, c + k + 1, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing c e
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih (c := c + 1) (e := e + 1))
    ring_nf; finish

theorem main_trans (hF : F ≤ 3 * K + 4) :
    ⟨K + F + 2, 0, 0, 2 * K + 2, 0⟩ [fm]⊢⁺ ⟨3 * K + F + 5, 0, 0, 4 * K + 6, 0⟩ := by
  obtain ⟨G, hG⟩ : ∃ G, 3 * K + 4 = F + G := ⟨3 * K + 4 - F, by omega⟩
  -- Opening: R5, R1, R2 (3 steps)
  step fm; step fm; step fm
  -- After opening: (K+F, 2, 2, 2K+1, 2)
  -- R1R1R2 loop (K rounds)
  rw [show K + F = F + K from by ring, show 2 * K + 1 = 1 + 2 * K from by ring]
  apply stepStar_trans (r1r1r2_loop K (A := F) (B := 2) (D := 1) (E := 2))
  -- After loop: (F, 2+3K, 2, 1, 2+K)
  -- R1 step
  apply stepStar_trans (step_stepStar (by simp [fm] : ⟨F, 2 + 3 * K, 2, 1, 2 + K⟩ [fm]⊢
    ⟨F, 2 + 3 * K + 2, 1, 0, 2 + K⟩))
  -- After R1: (F, 2+3K+2, 1, 0, 2+K)
  -- R2 drain (F steps)
  rw [show F = 0 + F from by ring,
      show 2 + 3 * K + 2 = G + F from by omega,
      show 2 + K = K + 2 from by ring]
  apply stepStar_trans (r2_drain F (a := 0) (b := G) (c := 1) (e := K + 2))
  -- After R2 drain: (0, G, 1+2F, 0, K+2+F)
  -- R3/R2 alternation (G rounds)
  rw [show 1 + 2 * F = 2 * F + 0 + 1 from by ring,
      show K + 2 + F = K + F + 2 from by ring]
  apply stepStar_trans (r3r2_alt G (c := 2 * F + 0) (e := K + F + 2))
  -- After R3/R2: (0, 0, 2F+G+1, 0, K+F+2+G)
  rw [show 2 * F + 0 + G + 1 = 3 * K + F + 5 from by omega,
      show K + F + 2 + G = 4 * K + 6 from by omega,
      show (3 * K + F + 5 : ℕ) = 0 + (3 * K + F + 5) from by ring]
  -- R3 chain
  apply stepStar_trans (r3_chain (3 * K + F + 5) (a := 0) (c := 0) (e := 4 * K + 6))
  -- After R3: (3K+F+5, 0, 0, 0, 4K+6)
  rw [show 0 + (3 * K + F + 5) = 3 * K + F + 5 from by ring,
      show (4 * K + 6 : ℕ) = 0 + (4 * K + 6) from by ring]
  -- R4 chain
  apply stepStar_trans (r4_chain (4 * K + 6) (a := 3 * K + F + 5) (d := 0) (e := 0))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ K F, q = ⟨K + F + 2, 0, 0, 2 * K + 2, 0⟩ ∧ F ≤ 3 * K + 4)
  · intro c ⟨K, F, hq, hF⟩; subst hq
    refine ⟨⟨3 * K + F + 5, 0, 0, 4 * K + 6, 0⟩,
      ⟨2 * K + 2, K + F + 1, ?_, ?_⟩, main_trans hF⟩
    · show (3 * K + F + 5, (0 : ℕ), (0 : ℕ), 4 * K + 6, (0 : ℕ)) =
        (2 * K + 2 + (K + F + 1) + 2, 0, 0, 2 * (2 * K + 2) + 2, 0)
      have h1 : 3 * K + F + 5 = 2 * K + 2 + (K + F + 1) + 2 := by omega
      have h2 : 4 * K + 6 = 2 * (2 * K + 2) + 2 := by omega
      rw [h1, h2]
    · omega
  · exact ⟨0, 0, rfl, by omega⟩
