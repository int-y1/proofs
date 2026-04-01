import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1366: [63/10, 4/33, 847/2, 5/7, 3/5]

Vector representation:
```
-1  2 -1  1  0
 2 -1  0  0 -1
-1  0  0  1  2
 0  0  1 -1  0
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1366

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 chain
theorem d_to_c : ∀ k, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih generalizing c d
  · exists 0
  · rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (ih (c := c + 1)); ring_nf; finish

-- R3 chain
theorem r3_chain : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + 2 * k⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]; step fm
    apply stepStar_trans (ih (d := d + 1) (e := e + 2)); ring_nf; finish

-- R1R1R2 chain
theorem r1r1r2_chain : ∀ k, ⟨2, b, c + 2 * k, d, e + k⟩ [fm]⊢* ⟨2, b + 3 * k, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih generalizing b c d e
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b := b + 3) (d := d + 2)); ring_nf; finish

-- Drain by strong induction on a + 3*b
theorem drain : ∀ N, ∀ a b d e, a + 3 * b = N →
    ⟨a + 1, b, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + a + 1 + 2 * b, e + 2 * a + 2 + 3 * b⟩ := by
  intro N; induction' N using Nat.strongRecOn with N ih
  intro a b d e hN
  rcases b with _ | b
  · rw [show a + 1 = 0 + (a + 1) from by ring]
    apply stepStar_trans (r3_chain (a + 1) (a := 0)); ring_nf; finish
  · rcases e with _ | e
    · step fm; step fm
      rcases b with _ | b'
      · rw [show a + 2 = 0 + (a + 2) from by ring]
        apply stepStar_trans (r3_chain (a + 2) (a := 0) (d := d + 1) (e := 1))
        ring_nf; finish
      · step fm
        show ⟨(a + 3) + 1, b', 0, d + 1, 0⟩ [fm]⊢* _
        apply stepStar_trans (ih _ (by omega) (a + 3) b' (d + 1) 0 rfl)
        ring_nf; finish
    · step fm
      show ⟨(a + 2) + 1, b, 0, d, e⟩ [fm]⊢* _
      apply stepStar_trans (ih _ (by omega) (a + 2) b d e rfl)
      ring_nf; finish

-- Helper: the ⊢* part after the first R4 step for even case
theorem even_rest :
    ⟨0, 0, 1, 0 + (2 * M), M + F + 1⟩ [fm]⊢* ⟨0, 0, 0, 8 * M + 2, 9 * M + F + 4⟩ := by
  -- Remaining R4 steps: (2*M) more
  apply stepStar_trans (d_to_c (2 * M) (c := 1) (d := 0) (e := M + F + 1))
  -- Now at (0, 0, 1+2*M, 0, M+F+1). R5.
  rw [show (1 : ℕ) + 2 * M = (2 * M) + 1 from by ring]
  step fm -- R5: (0, 1, 2*M, 0, M+F+1)
  -- R2: (2, 0, 2*M, 0, M+F)
  step fm
  -- R1R1R2 x M
  rw [show (2 * M : ℕ) = 0 + 2 * M from by ring,
      show M + F = F + M from by ring]
  apply stepStar_trans (r1r1r2_chain M (b := 0) (c := 0) (d := 0) (e := F))
  -- Now at (2, 3*M, 0, 2*M, F). Drain.
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show (0 : ℕ) + 3 * M = 3 * M from by ring,
      show (0 : ℕ) + 2 * M = 2 * M from by ring]
  apply stepStar_trans (drain (1 + 3 * (3 * M)) 1 (3 * M) (2 * M) F (by ring))
  ring_nf; finish

-- Even case: (0, 0, 0, 2*M+1, M+F+1) →⁺ (0, 0, 0, 8*M+2, 9*M+F+4)
theorem main_trans_even :
    ⟨0, 0, 0, 2 * M + 1, M + F + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 8 * M + 2, 9 * M + F + 4⟩ := by
  -- First R4 step gives us ⊢⁺
  rw [show 2 * M + 1 = 0 + (2 * M + 1) from by ring]
  step fm -- R4: (0, 0, 1, 0+(2*M), M+F+1)
  exact even_rest

-- Helper: the ⊢* part after the first R4 step for odd case
theorem odd_rest :
    ⟨0, 0, 1, 0 + (2 * M + 1), M + G + 2⟩ [fm]⊢* ⟨0, 0, 0, 8 * M + 6, 9 * M + G + 9⟩ := by
  -- Remaining R4 steps: (2*M+1) more
  apply stepStar_trans (d_to_c (2 * M + 1) (c := 1) (d := 0) (e := M + G + 2))
  -- Now at (0, 0, 2+2*M, 0, M+G+2). R5.
  rw [show (1 : ℕ) + (2 * M + 1) = (2 * M + 1) + 1 from by ring]
  step fm -- R5: (0, 1, 2*M+1, 0, M+G+2)
  -- R2: (2, 0, 2*M+1, 0, M+G+1)
  step fm
  -- R1R1R2 x M
  rw [show 2 * M + 1 = 1 + 2 * M from by ring,
      show M + G + 1 = (G + 1) + M from by ring]
  apply stepStar_trans (r1r1r2_chain M (b := 0) (c := 1) (d := 0) (e := G + 1))
  -- Now at (2, 3*M, 1, 2*M, G+1). R1.
  rw [show (0 : ℕ) + 3 * M = 3 * M from by ring,
      show (0 : ℕ) + 2 * M = 2 * M from by ring]
  step fm -- R1: (1, 3*M+2, 0, 2*M+1, G+1)
  -- Drain
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_trans (drain (0 + 3 * (3 * M + 2)) 0 (3 * M + 2) (2 * M + 1) (G + 1) (by ring))
  ring_nf; finish

-- Odd case: (0, 0, 0, 2*M+2, M+G+2) →⁺ (0, 0, 0, 8*M+6, 9*M+G+9)
theorem main_trans_odd :
    ⟨0, 0, 0, 2 * M + 2, M + G + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 8 * M + 6, 9 * M + G + 9⟩ := by
  rw [show 2 * M + 2 = 0 + (2 * M + 2) from by ring]
  step fm -- R4: (0, 0, 1, 0+(2*M+1), M+G+2)
  exact odd_rest

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D + 1, E + 1⟩ ∧ 2 * E ≥ D)
  · intro c ⟨D, E, hq, hDE⟩; subst hq
    rcases Nat.even_or_odd D with ⟨M, hM⟩ | ⟨M, hM⟩
    · rw [show M + M = 2 * M from by ring] at hM; subst hM
      obtain ⟨F, rfl⟩ : ∃ F, E = M + F := ⟨E - M, by omega⟩
      exact ⟨⟨0, 0, 0, 8 * M + 2, 9 * M + F + 4⟩,
        ⟨8 * M + 1, 9 * M + F + 3, by ring_nf, by omega⟩,
        main_trans_even⟩
    · subst hM
      obtain ⟨G, rfl⟩ : ∃ G, E = M + G + 1 := ⟨E - M - 1, by omega⟩
      exact ⟨⟨0, 0, 0, 8 * M + 6, 9 * M + G + 9⟩,
        ⟨8 * M + 5, 9 * M + G + 8, by ring_nf, by omega⟩,
        main_trans_odd⟩
  · exact ⟨0, 1, by ring_nf, by omega⟩

end Sz22_2003_unofficial_1366
