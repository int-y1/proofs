import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #840: [36/35, 5/22, 147/2, 11/3, 2/7]

Vector representation:
```
 2  2 -1 -1  0
-1  0  1  0 -1
-1  1  0  2  0
 0 -1  0  0  1
 1  0  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_840

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

theorem spiral : ∀ k, ∀ a b d e, ⟨a + 1, b, 0, d + k, e + k⟩ [fm]⊢* ⟨a + 1 + k, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (b + 2) d e)
    ring_nf; finish

theorem r2_drain : ∀ k, ∀ a b c, ⟨a + k, b, c, 0, k⟩ [fm]⊢* ⟨a, b, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b c
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a b (c + 1))
    ring_nf; finish

theorem r3_drain : ∀ k, ∀ b d, ⟨k, b, 0, d, 0⟩ [fm]⊢* ⟨0, b + k, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) (d + 2))
    ring_nf; finish

theorem r4_drain : ∀ k, ∀ d e, ⟨0, k, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih d (e + 1))
    ring_nf; finish

theorem from_abc : ∀ c, ∀ a b, ⟨a + 1, b, c, 0, 0⟩ [fm]⊢* ⟨0, 0, 0, 2 * a + 3 * c + 2, a + b + 4 * c + 1⟩ := by
  intro c; induction' c using Nat.strongRecOn with c ih; intro a b
  rcases c with _ | _ | c
  · apply stepStar_trans (r3_drain (a + 1) b 0)
    apply stepStar_trans (r4_drain (b + (a + 1)) (0 + 2 * (a + 1)) 0)
    ring_nf; finish
  · step fm; step fm
    apply stepStar_trans (r3_drain (a + 2) (b + 3) 1)
    apply stepStar_trans (r4_drain (b + 3 + (a + 2)) (1 + 2 * (a + 2)) 0)
    ring_nf; finish
  · step fm; step fm; step fm
    apply stepStar_trans (ih c (by omega) (a + 3) (b + 5))
    ring_nf; finish

theorem main_transition (hD : D ≥ 2) (hDE : D ≤ E) (h2D : 2 * D ≥ E + 2) :
    ⟨0, 0, 0, D, E⟩ [fm]⊢⁺ ⟨0, 0, 0, D + E + 1, 3 * E + 1⟩ := by
  -- Decompose D and E into spiral parameters.
  -- Let C = E - (D-1) = E - D + 1 (R2 drain count)
  -- Let A = D - 1 - C (from_abc a parameter, so a+1 = D - C = 2D - E - 1... + 1 = 2D - E)
  -- We need: A + 1 + C = D (total after R5 is D, split A+1 for from_abc + C for drains)
  -- and E = C + (D - 1) (spiral decomposes E into C remainder + D-1 spiral rounds)
  obtain ⟨C, hC⟩ : ∃ C, C + (D - 1) = E := ⟨E - (D - 1), by omega⟩
  obtain ⟨A, hA⟩ : ∃ A, A + C = D - 1 := ⟨D - 1 - C, by omega⟩
  -- Now D = A + C + 1, E = C + (A + C) = C + A + C = A + 2C
  -- Wait: E = C + (D-1) = C + (A + C) = A + 2C. And D = A + C + 1.
  -- Check: 2D >= E+2 => 2(A+C+1) >= (A+2C)+2 => 2A+2C+2 >= A+2C+2 => A >= 0 ✓
  -- And D <= E => A+C+1 <= A+2C => 1 <= C, so C >= 1.
  have hC1 : C ≥ 1 := by omega
  -- D = A + C + 1
  have hD_eq : D = A + C + 1 := by omega
  -- E = A + 2 * C
  have hE_eq : E = A + 2 * C := by omega
  subst hD_eq; subst hE_eq
  -- Goal: (0,0,0,A+C+1,A+2*C) ⊢⁺ (0,0,0,(A+C+1)+(A+2*C)+1, 3*(A+2*C)+1)
  -- = (0,0,0,2*A+3*C+2, 3*A+6*C+1)
  -- R5 step
  step fm
  -- After R5: (1, 0, 0, A+C, A+2*C)
  -- spiral (A+C) rounds: (1, 0, 0, 0+(A+C), C+(A+C)) ⊢* (1+(A+C), 2*(A+C), 0, 0, C)
  rw [show (A + C : ℕ) = 0 + (A + C) from by ring,
      show (A + 2 * C : ℕ) = C + (A + C) from by ring]
  apply stepStar_trans (spiral (A + C) 0 0 0 C)
  -- After spiral: (A+C+1, 2*A+2*C, 0, 0, C)
  -- R2 drain C steps: (A+C+1, 2*A+2*C, 0, 0, C) = ((A+1)+C, 2*A+2*C, 0, 0, C)
  rw [show 0 + 1 + (A + C) = (A + 1) + C from by ring,
      show 0 + 2 * (A + C) = 2 * A + 2 * C from by ring]
  apply stepStar_trans (r2_drain C (A + 1) (2 * A + 2 * C) 0)
  -- After R2 drain: (A+1, 2*A+2*C, C, 0, 0)
  -- from_abc C A (2*A+2*C)
  rw [show 0 + C = C from by ring]
  apply stepStar_trans (from_abc C A (2 * A + 2 * C))
  -- Result: (0, 0, 0, 2*A+3*C+2, A+(2*A+2*C)+4*C+1) = (0, 0, 0, 2*A+3*C+2, 3*A+6*C+1)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 4, 4⟩) (by execute fm 11)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D, E⟩ ∧ D ≥ 2 ∧ D ≤ E ∧ 2 * D ≥ E + 2)
  · intro c ⟨D, E, hq, hD, hDE, h2D⟩; subst hq
    exact ⟨⟨0, 0, 0, D + E + 1, 3 * E + 1⟩,
      ⟨D + E + 1, 3 * E + 1, rfl, by omega, by omega, by omega⟩,
      main_transition hD hDE h2D⟩
  · exact ⟨4, 4, rfl, by omega, by omega, by omega⟩
