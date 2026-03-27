import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #502: [28/15, 3/22, 25/2, 1331/7, 3/5]

Vector representation:
```
 2 -1 -1  1  0
-1  1  0  0 -1
-1  0  2  0  0
 0  0  0 -1  3
 0  1 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_502

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem d_to_e : ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + 3 * k⟩ := by
  have h : ∀ k d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨0, 0, c, d, e + 3 * k⟩ := by
    intro k; induction' k with k ih <;> intro d e
    · exists 0
    rw [show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih _ _); step fm
    rw [show e + 3 * k + 3 = e + 3 * (k + 1) from by ring]; finish
  exact h k d e

theorem r1r2_chain : ∀ k, ∀ a d e, ⟨a, 1, k + 1, d, e + k⟩ [fm]⊢*
    ⟨a + k + 2, 0, 0, d + k + 1, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · step fm; ring_nf; finish
  rw [show (k + 1) + 1 = k + 1 + 1 from rfl,
      show e + (k + 1) = e + k + 1 from by ring]
  step fm; rw [show a + 2 = (a + 1) + 1 from by ring]; step fm
  apply stepStar_trans (ih (a + 1) (d + 1) e); ring_nf; finish

theorem r2_drain : ∀ k, ∀ a b, ⟨a + k, b, 0, d, k⟩ [fm]⊢* ⟨a, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring, show (k : ℕ) + 1 = k + 1 from rfl]
  step fm; rw [show b + (k + 1) = (b + 1) + k from by ring]; exact ih _ _

theorem r3_drain : ∀ a, ∀ c, ⟨a, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c + 2 * a, d, 0⟩ := by
  intro a; induction' a with a ih <;> intro c
  · exists 0
  step fm; apply stepStar_trans (ih _); ring_nf; finish

theorem r3r1r1_rounds : ∀ k, ∀ a d, ⟨a + 1, b + 2 * k, 0, d, 0⟩ [fm]⊢*
    ⟨a + 3 * k + 1, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring]
  step fm; step fm; step fm
  rw [show a + 1 + 1 + 2 = (a + 3) + 1 from by ring,
      show d + 1 + 1 = d + 2 from by ring,
      show a + 3 * (k + 1) + 1 = (a + 3) + 3 * k + 1 from by ring,
      show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
  exact ih _ _

theorem b1_cleanup : ⟨a + 1, 1, 0, d, 0⟩ [fm]⊢* ⟨0, 0, 2 * a + 5, d + 1, 0⟩ := by
  step fm; step fm; step fm
  apply stepStar_trans (r3_drain _ _); ring_nf; finish

theorem main_trans (hlo : 2 * c ≥ 3 * d + 3) (hhi : c ≤ 3 * d + 2) :
    ⟨0, 0, c, d, 0⟩ [fm]⊢⁺ ⟨0, 0, c + 3 * d + 2, 3 * d + 1, 0⟩ := by
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 2 := ⟨c - 2, by omega⟩
  -- A = 2c'+2-3d ≥ 1 (from hlo: 2c'+4 ≥ 3d+3, so 2c'+2 ≥ 3d+1, so A ≥ 1)
  obtain ⟨A, hA⟩ : ∃ A, 2 * c' + 2 - 3 * d = A + 1 := ⟨2 * c' + 1 - 3 * d, by omega⟩
  -- Phase 1: drain d
  rw [show d = 0 + d from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e (e := 0))
  simp only [Nat.zero_add]
  -- Phase 2: R5 + r1r2_chain
  rw [show (3 : ℕ) * d = (3 * d - c') + c' from by omega]
  step fm
  apply stepStar_trans (r1r2_chain c' 0 0 (3 * d - c'))
  rw [show 0 + c' + 2 = c' + 2 from by ring, show 0 + c' + 1 = c' + 1 from by ring]
  -- Phase 3: R2 drain
  rw [show c' + 2 = (A + 1) + (3 * d - c') from by omega]
  apply stepStar_trans (r2_drain (3 * d - c') _ 0)
  rw [show (0 : ℕ) + (3 * d - c') = 3 * d - c' from by ring]
  -- State: (A+1, 3d-c', 0, c'+1, 0)
  -- The target RHS is: (0, 0, A+1+(3d-c')+(3d-c'+c')+2, 3d-c'+c'+1, 0)
  -- We need to rewrite it to match the phase outputs
  rcases Nat.even_or_odd (3 * d - c') with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- Even: 3d-c' = 2K
    rw [hK]
    -- Target RHS: (0, 0, A+1+(K+K)+(K+K+c')+2, K+K+c'+1, 0)
    -- r3r1r1_rounds produces: (A+3K+1, 0, 0, c'+1+2K, 0) from (A+1, 0+2K, 0, c'+1, 0)
    -- r3_drain produces: (0, 0, 0+2*(A+3K+1), c'+1+2K, 0)
    -- = (0, 0, 2A+6K+2, c'+1+2K, 0)
    -- Need: 2A+6K+2 = A+1+(K+K)+(K+K+c')+2 and c'+1+2K = K+K+c'+1
    rw [show K + K = 0 + 2 * K from by ring]
    apply stepStar_trans (r3r1r1_rounds K A _)
    apply stepStar_trans (r3_drain _ _)
    rw [show 0 + 2 * (A + 3 * K + 1) = A + 1 + (0 + 2 * K) + (0 + 2 * K + c') + 2 from by omega,
        show c' + 1 + 2 * K = 0 + 2 * K + c' + 1 from by omega]
    finish
  · -- Odd: 3d-c' = 2K+1
    rw [hK]
    -- r3r1r1_rounds with b=1: (A+1, 1+2K, 0, c'+1, 0) -> (A+3K+1, 1, 0, c'+1+2K, 0)
    -- b1_cleanup: (A+3K+1, 1, 0, c'+1+2K, 0) -> (0, 0, 2(A+3K)+5, c'+1+2K+1, 0)
    rw [show 2 * K + 1 = 1 + 2 * K from by ring]
    apply stepStar_trans (r3r1r1_rounds K A _)
    apply stepStar_trans b1_cleanup
    rw [show 2 * (A + 3 * K) + 5 = A + 1 + (1 + 2 * K) + (1 + 2 * K + c') + 2 from by omega,
        show c' + 1 + 2 * K + 1 = 1 + 2 * K + c' + 1 from by omega]
    finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 1, 0⟩) (by execute fm 5)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c d, q = ⟨0, 0, c, d, 0⟩ ∧ d ≥ 1 ∧ 2 * c ≥ 3 * d + 3 ∧ c ≤ 3 * d + 2)
  · intro q ⟨c, d, hq, hd, hlo, hhi⟩; subst hq
    exact ⟨⟨0, 0, c + 3 * d + 2, 3 * d + 1, 0⟩,
      ⟨c + 3 * d + 2, 3 * d + 1, rfl, by omega, by omega, by omega⟩,
      main_trans hlo hhi⟩
  · exact ⟨4, 1, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_502
