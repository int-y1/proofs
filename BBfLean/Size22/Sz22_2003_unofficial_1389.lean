import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1389: [63/10, 8/77, 33/2, 5/3, 7/5]

Vector representation:
```
-1  2 -1  1  0
 3  0  0 -1 -1
-1  1  0  0  1
 0 -1  1  0  0
 0  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1389

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

theorem r3_chain : ∀ k a b e, ⟨a + k, b, 0, 0, e⟩ [fm]⊢* ⟨a, b + k, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih a (b + 1) (e + 1)); ring_nf; finish

theorem r4_chain : ∀ k b c e, ⟨0, b + k, c, 0, e⟩ [fm]⊢* ⟨0, b, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih b (c + 1) e); ring_nf; finish

theorem r2_drain : ∀ k a b d, ⟨a, b, 0, d + k, k⟩ [fm]⊢* ⟨a + 3 * k, b, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring, show (k + 1 : ℕ) = k + 1 from rfl]
    step fm; apply stepStar_trans (ih (a + 3) b d); ring_nf; finish

theorem r3r2_alt : ∀ D a b, ⟨a + 1, b, 0, D, 0⟩ [fm]⊢* ⟨a + 2 * D + 1, b + D, 0, 0, 0⟩ := by
  intro D; induction' D with D ih <;> intro a b
  · exists 0
  · rw [show (D + 1 : ℕ) = D + 1 from rfl]
    step fm; step fm; apply stepStar_trans (ih (a + 2) (b + 1)); ring_nf; finish

theorem round_chain : ∀ K B C D E,
    ⟨3, B, C + 3 * K, D, E + K⟩ [fm]⊢* ⟨3, B + 6 * K, C, D + 2 * K, E⟩ := by
  intro K; induction' K with K ih <;> intro B C D E
  · exists 0
  · rw [show C + 3 * (K + 1) = ((C + 3 * K) + 2) + 1 from by ring,
        show E + (K + 1) = (E + K) + 1 from by ring, show (3 : ℕ) = 2 + 1 from rfl]
    step fm; rw [show (C + 3 * K) + 2 = ((C + 3 * K) + 1) + 1 from by ring]
    step fm; rw [show (C + 3 * K) + 1 = (C + 3 * K) + 1 from rfl]
    step fm; step fm; apply stepStar_trans (ih (B + 6) C (D + 2) E); ring_nf; finish

theorem r1_twice : ∀ B c D E,
    ⟨3, B, c + 2, D, E⟩ [fm]⊢* ⟨1, B + 4, c, D + 2, E⟩ := by
  intro B c D E
  rw [show c + 2 = (c + 1) + 1 from by ring, show (3 : ℕ) = 2 + 1 from rfl]
  step fm; rw [show c + 1 = c + 1 from rfl]; step fm; ring_nf; finish

-- We parameterize by E = A - K to avoid A-K+K issues.
-- r=0: (3, 0, 3K, 0, E+K) →* (2*(E+K)+B+3, 2*(E+K)+3B, 0, 0, 0) where E+K+B = 3K
theorem phase45_r0 (E B K : ℕ) (hEB : E + K + B = 3 * K) :
    ⟨3, 0, 3 * K, 0, E + K⟩ [fm]⊢* ⟨2 * (E + K) + B + 3, 2 * (E + K) + 3 * B, 0, 0, 0⟩ := by
  rw [show 3 * K = 0 + 3 * K from by ring, show E + K = E + K from rfl]
  apply stepStar_trans (round_chain K 0 0 0 E)
  rw [show 0 + 6 * K = 6 * K from by ring, show 0 + 2 * K = (2 * K - E) + E from by omega]
  apply stepStar_trans (r2_drain E 3 (6 * K) (2 * K - E))
  rw [show 3 + 3 * E = (3 * E + 2) + 1 from by ring]
  apply stepStar_trans (r3r2_alt (2 * K - E) (3 * E + 2) (6 * K))
  rw [show 3 * E + 2 + 2 * (2 * K - E) + 1 = 2 * (E + K) + B + 3 from by omega,
      show 6 * K + (2 * K - E) = 2 * (E + K) + 3 * B from by omega]; finish

-- r=1
theorem phase45_r1 (E B K : ℕ) (hEB : E + K + B = 3 * K + 1) :
    ⟨3, 0, 3 * K + 1, 0, E + K⟩ [fm]⊢* ⟨2 * (E + K) + B + 3, 2 * (E + K) + 3 * B, 0, 0, 0⟩ := by
  rw [show 3 * K + 1 = 1 + 3 * K from by ring, show E + K = E + K from rfl]
  apply stepStar_trans (round_chain K 0 1 0 E)
  rw [show 0 + 6 * K = 6 * K from by ring, show 0 + 2 * K = 2 * K from by ring,
      show (3 : ℕ) = 2 + 1 from rfl, show (1 : ℕ) = 0 + 1 from rfl]
  step fm
  rw [show 6 * K + 0 + 1 + 1 = 6 * K + 2 from by ring,
      show 2 * K + 0 + 1 = (2 * K + 1 - E) + E from by omega]
  apply stepStar_trans (r2_drain E 2 (6 * K + 2) (2 * K + 1 - E))
  rw [show 2 + 3 * E = (3 * E + 1) + 1 from by ring]
  apply stepStar_trans (r3r2_alt (2 * K + 1 - E) (3 * E + 1) (6 * K + 2))
  rw [show 3 * E + 1 + 2 * (2 * K + 1 - E) + 1 = 2 * (E + K) + B + 3 from by omega,
      show 6 * K + 2 + (2 * K + 1 - E) = 2 * (E + K) + 3 * B from by omega]; finish

-- r=2
theorem phase45_r2 (E B K : ℕ) (hEB : E + K + B = 3 * K + 2) :
    ⟨3, 0, 3 * K + 2, 0, E + K⟩ [fm]⊢* ⟨2 * (E + K) + B + 3, 2 * (E + K) + 3 * B, 0, 0, 0⟩ := by
  rw [show 3 * K + 2 = 0 + 2 + 3 * K from by ring, show E + K = E + K from rfl]
  apply stepStar_trans (round_chain K 0 (0 + 2) 0 E)
  rw [show 0 + 6 * K = 6 * K from by ring, show 0 + 2 * K = 2 * K from by ring]
  apply stepStar_trans (r1_twice (6 * K) 0 (2 * K) E)
  rw [show 6 * K + 4 = 6 * K + 4 from rfl,
      show 2 * K + 2 = (2 * K + 2 - E) + E from by omega]
  apply stepStar_trans (r2_drain E 1 (6 * K + 4) (2 * K + 2 - E))
  rw [show 1 + 3 * E = (3 * E) + 1 from by ring]
  apply stepStar_trans (r3r2_alt (2 * K + 2 - E) (3 * E) (6 * K + 4))
  rw [show 3 * E + 2 * (2 * K + 2 - E) + 1 = 2 * (E + K) + B + 3 from by omega,
      show 6 * K + 4 + (2 * K + 2 - E) = 2 * (E + K) + 3 * B from by omega]; finish

-- Main transition
theorem main_trans (A B : ℕ) (hBA : B ≤ 2 * A + 1) :
    ⟨A + 1, B, 0, 0, 0⟩ [fm]⊢⁺ ⟨2 * A + B + 3, 2 * A + 3 * B, 0, 0, 0⟩ := by
  have p1 : ⟨A + 1, B, 0, 0, 0⟩ [fm]⊢* ⟨0, A + B + 1, 0, 0, A + 1⟩ := by
    rw [show A + 1 = 0 + (A + 1) from by ring]
    apply stepStar_trans (r3_chain (A + 1) 0 B 0); ring_nf; finish
  have p2 : ⟨0, A + B + 1, 0, 0, A + 1⟩ [fm]⊢* ⟨0, 0, A + B + 1, 0, A + 1⟩ := by
    rw [show A + B + 1 = 0 + (A + B + 1) from by ring]
    apply stepStar_trans (r4_chain (A + B + 1) 0 0 (A + 1)); ring_nf; finish
  have p3 : ⟨0, 0, A + B + 1, 0, A + 1⟩ [fm]⊢⁺ ⟨3, 0, A + B, 0, A⟩ := by
    rw [show A + B + 1 = (A + B) + 1 from by ring, show (A + 1 : ℕ) = A + 1 from rfl]
    step fm; step fm; ring_nf; finish
  suffices p45 : ⟨3, 0, A + B, 0, A⟩ [fm]⊢* ⟨2 * A + B + 3, 2 * A + 3 * B, 0, 0, 0⟩ by
    exact stepStar_stepPlus_stepPlus p1
      (stepStar_stepPlus_stepPlus p2 (stepPlus_stepStar_stepPlus p3 p45))
  -- Determine K = (A+B)/3, use E = A-K
  have ⟨K, hABK⟩ : ∃ K, A + B = 3 * K ∨ A + B = 3 * K + 1 ∨ A + B = 3 * K + 2 := by
    exact ⟨(A + B) / 3, by omega⟩
  rcases hABK with hAB | hAB | hAB
  · have hAK : K ≤ A := by omega
    rw [hAB, show A = A - K + K from (Nat.sub_add_cancel hAK).symm]
    exact phase45_r0 (A - K) B K (by omega)
  · have hAK : K ≤ A := by omega
    rw [hAB, show A = A - K + K from (Nat.sub_add_cancel hAK).symm]
    exact phase45_r1 (A - K) B K (by omega)
  · have hAK : K ≤ A := by omega
    rw [hAB, show A = A - K + K from (Nat.sub_add_cancel hAK).symm]
    exact phase45_r2 (A - K) B K (by omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 0⟩) (by execute fm 4)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A B, q = ⟨A + 1, B, 0, 0, 0⟩ ∧ B ≤ 2 * A + 1)
  · intro c ⟨A, B, hq, hBA⟩; subst hq
    exact ⟨⟨2 * A + B + 3, 2 * A + 3 * B, 0, 0, 0⟩,
      ⟨2 * A + B + 2, 2 * A + 3 * B, rfl, by omega⟩,
      main_trans A B hBA⟩
  · exact ⟨2, 0, rfl, by omega⟩

end Sz22_2003_unofficial_1389
