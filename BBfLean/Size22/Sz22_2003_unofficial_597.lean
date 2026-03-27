import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #597: [35/6, 121/2, 4/55, 3/7, 14/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  2
 2  0 -1  0 -1
 0  1  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_597

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R4 repeated
theorem d_to_b : ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  have many_step : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k h <;> intro b
    · exists 0
    rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (h _); ring_nf; finish
  exact many_step k b

-- Interleave rounds
theorem interleave_round : ∀ k c d, ⟨1, b+2*k, c, d, e+k⟩ [fm]⊢* ⟨1, b, c+k, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _); ring_nf; finish

-- R3R2R2 drain
theorem r3r2r2_drain : ⟨0, 0, c+k, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d, e+4*k⟩ := by
  have many_step : ∀ k c e, ⟨0, 0, c+k, d, e+k⟩ [fm]⊢* ⟨0, 0, c, d, e+4*k⟩ := by
    intro k; induction' k with k h <;> intro c e
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    rw [show e + k + 2 + 2 = (e + 4) + k from by ring]
    apply stepStar_trans (h c (e + 4)); ring_nf; finish
  exact many_step k c e

-- Even: (0, 0, 0, 2*k, 2*k+f+1) →⁺ (0, 0, 0, 2*k+1, 4*k+f+2)
theorem main_even : ⟨0, 0, 0, 2*k, 2*k+f+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*k+1, 4*k+f+2⟩ := by
  have hA := d_to_b (b := 0) (d := 0) (k := 2*k) (e := 2*k+f+1)
  simp only [Nat.zero_add] at hA
  have hB : ⟨0, 2*k, 0, 0, 2*k+f+1⟩ [fm]⊢⁺ ⟨1, 2*k, 0, 1, 2*k+f⟩ := by
    rw [show 2*k+f+1 = (2*k+f)+1 from by ring]; step fm; finish
  have hC := interleave_round (b := 0) (e := k+f) k 0 1
  simp only [Nat.zero_add] at hC
  -- hC : (1, 2*k, 0, 1, k+f+k) ⊢* (1, 0, k, 1+2*k, k+f)
  have hD : ⟨1, 0, k, 1+2*k, k+f⟩ [fm]⊢⁺ ⟨0, 0, k, 1+2*k, k+f+2⟩ := by
    step fm; finish
  have hE := r3r2r2_drain (c := 0) (d := 1+2*k) (e := f+2) (k := k)
  simp only [Nat.zero_add] at hE
  -- hE : (0, 0, k, 1+2*k, f+2+k) ⊢* (0, 0, 0, 1+2*k, f+2+4*k)
  apply stepStar_stepPlus_stepPlus hA
  apply stepPlus_stepStar_stepPlus hB
  rw [show 2*k+f = k+f+k from by ring]
  apply stepStar_trans hC
  apply stepStar_trans (stepPlus_stepStar hD)
  rw [show k+f+2 = f+2+k from by ring]
  apply stepStar_trans hE
  ring_nf; finish

-- Odd: (0, 0, 0, 2*k+1, 2*k+f+2) →⁺ (0, 0, 0, 2*k+2, 4*k+f+4)
theorem main_odd : ⟨0, 0, 0, 2*k+1, 2*k+f+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*k+2, 4*k+f+4⟩ := by
  have hA := d_to_b (b := 0) (d := 0) (k := 2*k+1) (e := 2*k+f+2)
  simp only [Nat.zero_add] at hA
  have hB : ⟨0, 2*k+1, 0, 0, 2*k+f+2⟩ [fm]⊢⁺ ⟨1, 2*k+1, 0, 1, 2*k+f+1⟩ := by
    rw [show 2*k+f+2 = (2*k+f+1)+1 from by ring]; step fm; finish
  have hC := interleave_round (b := 1) (e := k+f+1) k 0 1
  simp only [Nat.zero_add] at hC
  -- hC : (1, 1+2*k, 0, 1, k+f+1+k) ⊢* (1, 1, k, 1+2*k, k+f+1)
  have hD : ⟨1, 1, k, 1+2*k, k+f+1⟩ [fm]⊢⁺ ⟨0, 0, k+1, 1+2*k+1, k+f+1⟩ := by
    rw [show 1+2*k = (2*k)+1 from by ring]; step fm; finish
  have hE := r3r2r2_drain (c := 0) (d := 1+2*k+1) (e := f) (k := k+1)
  simp only [Nat.zero_add] at hE
  -- hE : (0, 0, k+1, 1+2*k+1, f+(k+1)) ⊢* (0, 0, 0, 1+2*k+1, f+4*(k+1))
  apply stepStar_stepPlus_stepPlus hA
  apply stepPlus_stepStar_stepPlus hB
  rw [show 2*k+f+1 = k+f+1+k from by ring, show 2*k+1 = 1+2*k from by ring]
  apply stepStar_trans hC
  apply stepStar_trans (stepPlus_stepStar hD)
  rw [show k+f+1 = f+(k+1) from by ring]
  apply stepStar_trans hE
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n f, q = ⟨0, 0, 0, n+1, n+f+2⟩)
  · intro c ⟨n, f, hq⟩; subst hq
    rcases Nat.even_or_odd (n + 1) with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK
      rw [show n + 1 = 2*K from hK, show n + f + 2 = 2*K + f + 1 from by omega]
      exact ⟨⟨0, 0, 0, 2*K+1, 4*K+f+2⟩, ⟨2*K, 2*K+f, by ring_nf⟩, main_even⟩
    · rw [show n + 1 = 2*K+1 from hK, show n + f + 2 = 2*K + f + 2 from by omega]
      exact ⟨⟨0, 0, 0, 2*K+2, 4*K+f+4⟩, ⟨2*K+1, 2*K+f+1, by ring_nf⟩, main_odd⟩
  · exact ⟨0, 1, rfl⟩

end Sz22_2003_unofficial_597
