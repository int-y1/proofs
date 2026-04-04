import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1970: [99/35, 2/5, 25/6, 7/11, 275/2]

Vector representation:
```
 0  2 -1 -1  1
 1  0 -1  0  0
-1 -1  2  0  0
 0  0  0  1 -1
-1  0  2  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1970

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | _ => none

theorem e_to_d : ∀ k, ⟨a, 0, 0, d, e + k⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing d e
  · exists 0
  · rw [Nat.add_succ e k]; step fm
    apply stepStar_trans (ih (d := d + 1)); ring_nf; finish

theorem drain : ∀ k, ⟨a + 1, b + k, 0, 0, e⟩ [fm]⊢* ⟨a + 1 + k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih generalizing a b
  · exists 0
  · rw [Nat.add_succ b k]; step fm; step fm; step fm
    apply stepStar_trans (ih (a := a + 1)); ring_nf; finish

-- One R1R1R3 cycle: (a+2, b, 2, d+2, e) →* (a+1, b+3, 2, d, e+2)
-- Iterated j times.
theorem r1r1r3_chain : ∀ j, ⟨a + 1 + j, b, 2, d + 2 * j, e⟩ [fm]⊢*
    ⟨a + 1, b + 3 * j, 2, d, e + 2 * j⟩ := by
  intro j; induction' j with j ih generalizing a b d e
  · exists 0
  · rw [show d + 2 * (j + 1) = (d + 2 * j + 1) + 1 from by ring,
        show a + 1 + (j + 1) = (a + 1 + j) + 1 from by ring]
    step fm; step fm
    rw [show (a + 1 + j) + 1 = (a + j + 1) + 1 from by ring]
    step fm
    rw [show a + j + 1 = a + 1 + j from by ring,
        show e + 1 + 1 = e + 2 from by ring]
    apply stepStar_trans (ih (a := a) (b := b + 3) (d := d) (e := e + 2))
    ring_nf; finish

theorem main_trans_e0 : ⟨a + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 2, 0, 0, 0, 1⟩ := by
  execute fm 3

-- For odd e = 2k+1: (a+2k+2, 0, 0, 0, 2k+1) ⊢⁺ (a+4k+4, 0, 0, 0, 2k+2)
theorem main_trans_odd : ⟨a + 2 * k + 2, 0, 0, 0, 2 * k + 1⟩ [fm]⊢⁺
    ⟨a + 4 * k + 4, 0, 0, 0, 2 * k + 2⟩ := by
  -- e_to_d: (a+2k+2, 0, 0, 0, 0+(2k+1)) →* (a+2k+2, 0, 0, 0+(2k+1), 0)
  -- = (a+2k+2, 0, 0, 2k+1, 0)
  have h1 : ⟨a + 2 * k + 2, 0, 0, 0, 2 * k + 1⟩ [fm]⊢*
      ⟨a + 2 * k + 2, 0, 0, 2 * k + 1, 0⟩ := by
    rw [show 2 * k + 1 = 0 + (2 * k + 1) from by ring]
    exact e_to_d (2 * k + 1) (a := a + 2 * k + 2) (d := 0) (e := 0)
  -- R5: (a+2k+2, 0, 0, 2k+1, 0) → (a+2k+1, 0, 2, 2k+1, 1)
  have h2 : ⟨a + 2 * k + 2, 0, 0, 2 * k + 1, 0⟩ [fm]⊢
      ⟨a + 2 * k + 1, 0, 2, 2 * k + 1, 1⟩ := by
    rw [show a + 2 * k + 2 = (a + 2 * k + 1) + 1 from by ring]; simp [fm]
  -- Opening: R1R1R3(k) + R1 + R2
  have h3 : ⟨a + 2 * k + 1, 0, 2, 2 * k + 1, 1⟩ [fm]⊢*
      ⟨a + k + 1, 3 * k, 2, 1, 2 * k + 1⟩ := by
    rw [show a + 2 * k + 1 = (a + k) + 1 + k from by ring,
        show 2 * k + 1 = 1 + 2 * k from by ring]
    apply stepStar_trans (r1r1r3_chain k (a := a + k) (b := 0) (d := 1) (e := 1))
    rw [show 1 + 2 * k = 2 * k + 1 from by ring]; ring_nf; finish
  -- R1: (a+k+1, 3k, 2, 1, 2k+1) → (a+k+1, 3k+2, 1, 0, 2k+2)
  have h4 : ⟨a + k + 1, 3 * k, 2, 1, 2 * k + 1⟩ [fm]⊢*
      ⟨a + k + 2, 3 * k + 2, 0, 0, 2 * k + 2⟩ := by
    step fm; step fm; finish
  -- Drain
  have h5 : ⟨a + k + 2, 3 * k + 2, 0, 0, 2 * k + 2⟩ [fm]⊢*
      ⟨a + 4 * k + 4, 0, 0, 0, 2 * k + 2⟩ := by
    rw [show a + k + 2 = (a + k + 1) + 1 from by ring,
        show 3 * k + 2 = 0 + (3 * k + 2) from by ring]
    apply stepStar_trans (drain (3 * k + 2) (a := a + k + 1) (b := 0) (e := 2 * k + 2))
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus h1
    (step_stepStar_stepPlus h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

-- For even e = 2(k+1): (a+2k+3, 0, 0, 0, 2(k+1)) ⊢⁺ (a+4k+6, 0, 0, 0, 2k+3)
theorem main_trans_even : ⟨a + 2 * k + 3, 0, 0, 0, 2 * (k + 1)⟩ [fm]⊢⁺
    ⟨a + 4 * k + 6, 0, 0, 0, 2 * k + 3⟩ := by
  have h1 : ⟨a + 2 * k + 3, 0, 0, 0, 2 * (k + 1)⟩ [fm]⊢*
      ⟨a + 2 * k + 3, 0, 0, 2 * (k + 1), 0⟩ := by
    rw [show 2 * (k + 1) = 0 + 2 * (k + 1) from by ring]
    exact e_to_d (2 * (k + 1)) (a := a + 2 * k + 3) (d := 0) (e := 0)
  have h2 : ⟨a + 2 * k + 3, 0, 0, 2 * (k + 1), 0⟩ [fm]⊢
      ⟨a + 2 * k + 2, 0, 2, 2 * (k + 1), 1⟩ := by
    rw [show a + 2 * k + 3 = (a + 2 * k + 2) + 1 from by ring]; simp [fm]
  have h3 : ⟨a + 2 * k + 2, 0, 2, 2 * (k + 1), 1⟩ [fm]⊢*
      ⟨a + k + 2, 3 * k, 2, 2, 2 * k + 1⟩ := by
    rw [show a + 2 * k + 2 = (a + k + 1) + 1 + k from by ring,
        show 2 * (k + 1) = 2 + 2 * k from by ring]
    apply stepStar_trans (r1r1r3_chain k (a := a + k + 1) (b := 0) (d := 2) (e := 1))
    rw [show 1 + 2 * k = 2 * k + 1 from by ring]; ring_nf; finish
  -- R1R1: (a+k+2, 3k, 2, 2, 2k+1) → R1 → R1 → (a+k+2, 3k+4, 0, 0, 2k+3)
  have h4 : ⟨a + k + 2, 3 * k, 2, 2, 2 * k + 1⟩ [fm]⊢*
      ⟨a + k + 2, 3 * k + 4, 0, 0, 2 * k + 3⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by ring]; step fm; step fm; finish
  have h5 : ⟨a + k + 2, 3 * k + 4, 0, 0, 2 * k + 3⟩ [fm]⊢*
      ⟨a + 4 * k + 6, 0, 0, 0, 2 * k + 3⟩ := by
    rw [show a + k + 2 = (a + k + 1) + 1 from by ring,
        show 3 * k + 4 = 0 + (3 * k + 4) from by ring]
    apply stepStar_trans (drain (3 * k + 4) (a := a + k + 1) (b := 0) (e := 2 * k + 3))
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus h1
    (step_stepStar_stepPlus h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨a + e + 1, 0, 0, 0, e⟩) ⟨0, 0⟩
  intro ⟨a, e⟩
  rcases e with _ | e
  · -- e = 0
    refine ⟨⟨a, 1⟩, ?_⟩
    show ⟨a + 0 + 1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 1 + 1, 0, 0, 0, 1⟩
    rw [show a + 0 + 1 = a + 1 from by ring, show a + 1 + 1 = a + 2 from by ring]
    exact main_trans_e0
  · rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- e = 2k, e+1 = 2k+1
      subst hk
      refine ⟨⟨a + 2 * k + 1, 2 * k + 2⟩, ?_⟩
      show ⟨a + (k + k + 1) + 1, 0, 0, 0, k + k + 1⟩ [fm]⊢⁺
        ⟨(a + 2 * k + 1) + (2 * k + 2) + 1, 0, 0, 0, 2 * k + 2⟩
      rw [show a + (k + k + 1) + 1 = a + 2 * k + 2 from by ring,
          show k + k + 1 = 2 * k + 1 from by ring,
          show (a + 2 * k + 1) + (2 * k + 2) + 1 = a + 4 * k + 4 from by ring]
      exact main_trans_odd
    · -- e = 2k+1, e+1 = 2(k+1)
      subst hk
      refine ⟨⟨a + 2 * k + 2, 2 * k + 3⟩, ?_⟩
      show ⟨a + (2 * k + 1 + 1) + 1, 0, 0, 0, 2 * k + 1 + 1⟩ [fm]⊢⁺
        ⟨(a + 2 * k + 2) + (2 * k + 3) + 1, 0, 0, 0, 2 * k + 3⟩
      rw [show a + (2 * k + 1 + 1) + 1 = a + 2 * k + 3 from by ring,
          show 2 * k + 1 + 1 = 2 * (k + 1) from by ring,
          show (a + 2 * k + 2) + (2 * k + 3) + 1 = a + 4 * k + 6 from by ring]
      exact main_trans_even

end Sz22_2003_unofficial_1970
