import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #327: [18/35, 5/33, 49/3, 1331/2, 3/11]

Vector representation:
```
 1  2 -1 -1  0
 0 -1  1  0 -1
 0 -1  0  2  0
-1  0  0  0  3
 0  1  0  0 -1
```

This Fractran program doesn't halt. The canonical state is (a, 0, 0, d, 0) with a >= 1
and 2*d + 1 >= 3*a. Each step maps (a, 0, 0, d, 0) to (3*a - 1, 0, 0, d + 3*a + 1, 0).

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_327

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

theorem r4_loop : ∀ k a d e,
    ⟨a + k, 0, 0, d, e⟩ [fm]⊢* (⟨a, 0, 0, d, e + 3 * k⟩ : Q) := by
  intro k; induction k with
  | zero => intro a d e; exists 0
  | succ k ih =>
    intro a d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + 3 * (k + 1) = (e + 3) + 3 * k from by ring]
    step fm; exact ih a d (e + 3)

theorem r12_loop : ∀ k j d e,
    ⟨j, j, 1, d + k, e + k⟩ [fm]⊢* (⟨j + k, j + k, 1, d, e⟩ : Q) := by
  intro k; induction k with
  | zero => intro j d e; exists 0
  | succ k ih =>
    intro j d e
    rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    rw [show j + (k + 1) = (j + 1) + k from by ring]
    exact ih (j + 1) d e

theorem r3_loop : ∀ k a b d,
    ⟨a, b + k, 0, d, 0⟩ [fm]⊢* (⟨a, b, 0, d + 2 * k, 0⟩ : Q) := by
  intro k; induction k with
  | zero => intro a b d; exists 0
  | succ k ih =>
    intro a b d
    rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2) + 2 * k from by ring]
    step fm; exact ih a b (d + 2)

theorem r2_drain : ∀ k a b c,
    ⟨a, b + k, c, 0, k⟩ [fm]⊢* (⟨a, b, c + k, 0, 0⟩ : Q) := by
  intro k; induction k with
  | zero => intro a b c; exists 0
  | succ k ih =>
    intro a b c
    rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show c + (k + 1) = (c + 1) + k from by ring]
    step fm; exact ih a b (c + 1)

theorem r3r1_loop : ∀ k a b c,
    ⟨a, b + 1, c + 2 * k, 0, 0⟩ [fm]⊢* (⟨a + 2 * k, b + 1 + 3 * k, c, 0, 0⟩ : Q) := by
  intro k; induction k with
  | zero => intro a b c; exists 0
  | succ k ih =>
    intro a b c
    rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    rw [show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show b + 1 + 3 * (k + 1) = (b + 3) + 1 + 3 * k from by ring]
    exact ih (a + 2) (b + 3) c

-- Phase 1+2: (a'+1, 0, 0, d, 0) →⁺ (0, 0, 1, d, 3*a'+1)
theorem phase12 (a' d : ℕ) :
    ⟨a' + 1, 0, 0, d, 0⟩ [fm]⊢⁺ (⟨0, 0, 1, d, 3 * a' + 1⟩ : Q) := by
  rw [show a' + 1 = 0 + (a' + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (h₁ := r4_loop (a' + 1) 0 d 0)
  rw [show (0 : ℕ) + 3 * (a' + 1) = 3 * a' + 2 + 1 from by ring]
  step fm
  rw [show 3 * a' + 2 = 3 * a' + 1 + 1 from by ring]
  step fm
  exact ⟨0, rfl⟩

-- Case A: e runs out first in the r1+r2 loop (d >= 3a'+2, i.e., d_extra >= 1)
-- After r12_loop(3a'+1): (3a'+1, 3a'+1, 1, d_extra, 0) with d_extra >= 1
-- r1: (3a'+2, 3a'+3, 0, d_extra-1, 0). r3_loop(3a'+3): (3a'+2, 0, 0, d_extra-1+2*(3a'+3), 0)
-- = (3a'+2, 0, 0, d_extra + 6a' + 5, 0)
theorem mid_case_a (a' d_extra : ℕ) :
    ⟨0, 0, 1, (d_extra + 1) + (3 * a' + 1), 3 * a' + 1⟩ [fm]⊢*
    (⟨3 * a' + 2, 0, 0, (d_extra + 1) + 6 * a' + 5, 0⟩ : Q) := by
  have h1 := r12_loop (3 * a' + 1) 0 (d_extra + 1) 0
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  step fm
  rw [show 3 * a' + 1 + 1 = 3 * a' + 2 from by ring,
      show 3 * a' + 1 + 2 = 0 + (3 * a' + 3) from by ring]
  apply stepStar_trans (r3_loop (3 * a' + 3) (3 * a' + 2) 0 d_extra)
  rw [show d_extra + 2 * (3 * a' + 3) = (d_extra + 1) + 6 * a' + 5 from by ring]
  exists 0

-- Case B: d runs out first (d <= 3a')
-- After r12_loop(d): (d, d, 1, 0, el) where el = 3a'+1-d
-- r2_drain(el): (d, bl, 1+el, 0, 0) = (d, bl, 3a'+2-d, 0, 0) where bl = d - el = 2d-(3a'+1)
-- Then r3r1_loop + possible final steps + r3_loop
theorem mid_case_b (a' d : ℕ) (hd : 2 * d + 1 ≥ 3 * a' + 3) (hlt : d ≤ 3 * a' + 1) :
    ⟨d, d, 1, 0, 3 * a' + 1 - d⟩ [fm]⊢*
    (⟨3 * a' + 2, 0, 0, d + 3 * a' + 4, 0⟩ : Q) := by
  set el := 3 * a' + 1 - d
  set bl := 2 * d - (3 * a' + 1)
  have hbl_pos : bl ≥ 1 := by omega
  have hd_decomp : d = bl + el := by omega
  -- r2_drain(el): (d, d, 1, 0, el) → (d, bl, 1+el, 0, 0)
  -- Rewrite second d to bl + el for r2_drain
  have h_r2 := r2_drain el d bl 1
  -- h_r2 : (d, bl + el, 1, 0, el) ⊢* (d, bl, 1 + el, 0, 0)
  rw [show bl + el = d from by omega] at h_r2
  apply stepStar_trans h_r2
  rw [show 1 + el = 3 * a' + 2 - d from by omega]
  -- Now at (d, bl, 3a'+2-d, 0, 0)
  set C := 3 * a' + 2 - d
  have hC_pos : C ≥ 1 := by omega
  by_cases hparity : C % 2 = 0
  · -- C is even: C = 2m
    obtain ⟨m, hm⟩ : ∃ m, C = 2 * m := ⟨C / 2, by omega⟩
    rw [hm]
    -- Goal: (d, bl, 2*m, 0, 0) ⊢* ... Need to set up for r3r1_loop with c=0, k=m
    rw [show (2 : ℕ) * m = 0 + 2 * m from by ring,
        show bl = (bl - 1) + 1 from by omega]
    apply stepStar_trans (r3r1_loop m d (bl - 1) 0)
    rw [show d + 2 * m = 3 * a' + 2 from by omega,
        show bl - 1 + 1 + 3 * m = (d + 3 * a' + 4) / 2 from by omega,
        show (d + 3 * a' + 4) / 2 = 0 + (d + 3 * a' + 4) / 2 from by ring]
    apply stepStar_trans (r3_loop ((d + 3 * a' + 4) / 2) (3 * a' + 2) 0 0)
    rw [show 0 + 2 * ((d + 3 * a' + 4) / 2) = d + 3 * a' + 4 from by omega]
    exists 0
  · -- C is odd: C = 2m+1
    obtain ⟨m, hm⟩ : ∃ m, C = 2 * m + 1 := ⟨C / 2, by omega⟩
    rw [hm, show (2 : ℕ) * m + 1 = 1 + 2 * m from by ring,
        show bl = (bl - 1) + 1 from by omega]
    apply stepStar_trans (r3r1_loop m d (bl - 1) 1)
    -- After r3r1_loop: (d+2m, bl-1+1+3m, 1, 0, 0)
    rw [show d + 2 * m = 3 * a' + 1 from by omega,
        show bl - 1 + 1 + 3 * m = ((d + 3 * a' + 1) / 2 - 1) + 1 from by omega]
    -- r3 + r1
    step fm; step fm
    rw [show 3 * a' + 1 + 1 = 3 * a' + 2 from by ring,
        show (d + 3 * a' + 1) / 2 - 1 + 2 = 0 + ((d + 3 * a' + 1) / 2 + 1) from by omega]
    apply stepStar_trans (r3_loop ((d + 3 * a' + 1) / 2 + 1) (3 * a' + 2) 0 1)
    rw [show 1 + 2 * ((d + 3 * a' + 1) / 2 + 1) = d + 3 * a' + 4 from by omega]
    exists 0

-- Combined middle
theorem mid (a' d : ℕ) (hd : 2 * d + 1 ≥ 3 * a' + 3) :
    ⟨0, 0, 1, d, 3 * a' + 1⟩ [fm]⊢*
    (⟨3 * a' + 2, 0, 0, d + 3 * a' + 4, 0⟩ : Q) := by
  by_cases hcase : d ≥ 3 * a' + 2
  · -- Case A: d >= 3a'+2
    have h := mid_case_a a' (d - (3 * a' + 2))
    rw [show d - (3 * a' + 2) + 1 + (3 * a' + 1) = d from by omega,
        show d - (3 * a' + 2) + 1 + 6 * a' + 5 = d + 3 * a' + 4 from by omega] at h
    exact h
  · -- Case B: d <= 3a'+1
    push_neg at hcase
    have hlt : d ≤ 3 * a' + 1 := by omega
    have h1 := r12_loop d 0 0 (3 * a' + 1 - d)
    rw [show 0 + d = d from by ring,
        show 3 * a' + 1 - d + d = 3 * a' + 1 from by omega] at h1
    exact stepStar_trans h1 (mid_case_b a' d hd hlt)

-- Main transition
theorem main_trans (a' d : ℕ) (hd : 2 * d + 1 ≥ 3 * a' + 3) :
    ⟨a' + 1, 0, 0, d, 0⟩ [fm]⊢⁺ (⟨3 * a' + 2, 0, 0, d + 3 * a' + 4, 0⟩ : Q) := by
  exact stepPlus_stepStar_stepPlus (phase12 a' d) (mid a' d hd)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 5, 0⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a' d : ℕ, 2 * d + 1 ≥ 3 * a' + 3 ∧ q = (⟨a' + 1, 0, 0, d, 0⟩ : Q))
  · intro c ⟨a', d, hd, hq⟩
    subst hq
    exact ⟨⟨3 * a' + 2, 0, 0, d + 3 * a' + 4, 0⟩,
      ⟨3 * a' + 1, d + 3 * a' + 4, by omega, by ring_nf⟩,
      main_trans a' d hd⟩
  · exact ⟨0, 5, by omega, by ring_nf⟩

end Sz22_2003_unofficial_327
