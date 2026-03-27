import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #628: [35/6, 143/2, 4/55, 3/7, 15/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 0  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_628

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

-- R4 repeated: drain d to b
theorem d_to_b : ∀ k b, ⟨(0:ℕ), b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by omega]
  step fm; apply stepStar_trans (h (b + 1)); ring_nf; finish

-- R1R1R3 chain: three-step rounds consuming b by 2
theorem r1r1r3_chain : ∀ k b C D E F, ⟨(2:ℕ), b + 2 * k, C, D, E + k, F⟩ [fm]⊢*
    ⟨2, b, C + k, D + 2 * k, E, F⟩ := by
  intro k; induction' k with k h <;> intro b C D E F
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h b (C + 1) (D + 2) E F); ring_nf; finish

-- R1R2R3: handle remaining b=1
theorem b1_step (C D E F : ℕ) : ⟨(2:ℕ), 1, C, D, E, F⟩ [fm]⊢* ⟨2, 0, C, D+1, E, F+1⟩ := by
  step fm; step fm; step fm; finish

-- R2R2R3 chain: drain c when b=0
theorem r2r2r3_chain : ∀ k c D e f, ⟨(2:ℕ), 0, c + k, D, e, f⟩ [fm]⊢*
    ⟨2, 0, c, D, e + k, f + 2 * k⟩ := by
  intro k; induction' k with k h <;> intro c D e f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm
  rw [show f + 1 + 1 = f + 2 from by ring]
  apply stepStar_trans (h c D (e + 1) (f + 2)); ring_nf; finish

-- Final two R2 steps
theorem final_r2r2 (D e f : ℕ) :
    ⟨(2:ℕ), 0, 0, D, e, f⟩ [fm]⊢* ⟨0, 0, 0, D, e+2, f+2⟩ := by
  step fm; step fm; ring_nf; finish

-- Main transition for n even: n = 2*m, n+1 = 2*m+1, n+2 = 2*(m+1)
theorem main_trans_even (m g : ℕ) :
    ⟨(0:ℕ), 0, 0, 2*m+1, 2*m+2, g+3⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2*m+2, 2*m+3, g+2*m+6⟩ := by
  -- R4 step for ⊢⁺
  rw [show 2*m+1 = 0+(2*m+1) from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  simp only [Nat.add_eq, Nat.zero_add]
  -- d_to_b
  have p1 : ⟨(0:ℕ), 1, 0, 2*m, 2*m+2, g+3⟩ [fm]⊢*
            ⟨0, 2*m+1, 0, 0, 2*m+2, g+3⟩ := by
    have h := d_to_b (d := 0) (e := 2*m+2) (f := g+3) (2*m) 1
    simp only [Nat.zero_add] at h
    rw [show (1:ℕ)+2*m = 2*m+1 from by ring] at h; exact h
  apply stepStar_trans p1
  -- R5 + R3
  have p2 : ⟨(0:ℕ), 2*m+1, 0, 0, 2*m+2, g+3⟩ [fm]⊢*
            ⟨2, 2*m+2, 0, 0, 2*m+1, g+2⟩ := by
    rw [show 2*m+1 = 0+(2*m+1) from by ring]
    step fm; simp only [Nat.zero_add]; step fm; ring_nf; finish
  apply stepStar_trans p2
  -- r1r1r3_chain with k=m+1, b=0
  have p3 : ⟨(2:ℕ), 2*m+2, 0, 0, 2*m+1, g+2⟩ [fm]⊢*
            ⟨2, 0, m+1, 2*m+2, m, g+2⟩ := by
    rw [show 2*m+2 = 0+2*(m+1) from by ring,
        show 2*m+1 = m+(m+1) from by ring]
    have h := r1r1r3_chain (m+1) 0 0 0 m (g+2)
    simp only [Nat.zero_add] at h
    convert h using 2; all_goals ring_nf
  apply stepStar_trans p3
  -- r2r2r3_chain with k=m+1
  have p4 : ⟨(2:ℕ), 0, m+1, 2*m+2, m, g+2⟩ [fm]⊢*
            ⟨2, 0, 0, 2*m+2, 2*m+1, g+2*m+4⟩ := by
    rw [show m+1 = 0+(m+1) from by ring]
    have h := r2r2r3_chain (m+1) 0 (2*m+2) m (g+2)
    simp only [Nat.zero_add] at h
    convert h using 2; all_goals ring_nf
  apply stepStar_trans p4
  -- final R2, R2
  have p5 := final_r2r2 (2*m+2) (2*m+1) (g+2*m+4)
  convert p5 using 2

-- Main transition for n odd: n = 2*m+1, n+1 = 2*m+2, n+2 = 2*m+3
theorem main_trans_odd (m g : ℕ) :
    ⟨(0:ℕ), 0, 0, 2*m+2, 2*m+3, g+3⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2*m+3, 2*m+4, g+2*m+7⟩ := by
  -- R4 step for ⊢⁺
  rw [show 2*m+2 = 0+(2*m+2) from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  simp only [Nat.add_eq, Nat.zero_add]
  -- d_to_b
  have p1 : ⟨(0:ℕ), 1, 0, 2*m+1, 2*m+3, g+3⟩ [fm]⊢*
            ⟨0, 2*m+2, 0, 0, 2*m+3, g+3⟩ := by
    have h := d_to_b (d := 0) (e := 2*m+3) (f := g+3) (2*m+1) 1
    simp only [Nat.zero_add] at h
    convert h using 2; all_goals ring_nf
  apply stepStar_trans p1
  -- R5 + R3
  have p2 : ⟨(0:ℕ), 2*m+2, 0, 0, 2*m+3, g+3⟩ [fm]⊢*
            ⟨2, 2*m+3, 0, 0, 2*m+2, g+2⟩ := by
    rw [show 2*m+2 = 0+(2*m+2) from by ring]
    step fm; simp only [Nat.zero_add]; step fm; ring_nf; finish
  apply stepStar_trans p2
  -- r1r1r3_chain with k=m+1, b=1
  have p3 : ⟨(2:ℕ), 2*m+3, 0, 0, 2*m+2, g+2⟩ [fm]⊢*
            ⟨2, 1, m+1, 2*m+2, m+1, g+2⟩ := by
    rw [show 2*m+3 = 1+2*(m+1) from by ring,
        show 2*m+2 = (m+1)+(m+1) from by ring]
    have h := r1r1r3_chain (m+1) 1 0 0 (m+1) (g+2)
    simp only [Nat.zero_add] at h
    convert h using 2; all_goals ring_nf
  apply stepStar_trans p3
  -- b1_step
  have p4 : ⟨(2:ℕ), 1, m+1, 2*m+2, m+1, g+2⟩ [fm]⊢*
            ⟨2, 0, m+1, 2*m+3, m+1, g+3⟩ := by
    exact b1_step (m+1) (2*m+2) (m+1) (g+2)
  apply stepStar_trans p4
  -- r2r2r3_chain with k=m+1
  have p5 : ⟨(2:ℕ), 0, m+1, 2*m+3, m+1, g+3⟩ [fm]⊢*
            ⟨2, 0, 0, 2*m+3, 2*m+2, g+2*m+5⟩ := by
    rw [show m+1 = 0+(m+1) from by ring]
    have h := r2r2r3_chain (m+1) 0 (2*m+3) (m+1) (g+3)
    simp only [Nat.zero_add] at h
    convert h using 2; all_goals ring_nf
  apply stepStar_trans p5
  -- final R2, R2
  have p6 := final_r2r2 (2*m+3) (2*m+2) (g+2*m+5)
  convert p6 using 2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2, 3⟩) (by execute fm 8)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n g, q = ⟨0, 0, 0, n+1, n+2, g+3⟩)
  · intro c ⟨n, g, hq⟩; subst hq
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm
      refine ⟨⟨0, 0, 0, 2*m+2, 2*m+3, g+2*m+6⟩,
        ⟨2*m+1, g+2*m+3, by ring_nf⟩, ?_⟩
      have := main_trans_even m g
      convert this using 2; all_goals ring_nf
    · subst hm
      refine ⟨⟨0, 0, 0, 2*m+3, 2*m+4, g+2*m+7⟩,
        ⟨2*m+2, g+2*m+4, by ring_nf⟩, ?_⟩
      have := main_trans_odd m g
      convert this using 2
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_628
