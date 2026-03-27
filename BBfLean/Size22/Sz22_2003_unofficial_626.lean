import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# sz22_2003_unofficial #626: [35/6, 143/2, 4/55, 3/7, 12/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 2  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_626

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+2, b+1, c, d, e, f⟩
  | _ => none

-- R4 repeated: drain d to b
theorem d_to_b : ∀ k b, ⟨(0:ℕ), b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by omega]
  step fm; apply stepStar_trans (h (b + 1)); ring_nf; finish

-- R1, R1, R3 chain
theorem r1r1r3_chain : ∀ k b C D E F, ⟨(2:ℕ), b + 2 * k, C, D, E + k, F⟩ [fm]⊢*
    ⟨2, b, C + k, D + 2 * k, E, F⟩ := by
  intro k; induction' k with k h <;> intro b C D E F
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h b (C + 1) (D + 2) E F); ring_nf; finish

-- Drain with a=0: R3, R2, R2 chain
theorem drain_a0 : ∀ k c D e f, ⟨(0:ℕ), 0, c + k, D, e + k, f⟩ [fm]⊢*
    ⟨0, 0, c, D, e + 2 * k, f + 2 * k⟩ := by
  intro k; induction' k with k h <;> intro c D e f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  rw [show e + k + 1 + 1 = (e + 2) + k from by ring,
      show f + 1 + 1 = f + 2 from by ring]
  apply stepStar_trans (h c D (e + 2) (f + 2)); ring_nf; finish

-- Drain with a=2: R2, R2, R3 chain
theorem drain_a2 : ∀ k c D e f, ⟨(2:ℕ), 0, c + k, D, e, f⟩ [fm]⊢*
    ⟨2, 0, c, D, e + k, f + 2 * k⟩ := by
  intro k; induction' k with k h <;> intro c D e f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm
  rw [show f + 1 + 1 = f + 2 from by ring]
  apply stepStar_trans (h c D (e + 1) (f + 2)); ring_nf; finish

-- Final R2, R2
theorem final_r2r2 (D e f : ℕ) :
    ⟨(2:ℕ), 0, 0, D, e, f⟩ [fm]⊢* ⟨0, 0, 0, D, e + 2, f + 2⟩ := by
  step fm; step fm; ring_nf; finish

-- Even transition: n = 2*m
theorem even_trans (m g : ℕ) :
    ⟨(0:ℕ), 0, 0, 2*m, 4*m+1, g+1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2*m+1, 4*m+3, g+2*m+3⟩ := by
  rcases m with _ | m
  · execute fm 6
  · -- R4 step for ⊢⁺
    rw [show 2*(m+1) = 2*m+1+1 from by omega]
    apply step_stepStar_stepPlus (by unfold fm; rfl)
    simp only [Nat.zero_add]
    rw [show 2*m+1+1+1 = 2*m+3 from by ring,
        show 4*(m+1)+3 = 4*m+7 from by ring,
        show g+(2*m+1+1)+3 = g+2*m+5 from by ring,
        show 4*(m+1)+1 = 4*m+5 from by ring]
    -- d_to_b
    have p1 : ⟨(0:ℕ), 1, 0, 2*m+1, 4*m+5, g+1⟩ [fm]⊢*
              ⟨0, 2*m+2, 0, 0, 4*m+5, g+1⟩ := by
      have h := d_to_b (d := 0) (e := 4*m+5) (f := g+1) (2*m+1) 1
      simp only [Nat.zero_add] at h
      rw [show (1:ℕ)+(2*m+1) = 2*m+2 from by ring] at h; exact h
    apply stepStar_trans p1
    -- R5
    have p2 : ⟨(0:ℕ), 2*m+2, 0, 0, 4*m+5, g+1⟩ [fm]⊢*
              ⟨2, 2*m+3, 0, 0, 4*m+5, g⟩ := by
      rw [show 2*m+2 = 0+(2*m+1+1) from by ring]
      step fm; simp only [Nat.zero_add]; ring_nf; finish
    apply stepStar_trans p2
    -- r1r1r3_chain
    have p3 : ⟨(2:ℕ), 2*m+3, 0, 0, 4*m+5, g⟩ [fm]⊢*
              ⟨2, 1, m+1, 2*m+2, 3*m+4, g⟩ := by
      rw [show 2*m+3 = 1+2*(m+1) from by ring,
          show 4*m+5 = (3*m+4)+(m+1) from by ring]
      have h := r1r1r3_chain (m+1) 1 0 0 (3*m+4) g
      simp only [Nat.zero_add] at h
      rw [show 2*(m+1) = 2*m+2 from by ring] at h; exact h
    apply stepStar_trans p3
    -- R1 + R2
    have p4 : ⟨(2:ℕ), 1, m+1, 2*m+2, 3*m+4, g⟩ [fm]⊢*
              ⟨0, 0, m+2, 2*m+3, 3*m+5, g+1⟩ := by
      rw [show m+1 = 0+(m+1) from by ring, show 2*m+2 = 0+(2*m+2) from by ring]
      step fm; simp only [Nat.zero_add]
      step fm; ring_nf; finish
    apply stepStar_trans p4
    -- drain_a0
    rw [show m+2 = 0+(m+2) from by ring,
        show 3*m+5 = (2*m+3)+(m+2) from by ring]
    have h := drain_a0 (m+2) 0 (2*m+3) (2*m+3) (g+1)
    simp only [Nat.zero_add] at h
    convert h using 2; ring_nf

-- Odd transition: n = 2*m + 1
theorem odd_trans (m g : ℕ) :
    ⟨(0:ℕ), 0, 0, 2*m+1, 4*m+3, g+1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2*m+2, 4*m+5, g+2*m+4⟩ := by
  -- R4 step for ⊢⁺
  rw [show 2*m+1 = 0+(2*m+1) from by ring]
  apply step_stepStar_stepPlus (by unfold fm; rfl)
  simp only [Nat.add_eq, Nat.zero_add]
  -- d_to_b
  have p1 : ⟨(0:ℕ), 1, 0, 2*m, 4*m+3, g+1⟩ [fm]⊢*
            ⟨0, 2*m+1, 0, 0, 4*m+3, g+1⟩ := by
    have h := d_to_b (d := 0) (e := 4*m+3) (f := g+1) (2*m) 1
    simp only [Nat.zero_add] at h
    rw [show (1:ℕ)+2*m = 2*m+1 from by ring] at h; exact h
  apply stepStar_trans p1
  -- R5
  have p2 : ⟨(0:ℕ), 2*m+1, 0, 0, 4*m+3, g+1⟩ [fm]⊢*
            ⟨2, 2*m+2, 0, 0, 4*m+3, g⟩ := by
    rw [show 2*m+1 = 0+(2*m+1) from by ring]
    step fm; simp only [Nat.zero_add]; ring_nf; finish
  apply stepStar_trans p2
  -- r1r1r3_chain
  have p3 : ⟨(2:ℕ), 2*m+2, 0, 0, 4*m+3, g⟩ [fm]⊢*
            ⟨2, 0, m+1, 2*m+2, 3*m+2, g⟩ := by
    rw [show 2*m+2 = 0+2*(m+1) from by ring,
        show 4*m+3 = (3*m+2)+(m+1) from by ring]
    have h := r1r1r3_chain (m+1) 0 0 0 (3*m+2) g
    simp only [Nat.zero_add] at h
    convert h using 2; ring
  apply stepStar_trans p3
  -- drain_a2
  have p4 : ⟨(2:ℕ), 0, m+1, 2*m+2, 3*m+2, g⟩ [fm]⊢*
            ⟨2, 0, 0, 2*m+2, 4*m+3, g+2*m+2⟩ := by
    rw [show m+1 = 0+(m+1) from by ring]
    have h := drain_a2 (m+1) 0 (2*m+2) (3*m+2) g
    simp only [Nat.zero_add] at h
    convert h using 2; ring
  apply stepStar_trans p4
  -- final R2, R2
  have p5 := final_r2r2 (2*m+2) (4*m+3) (g+2*m+2)
  convert p5 using 2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d f, q = ⟨0, 0, 0, d, 2*d+1, f⟩ ∧ 2*f = (d+1)*(d+2))
  · intro c ⟨d, f, hq, hf⟩; subst hq
    rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- d = m + m
      subst hm
      have hf1 : f ≥ 1 := by nlinarith
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      refine ⟨⟨0, 0, 0, m+m+1, 2*(m+m+1)+1, g+2*m+3⟩,
        ⟨m+m+1, g+2*m+3, rfl, by nlinarith⟩, ?_⟩
      have := even_trans m g
      convert this using 2; ring
    · -- d = 2*m + 1
      subst hm
      have hf1 : f ≥ 1 := by nlinarith
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      refine ⟨⟨0, 0, 0, 2*m+2, 2*(2*m+2)+1, g+2*m+4⟩,
        ⟨2*m+2, g+2*m+4, rfl, by nlinarith⟩, ?_⟩
      have := odd_trans m g
      convert this using 2; ring
  · exact ⟨0, 1, rfl, by omega⟩

end Sz22_2003_unofficial_626
