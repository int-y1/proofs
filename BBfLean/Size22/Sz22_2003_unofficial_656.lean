import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #656: [35/6, 1573/2, 4/55, 3/7, 15/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  2  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 0  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_656

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+2, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

theorem d_to_b : ∀ k b d, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

-- R5 + R3: (0, b, 0, 0, e+1, f+1) →* (2, b+1, 0, 0, e, f)
theorem r5_r3 : ⟨0, b, 0, 0, e + 1, f + 1⟩ [fm]⊢* ⟨2, b + 1, 0, 0, e, f⟩ := by
  step fm; step fm; finish

-- Opening phase: R4×d, R5, R3
-- (0, 0, 0, d, e+1, f+1) →* (2, d+1, 0, 0, e, f) when d = 0 + d
theorem opening : ∀ d, ⟨0, 0, 0, d, e + 1, f + 1⟩ [fm]⊢* ⟨2, d + 1, 0, 0, e, f⟩ := by
  intro d
  rw [show (d : ℕ) = 0 + d from by omega]
  apply stepStar_trans (d_to_b d 0 0 (e := e + 1) (f := f + 1))
  rw [show 0 + d = d from by omega]
  exact r5_r3

theorem r1r1r3_chain : ∀ k b c d e,
    ⟨2, b + 2 * k, c, d, e + k, f⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) (d + 2) e)
    ring_nf; finish

theorem r2r2r3_chain : ∀ k c d e f,
    ⟨2, 0, c + k, d, e, f⟩ [fm]⊢* ⟨2, 0, c, d, e + 3 * k, f + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih c d (e + 3) (f + 2))
    ring_nf; finish

theorem final_r2r2 : ⟨2, 0, 0, d, e, f⟩ [fm]⊢⁺ ⟨0, 0, 0, d, e + 4, f + 2⟩ := by
  step fm; step fm; finish

-- Odd d = 2m+1
-- opening: (0,0,0,2m+1,g+4m+3+1,g+1) →* (2,2m+2,0,0,g+4m+3,g)
-- = (2,0+2*(m+1),0,0,(g+3m+2)+(m+1),g)
-- r1r1r3 k=m+1: →* (2,0,m+1,2m+2,g+3m+2,g)
-- = (2,0,0+(m+1),2m+2,g+3m+2,g)
-- r2r2r3 k=m+1: →* (2,0,0,2m+2,g+3m+2+3(m+1),g+2(m+1))
-- final_r2r2: →⁺ (0,0,0,2m+2,g+3m+2+3(m+1)+4,g+2(m+1)+2)
-- = (0,0,0,2m+2,g+6m+9,g+2m+4) ✓

theorem main_odd (m g : ℕ) :
    ⟨0, 0, 0, 2 * m + 1, g + 4 * m + 4, g + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 2, g + 6 * m + 9, g + 2 * m + 4⟩ := by
  rw [show g + 4 * m + 4 = g + 4 * m + 3 + 1 from by omega,
      show g + 1 = g + 0 + 1 from by omega]
  apply stepStar_stepPlus_stepPlus
    (opening (2 * m + 1) (e := g + 4 * m + 3) (f := g + 0))
  rw [show 2 * m + 1 + 1 = 0 + 2 * (m + 1) from by omega,
      show g + 4 * m + 3 = (g + 3 * m + 2) + (m + 1) from by omega,
      show g + 0 = g from by omega]
  apply stepStar_stepPlus_stepPlus
    (r1r1r3_chain (m + 1) 0 0 0 (g + 3 * m + 2) (f := g))
  rw [show 0 + (m + 1) = 0 + (m + 1) from rfl,
      show 0 + 2 * (m + 1) = 2 * m + 2 from by omega]
  apply stepStar_stepPlus_stepPlus
    (r2r2r3_chain (m + 1) 0 (2 * m + 2) (g + 3 * m + 2) g)
  exact stepPlus_stepStar_stepPlus final_r2r2 (by ring_nf; finish)

-- Even d = 0
-- (0,0,0,0,g+2,g+1) = (0,0,0,0,g+1+1,g+0+1)
-- opening: →* (2,1,0,0,g+1,g+0) = (2,0+1,0,0,g+1,g)
-- R1 (a=2≥1, b=1≥1): (1,0,1,1,g+1,g)
-- R2 (a=1≥1, b=0): (0,0,1,1,g+3,g+1)
-- R3 (c=1≥1, e=g+3≥1): (2,0,0,1,g+2,g+1)
-- final_r2r2: →⁺ (0,0,0,1,g+6,g+3) ✓

theorem main_even_zero (g : ℕ) :
    ⟨0, 0, 0, 0, g + 2, g + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 1, g + 6, g + 3⟩ := by
  rw [show g + 2 = g + 1 + 1 from by omega,
      show g + 1 = g + 0 + 1 from by omega]
  apply stepStar_stepPlus_stepPlus (opening 0 (e := g + 1) (f := g + 0))
  rw [show (0 : ℕ) + 1 = 0 + 1 from rfl,
      show g + 0 = g from by omega]
  -- (2, 1, 0, 0, g+1, g) = (2, 0+1, 0, 0, g+1, g)
  -- R1 needs a≥1, b≥1. a=2, b=1. R1: (1, 0, 1, 1, g+1, g)
  rw [show (0 : ℕ) + 1 = 0 + 1 from rfl]
  step fm  -- R1: (1, 0, 1, 1, g+1, g)
  -- R2: a=1, b=0. (0, 0, 1, 1, g+3, g+1)
  step fm  -- R2
  -- R3: c=1, e=g+3. (2, 0, 0, 1, g+2, g+1)
  step fm  -- R3
  -- final_r2r2
  exact stepPlus_stepStar final_r2r2

-- Even d = 2*(m+1) = 2m+2
-- opening: (0,0,0,2m+2,(g+4m+5)+1,(g+0)+1) →* (2,2m+3,0,0,g+4m+5,g)
-- = (2,1+2*(m+1),0,0,(g+3m+4)+(m+1),g)
-- r1r1r3 k=m+1, b=1: →* (2,1,m+1,2m+2,g+3m+4,g)
-- R1 (a=2,b=1): (1,0,m+2,2m+3,g+3m+4,g)
-- R2 (a=1,b=0): (0,0,m+2,2m+3,g+3m+6,g+1)
-- R3 (c=m+2≥1,e=g+3m+6≥1): (2,0,m+1,2m+3,g+3m+5,g+1)
-- r2r2r3 k=m+1: →* (2,0,0,2m+3,g+3m+5+3(m+1),g+1+2(m+1))
--              = (2,0,0,2m+3,g+6m+8,g+2m+3)
-- final_r2r2: →⁺ (0,0,0,2m+3,g+6m+12,g+2m+5) ✓

theorem main_even_succ (m g : ℕ) :
    ⟨0, 0, 0, 2 * m + 2, g + 4 * m + 6, g + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * m + 3, g + 6 * m + 12, g + 2 * m + 5⟩ := by
  rw [show g + 4 * m + 6 = g + 4 * m + 5 + 1 from by omega,
      show g + 1 = g + 0 + 1 from by omega]
  apply stepStar_stepPlus_stepPlus
    (opening (2 * m + 2) (e := g + 4 * m + 5) (f := g + 0))
  rw [show 2 * m + 2 + 1 = 1 + 2 * (m + 1) from by omega,
      show g + 4 * m + 5 = (g + 3 * m + 4) + (m + 1) from by omega,
      show g + 0 = g from by omega]
  apply stepStar_stepPlus_stepPlus
    (r1r1r3_chain (m + 1) 1 0 0 (g + 3 * m + 4) (f := g))
  rw [show 0 + (m + 1) = m + 1 from by omega,
      show 0 + 2 * (m + 1) = 2 * m + 2 from by omega]
  -- (2, 1, m+1, 2m+2, g+3m+4, g)
  -- R1
  rw [show (1 : ℕ) = 0 + 1 from by omega]
  step fm
  -- (1, 0, m+2, 2m+3, g+3m+4, g)
  -- R2
  step fm
  -- (0, 0, m+2, 2m+3, g+3m+6, g+1)
  -- R3
  step fm
  -- (2, 0, m+1, 2m+3, g+3m+5, g+1)
  rw [show (m + 1 : ℕ) = 0 + (m + 1) from by omega,
      show 2 * m + 2 + 1 = 2 * m + 3 from by ring]
  apply stepStar_trans
    (r2r2r3_chain (m + 1) 0 (2 * m + 3) (g + 3 * m + 5) (g + 1))
  have h := @final_r2r2 (2 * m + 3) (g + 3 * m + 5 + 3 * (m + 1)) (g + 1 + 2 * (m + 1))
  apply stepPlus_stepStar
  convert h using 2; ring_nf

theorem main_trans (d g : ℕ) :
    ⟨0, 0, 0, d, g + 2 * d + 2, g + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, d + 1, g + 3 * d + 6, g + d + 3⟩ := by
  rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    rcases m with _ | m
    · -- d = 0
      rw [show g + 2 * 0 + 2 = g + 2 from by ring,
          show (0 : ℕ) + 1 = 1 from rfl,
          show g + 3 * 0 + 6 = g + 6 from by ring,
          show g + 0 + 3 = g + 3 from by ring]
      exact main_even_zero g
    · -- d = 2*(m+1)
      rw [show g + 2 * (2 * (m + 1)) + 2 = g + 4 * m + 6 from by ring,
          show 2 * (m + 1) + 1 = 2 * m + 3 from by ring,
          show g + 3 * (2 * (m + 1)) + 6 = g + 6 * m + 12 from by ring,
          show g + 2 * (m + 1) + 3 = g + 2 * m + 5 from by ring,
          show 2 * (m + 1) = 2 * m + 2 from by ring]
      exact main_even_succ m g
  · subst hm
    rw [show g + 2 * (2 * m + 1) + 2 = g + 4 * m + 4 from by ring,
        show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
        show g + 3 * (2 * m + 1) + 6 = g + 6 * m + 9 from by ring,
        show g + (2 * m + 1) + 3 = g + 2 * m + 4 from by ring]
    exact main_odd m g

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2, 1⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, 0, 0, p.1, p.2 + 2 * p.1 + 2, p.2 + 1⟩) ⟨0, 0⟩
  intro ⟨d, g⟩
  refine ⟨⟨d + 1, g + d + 2⟩, ?_⟩
  show ⟨0, 0, 0, d, g + 2 * d + 2, g + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, d + 1, (g + d + 2) + 2 * (d + 1) + 2, (g + d + 2) + 1⟩
  rw [show (g + d + 2) + 2 * (d + 1) + 2 = g + 3 * d + 6 from by ring,
      show (g + d + 2) + 1 = g + d + 3 from by ring]
  exact main_trans d g

end Sz22_2003_unofficial_656
