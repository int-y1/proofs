import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1535: [7/30, 27/35, 22/3, 5/11, 35/2]

Vector representation:
```
-1 -1 -1  1  0
 0  3 -1 -1  0
 1 -1  0  0  1
 0  0  1  0 -1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1535

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

theorem r3_drain : ∀ k, ∀ a e, ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih
  · intro a e; exists 0
  · intro a e; step fm
    apply stepStar_trans (ih (a + 1) (e + 1)); ring_nf; finish

theorem r4_drain : ∀ k, ∀ a c e, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro a c e; exists 0
  · intro a c e
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e); ring_nf; finish

theorem r1_chain : ∀ k, ∀ a b c d e, ⟨a + k, b + k, c + k, d, e⟩ [fm]⊢* ⟨a, b, c, d + k, e⟩ := by
  intro k; induction' k with k ih
  · intro a b c d e; exists 0
  · intro a b c d e
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show b + (k + 1) = (b + k) + 1 from by ring,
        show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a b c (d + 1) e); ring_nf; finish

theorem interleaved_drain : ∀ k, ∀ a e, ⟨a, 3, 0, k, e⟩ [fm]⊢* ⟨a + 3 * k, 3, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih
  · intro a e; simp; exists 0
  · intro a e
    step fm; step fm; step fm
    rw [show e + 3 = (e + 2) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 3) (e + 2)); ring_nf; finish

theorem r2_r1x3_step : ∀ a c d e, ⟨a + 3, 0, c + 4, d + 1, e⟩ [fm]⊢* ⟨a, 0, c, d + 3, e⟩ := by
  intro a c d e
  rw [show c + 4 = (c + 3) + 1 from by ring]
  step fm
  have := r1_chain 3 a 0 c d e
  rw [show a + 3 = a + 3 from rfl, show 0 + 3 = 3 from by ring,
      show c + 3 = c + 3 from rfl, show d + 3 = d + 3 from rfl] at this
  exact this

theorem r2r1x3_loop : ∀ k, ∀ a c d e, ⟨a + 3 * k, 0, c + 4 * k, d + 1, e⟩ [fm]⊢*
    ⟨a, 0, c, d + 2 * k + 1, e⟩ := by
  intro k; induction' k with k ih
  · intro a c d e; simp; exists 0
  · intro a c d e
    rw [show a + 3 * (k + 1) = (a + 3 * k) + 3 from by ring,
        show c + 4 * (k + 1) = (c + 4 * k) + 4 from by ring,
        show d + 2 * (k + 1) + 1 = (d + 2) + 2 * k + 1 from by ring]
    apply stepStar_trans (r2_r1x3_step (a + 3 * k) (c + 4 * k) d e)
    exact ih a c (d + 2) e

-- Opening: R3x3 + R4 + R5 + R2 + R1x3
-- (a, 3, 0, 0, e) ->* (a+3, 0, 0, 0, e+3) ->* (a+3, 0, e+3, 0, 0)
-- -> (a+2, 0, e+4, 1, 0) -> (a+2, 3, e+3, 0, 0) ->* (a-1, 0, e, 3, 0)
-- Net: (a, 3, 0, 0, e) ⊢⁺ (a-1, 0, e, 3, 0)
-- With offset: (a+1, 3, 0, 0, e) ⊢⁺ (a, 0, e, 3, 0)
theorem opening : ∀ a e, ⟨a + 1, 3, 0, 0, e⟩ [fm]⊢⁺ ⟨a, 0, e, 3, 0⟩ := by
  intro a e
  -- R3x3
  step fm; step fm; step fm
  -- (a+4, 0, 0, 0, e+3) -> R4x(e+3)
  rw [show e + 3 = 0 + (e + 3) from by ring]
  apply stepStar_trans (r4_drain (e + 3) (a + 4) 0 0)
  rw [show 0 + (e + 3) = e + 3 from by ring]
  -- (a+4, 0, e+3, 0, 0) -> R5
  rw [show a + 4 = (a + 3) + 1 from by ring]
  step fm
  -- (a+3, 0, e+4, 1, 0) -> R2
  rw [show e + 4 = (e + 3) + 1 from by ring]
  step fm
  -- (a+3, 3, e+3, 0, 0) -> R1x3
  rw [show a + 3 = a + 3 from rfl,
      show (3 : ℕ) = 0 + 3 from rfl,
      show e + 3 = e + 3 from rfl]
  apply stepStar_trans (r1_chain 3 a 0 e 0 0)
  ring_nf; finish

theorem trans_mod3 (m B : ℕ) :
    ⟨B + 3 * m + 4, 3, 0, 0, 4 * m + 3⟩ [fm]⊢⁺ ⟨B + 6 * m + 11, 3, 0, 0, 4 * m + 6⟩ := by
  -- Opening: (B+3m+4, 3, 0, 0, 4m+3) ⊢⁺ (B+3m+3, 0, 4m+3, 3, 0)
  rw [show B + 3 * m + 4 = (B + 3 * m + 3) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening (B + 3 * m + 3) (4 * m + 3))
  -- Loop x m: (B+3m+3, 0, 4m+3, 3, 0) = ((B+3)+3m, 0, 3+4m, 2+1, 0)
  rw [show B + 3 * m + 3 = (B + 3) + 3 * m from by ring,
      show 4 * m + 3 = 3 + 4 * m from by ring,
      show (3 : ℕ) = 2 + 1 from rfl]
  apply stepStar_trans (r2r1x3_loop m (B + 3) 3 2 0)
  rw [show 2 + 2 * m + 1 = (2 * m + 2) + 1 from by ring]
  -- (B+3, 0, 3, (2m+2)+1, 0) -> R2 (c=3>=1, d=(2m+2)+1>=1)
  rw [show (3 : ℕ) = 2 + 1 from rfl]
  step fm
  -- (B+3, 3, 2, 2m+2, 0) -> R1x2
  rw [show B + 3 = (B + 1) + 1 + 1 from by ring,
      show (3 : ℕ) = 1 + 1 + 1 from by ring,
      show (2 : ℕ) = 0 + 1 + 1 from by ring]
  step fm; step fm
  -- (B+1, 1, 0, 2m+4, 0) -> R3
  step fm
  -- (B+2, 0, 0, 2m+4, 1) -> R4
  step fm
  -- (B+2, 0, 1, 2m+4, 0) -> R2 (c=1, d=2m+4>=1)
  rw [show 2 * m + 4 = (2 * m + 3) + 1 from by ring]
  step fm
  -- (B+2, 3, 0, 2m+3, 0) -> drain
  apply stepStar_trans (interleaved_drain (2 * m + 3) (B + 2) 0)
  ring_nf; finish

theorem trans_mod1 (m B : ℕ) :
    ⟨B + 3 * m + 5, 3, 0, 0, 4 * m + 5⟩ [fm]⊢⁺ ⟨B + 6 * m + 13, 3, 0, 0, 4 * m + 8⟩ := by
  rw [show B + 3 * m + 5 = (B + 3 * m + 4) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening (B + 3 * m + 4) (4 * m + 5))
  rw [show B + 3 * m + 4 = (B + 1) + 3 * (m + 1) from by ring,
      show 4 * m + 5 = 1 + 4 * (m + 1) from by ring,
      show (3 : ℕ) = 2 + 1 from rfl]
  apply stepStar_trans (r2r1x3_loop (m + 1) (B + 1) 1 2 0)
  rw [show 2 + 2 * (m + 1) + 1 = (2 * m + 4) + 1 from by ring]
  -- (B+1, 0, 1, (2m+4)+1, 0) -> R2 (c=1, d>=1)
  step fm
  apply stepStar_trans (interleaved_drain (2 * m + 4) (B + 1) 0)
  ring_nf; finish

theorem trans_mod2 (m B : ℕ) :
    ⟨B + 3 * m + 6, 3, 0, 0, 4 * m + 6⟩ [fm]⊢⁺ ⟨B + 6 * m + 15, 3, 0, 0, 4 * m + 9⟩ := by
  rw [show B + 3 * m + 6 = (B + 3 * m + 5) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening (B + 3 * m + 5) (4 * m + 6))
  rw [show B + 3 * m + 5 = (B + 2) + 3 * (m + 1) from by ring,
      show 4 * m + 6 = 2 + 4 * (m + 1) from by ring,
      show (3 : ℕ) = 2 + 1 from rfl]
  apply stepStar_trans (r2r1x3_loop (m + 1) (B + 2) 2 2 0)
  rw [show 2 + 2 * (m + 1) + 1 = (2 * m + 4) + 1 from by ring]
  -- (B+2, 0, 2, (2m+4)+1, 0) -> R2 (c=2>=1, d>=1)
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  step fm
  -- (B+2, 3, 1, 2m+4, 0) -> R1x1
  rw [show B + 2 = (B + 1) + 1 from by ring, show (3 : ℕ) = 2 + 1 from rfl]
  step fm
  -- (B+1, 2, 0, 2m+5, 0) -> R3x2
  step fm; step fm
  -- (B+3, 0, 0, 2m+5, 2) -> R4
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  step fm
  -- (B+3, 0, 1, 2m+5, 1) -> R2 (c=1, d=2m+5>=1)
  rw [show 2 * m + 5 = (2 * m + 4) + 1 from by ring]
  step fm
  -- (B+3, 3, 0, 2m+4, 1) -> drain
  apply stepStar_trans (interleaved_drain (2 * m + 4) (B + 3) 1)
  ring_nf; finish

theorem trans_mod0 (m B : ℕ) :
    ⟨B + 3 * m + 7, 3, 0, 0, 4 * m + 4⟩ [fm]⊢⁺ ⟨B + 6 * m + 17, 3, 0, 0, 4 * m + 10⟩ := by
  rw [show B + 3 * m + 7 = (B + 3 * m + 6) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening (B + 3 * m + 6) (4 * m + 4))
  rw [show B + 3 * m + 6 = (B + 3) + 3 * (m + 1) from by ring,
      show 4 * m + 4 = 0 + 4 * (m + 1) from by ring,
      show (3 : ℕ) = 2 + 1 from rfl]
  apply stepStar_trans (r2r1x3_loop (m + 1) (B + 3) 0 2 0)
  rw [show 2 + 2 * (m + 1) + 1 = 2 * m + 5 from by ring]
  -- (B+3, 0, 0, 2m+5, 0) -> R5 (a=B+3>=1)
  rw [show B + 3 = (B + 2) + 1 from by ring]
  step fm
  -- (B+2, 0, 1, 2m+6, 0) -> R2 (c=1, d=2m+6>=1)
  rw [show 2 * m + 6 = (2 * m + 5) + 1 from by ring]
  step fm
  -- (B+2, 3, 0, 2m+5, 0) -> drain
  apply stepStar_trans (interleaved_drain (2 * m + 5) (B + 2) 0)
  ring_nf; finish

theorem super_trans (m B : ℕ) :
    ⟨B + 3 * m + 6, 3, 0, 0, 4 * m + 6⟩ [fm]⊢⁺ ⟨B + 12 * m + 42, 3, 0, 0, 4 * m + 18⟩ := by
  have h1 := trans_mod2 m B
  have h2 := trans_mod1 (m + 1) (B + 3 * m + 7)
  rw [show B + 3 * m + 7 + 3 * (m + 1) + 5 = B + 6 * m + 15 from by ring,
      show 4 * (m + 1) + 5 = 4 * m + 9 from by ring,
      show B + 3 * m + 7 + 6 * (m + 1) + 13 = B + 9 * m + 26 from by ring,
      show 4 * (m + 1) + 8 = 4 * m + 12 from by ring] at h2
  have h3 := trans_mod0 (m + 2) (B + 6 * m + 13)
  rw [show B + 6 * m + 13 + 3 * (m + 2) + 7 = B + 9 * m + 26 from by ring,
      show 4 * (m + 2) + 4 = 4 * m + 12 from by ring,
      show B + 6 * m + 13 + 6 * (m + 2) + 17 = B + 12 * m + 42 from by ring,
      show 4 * (m + 2) + 10 = 4 * m + 18 from by ring] at h3
  exact stepPlus_trans (stepPlus_trans h1 h2) h3

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨11, 3, 0, 0, 6⟩) (by execute fm 54)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨p.1 + 3 * p.2 + 6, 3, 0, 0, 4 * p.2 + 6⟩) ⟨5, 0⟩
  intro ⟨B, m⟩
  exact ⟨⟨B + 9 * m + 27, m + 3⟩, by
    show ⟨B + 3 * m + 6, 3, 0, 0, 4 * m + 6⟩ [fm]⊢⁺
      ⟨B + 9 * m + 27 + 3 * (m + 3) + 6, 3, 0, 0, 4 * (m + 3) + 6⟩
    rw [show B + 9 * m + 27 + 3 * (m + 3) + 6 = B + 12 * m + 42 from by ring,
        show 4 * (m + 3) + 6 = 4 * m + 18 from by ring]
    exact super_trans m B⟩

end Sz22_2003_unofficial_1535
