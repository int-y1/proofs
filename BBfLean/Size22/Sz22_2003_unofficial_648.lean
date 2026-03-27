import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #648: [35/6, 143/2, 52/55, 3/7, 6/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  1
 0  1  0 -1  0  0
 1  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_648

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b+1, c, d, e, f⟩
  | _ => none

theorem d_to_b : ∀ k b, ⟨0, b, 0, d+k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, d, e, f⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _); ring_nf; finish

theorem r1r1r3_chain :
    ∀ k c d e f, ⟨2, b+2*k, c, d, e+k, f⟩ [fm]⊢* ⟨2, b, c+k, d+2*k, e, f+k⟩ := by
  intro k; induction' k with k h <;> intro c d e f
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _ _); ring_nf; finish

theorem r2r2r3_chain :
    ∀ k e f, ⟨2, 0, c+k, d, e, f⟩ [fm]⊢* ⟨2, 0, c, d, e+k, f+3*k⟩ := by
  intro k; induction' k with k h <;> intro e f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _); ring_nf; finish

theorem inner_even (m F : ℕ) :
    ⟨2, 2*m+1, 0, 1, 2*m+1, F⟩ [fm]⊢* ⟨0, 0, 0, 2*m+2, 2*m+3, F+4*m+4⟩ := by
  have h1 := r1r1r3_chain (b := 1) m 0 1 (m+1) F
  have h1' : ⟨2, 2*m+1, 0, 1, 2*m+1, F⟩ [fm]⊢* ⟨2, 1, m, 2*m+1, m+1, F+m⟩ := by
    convert h1 using 2 ; ring_nf
  apply stepStar_trans h1'
  step fm; step fm; step fm
  have h2 := r2r2r3_chain (c := 0) (d := 2*m+2) m (m+1) (F+m+2)
  have h2' : ⟨2, 0, m, 2*m+2, m+1, F+m+2⟩ [fm]⊢* ⟨2, 0, 0, 2*m+2, 2*m+1, F+4*m+2⟩ := by
    convert h2 using 2 ; ring_nf
  apply stepStar_trans h2'
  step fm; step fm; ring_nf; finish

theorem inner_odd (m F : ℕ) :
    ⟨2, 2*m+2, 0, 1, 2*m+2, F⟩ [fm]⊢* ⟨0, 0, 0, 2*m+3, 2*m+4, F+4*m+6⟩ := by
  have h1 := r1r1r3_chain (b := 0) (m+1) 0 1 (m+1) F
  have h1' : ⟨2, 2*m+2, 0, 1, 2*m+2, F⟩ [fm]⊢* ⟨2, 0, m+1, 2*m+3, m+1, F+m+1⟩ := by
    convert h1 using 2 ; ring_nf
  apply stepStar_trans h1'
  have h2 := r2r2r3_chain (c := 0) (d := 2*m+3) (m+1) (m+1) (F+m+1)
  have h2' : ⟨2, 0, m+1, 2*m+3, m+1, F+m+1⟩ [fm]⊢* ⟨2, 0, 0, 2*m+3, 2*m+2, F+4*m+4⟩ := by
    convert h2 using 2 ; ring_nf
  apply stepStar_trans h2'
  step fm; step fm; ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, n+1, n+2, n*n+3*n+3⟩ [fm]⊢⁺
    ⟨0, 0, 0, n+2, n+3, n*n+5*n+7⟩ := by
  have hR4 : ⟨0, 0, 0, n+1, n+2, n*n+3*n+3⟩ [fm]⊢* ⟨0, n+1, 0, 0, n+2, n*n+3*n+3⟩ := by
    have := d_to_b (d := 0) (e := n+2) (f := n*n+3*n+3) (n+1) 0
    convert this using 2 ; ring_nf
  apply stepStar_stepPlus_stepPlus hR4
  step fm; step fm; step fm
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    have hi := inner_even m ((m+m)*(m+m)+3*(m+m)+2+1)
    have h : ⟨2, m+m+1, 0, 1, m+m+1, (m+m)*(m+m)+3*(m+m)+2+1⟩ [fm]⊢*
             ⟨0, 0, 0, m+m+2, m+m+3, (m+m)*(m+m)+5*(m+m)+7⟩ := by
      convert hi using 2 ; ring_nf
    exact stepStar_trans h (by exists 0)
  · subst hm
    have hi := inner_odd m ((2*m+1)*(2*m+1)+3*(2*m+1)+2+1)
    have h : ⟨2, 2*m+1+1, 0, 1, 2*m+1+1, (2*m+1)*(2*m+1)+3*(2*m+1)+2+1⟩ [fm]⊢*
             ⟨0, 0, 0, 2*m+1+2, 2*m+1+3, (2*m+1)*(2*m+1)+5*(2*m+1)+7⟩ := by
      convert hi using 2 ; ring_nf
    exact stepStar_trans h (by exists 0)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2, 3⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n+1, n+2, n*n+3*n+3⟩) 0
  intro n; exists n+1
  have := main_trans n
  convert this using 2; ring_nf
