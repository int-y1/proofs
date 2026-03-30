import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #741: [35/6, 4/55, 1573/2, 3/7, 15/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  2  1
 0  1  0 -1  0  0
 0  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_741

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+2, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 2) (f + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e f, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a c d e f, ⟨a, 0, c + k, d, e + k, f⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e f)
    ring_nf; finish

theorem r1r1r2_chain : ∀ k, ∀ c d e f, ⟨2, 2 * k, c, d, e + k, f⟩ [fm]⊢* ⟨2, 0, c + k, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e f)
    ring_nf; finish

theorem r1r1r2_chain_odd : ∀ k, ∀ c d e f, ⟨2, 2 * k + 1, c, d, e + k, f⟩ [fm]⊢* ⟨1, 0, c + k + 1, d + 2 * k + 1, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e f)
    ring_nf; finish

theorem main_even (m f : ℕ) :
    ⟨2 * m + 1, 0, 0, 2 * m + 1, f + 2 * m + 2, f⟩ [fm]⊢⁺
    ⟨2 * m + 2, 0, 0, 2 * m + 2, f + 4 * m + 5, f + 2 * m + 2⟩ := by
  rw [show 2 * m + 1 = 0 + (2 * m + 1) from by ring]
  step fm
  -- After R3: (0+(2*m), 0, 0, 0+(2*m+1), f+2*m+2+2, f+1)
  -- Need to normalize and apply r3_chain for remaining 2*m steps
  have h1 := r3_chain (2 * m) 0 (2 * m + 1) (f + 2 * m + 4) (f + 1)
  -- h1: (0+(2*m), 0, 0, 2*m+1, f+2*m+4, f+1) ⊢* (0, 0, 0, 2*m+1, f+6*m+4, f+2*m+1)
  have h1' : ⟨0 + (2 * m), 0, 0, 0 + (2 * m + 1), f + 2 * m + 2 + 2, f + 1⟩ [fm]⊢*
              ⟨0, 0, 0, 2 * m + 1, f + 6 * m + 4, f + 2 * m + 1⟩ := by
    convert h1 using 2; all_goals ring_nf
  apply stepStar_trans h1'
  have h2 := r4_chain (2 * m + 1) 0 0 (f + 6 * m + 4) (f + 2 * m + 1)
  have h2' : ⟨0, 0, 0, 2 * m + 1, f + 6 * m + 4, f + 2 * m + 1⟩ [fm]⊢*
              ⟨0, 2 * m + 1, 0, 0, f + 6 * m + 4, f + 2 * m + 1⟩ := by
    convert h2 using 2; all_goals ring_nf
  apply stepStar_trans h2'
  -- Now: (0, 2*m+1, 0, 0, f+6*m+4, f+2*m+1)
  rw [show 2 * m + 1 = (2 * m) + 1 from by ring,
      show f + 2 * m + 1 = (f + 2 * m) + 1 from by ring]
  step fm -- R5: (0, 2*m+1+1, 1, 0, f+6*m+4, f+2*m)
  rw [show f + 6 * m + 4 = (f + 6 * m + 3) + 1 from by ring,
      show 2 * m + 1 = (2 * m) + 1 from by ring]
  step fm -- R2: (2, 2*m+1+1, 0, 0, f+6*m+3, f+2*m)
  -- Now: (2, 2*m+2, 0, 0, f+6*m+3, f+2*m)
  have h3 := r1r1r2_chain (m + 1) 0 0 (f + 5 * m + 2) (f + 2 * m)
  have h3' : ⟨2, 2 * m + 2, 0, 0, f + 6 * m + 3, f + 2 * m⟩ [fm]⊢*
              ⟨2, 0, m + 1, 2 * m + 2, f + 5 * m + 2, f + 2 * m⟩ := by
    convert h3 using 2; all_goals ring_nf
  apply stepStar_trans h3'
  have h4 := r2_chain (m + 1) 2 0 (2 * m + 2) (f + 4 * m + 1) (f + 2 * m)
  have h4' : ⟨2, 0, m + 1, 2 * m + 2, f + 5 * m + 2, f + 2 * m⟩ [fm]⊢*
              ⟨2 * m + 4, 0, 0, 2 * m + 2, f + 4 * m + 1, f + 2 * m⟩ := by
    convert h4 using 2; all_goals ring_nf
  apply stepStar_trans h4'
  have h5 := r3_chain 2 (2 * m + 2) (2 * m + 2) (f + 4 * m + 1) (f + 2 * m)
  convert h5 using 2

theorem main_odd (m f : ℕ) :
    ⟨2 * m + 2, 0, 0, 2 * m + 2, f + 2 * m + 3, f⟩ [fm]⊢⁺
    ⟨2 * m + 3, 0, 0, 2 * m + 3, f + 4 * m + 7, f + 2 * m + 3⟩ := by
  rw [show 2 * m + 2 = 0 + (2 * m + 2) from by ring]
  step fm
  have h1 := r3_chain (2 * m + 1) 0 (2 * m + 2) (f + 2 * m + 5) (f + 1)
  have h1' : ⟨0 + (2 * m + 1), 0, 0, 0 + (2 * m + 2), f + 2 * m + 3 + 2, f + 1⟩ [fm]⊢*
              ⟨0, 0, 0, 2 * m + 2, f + 6 * m + 7, f + 2 * m + 2⟩ := by
    convert h1 using 2; all_goals ring_nf
  apply stepStar_trans h1'
  have h2 := r4_chain (2 * m + 2) 0 0 (f + 6 * m + 7) (f + 2 * m + 2)
  have h2' : ⟨0, 0, 0, 2 * m + 2, f + 6 * m + 7, f + 2 * m + 2⟩ [fm]⊢*
              ⟨0, 2 * m + 2, 0, 0, f + 6 * m + 7, f + 2 * m + 2⟩ := by
    convert h2 using 2; all_goals ring_nf
  apply stepStar_trans h2'
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring,
      show f + 2 * m + 2 = (f + 2 * m + 1) + 1 from by ring]
  step fm -- R5
  rw [show f + 6 * m + 7 = (f + 6 * m + 6) + 1 from by ring,
      show 2 * m + 1 + 1 + 1 = (2 * m + 2) + 1 from by ring]
  step fm -- R2
  have h3 := r1r1r2_chain_odd (m + 1) 0 0 (f + 5 * m + 5) (f + 2 * m + 1)
  have h3' : ⟨2, 2 * m + 3, 0, 0, f + 6 * m + 6, f + 2 * m + 1⟩ [fm]⊢*
              ⟨1, 0, m + 2, 2 * m + 3, f + 5 * m + 5, f + 2 * m + 1⟩ := by
    convert h3 using 2; all_goals ring_nf
  apply stepStar_trans h3'
  have h4 := r2_chain (m + 2) 1 0 (2 * m + 3) (f + 4 * m + 3) (f + 2 * m + 1)
  have h4' : ⟨1, 0, m + 2, 2 * m + 3, f + 5 * m + 5, f + 2 * m + 1⟩ [fm]⊢*
              ⟨2 * m + 5, 0, 0, 2 * m + 3, f + 4 * m + 3, f + 2 * m + 1⟩ := by
    convert h4 using 2; all_goals ring_nf
  apply stepStar_trans h4'
  have h5 := r3_chain 2 (2 * m + 3) (2 * m + 3) (f + 4 * m + 3) (f + 2 * m + 1)
  convert h5 using 2

theorem main_trans (n f : ℕ) :
    ⟨n + 1, 0, 0, n + 1, f + n + 2, f⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, n + 2, f + 2 * n + 5, f + n + 2⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    convert main_even m f using 2
    all_goals ring_nf
  · subst hm
    convert main_odd m f using 2
    all_goals ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 1, 4, 2⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, f⟩ ↦ ⟨n + 1, 0, 0, n + 1, f + n + 2, f⟩) ⟨0, 2⟩
  intro ⟨n, f⟩
  refine ⟨⟨n + 1, f + n + 2⟩, ?_⟩
  convert main_trans n f using 2
  all_goals ring_nf

end Sz22_2003_unofficial_741
