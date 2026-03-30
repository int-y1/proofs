import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #745: [35/6, 4/55, 1859/2, 3/7, 15/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  2
 0  1  0 -1  0  0
 0  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_745

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+2⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

theorem r112_chain : ∀ k, ∀ b c d e f,
    ⟨2, b + 2 * k, c, d, e + k, f⟩ [fm]⊢*
    ⟨2, b, c + k, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d e f
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    rw [show b + 2 * k = b + 2 * k from rfl]
    step fm
    apply stepStar_trans (ih b (c + 1) (d + 2) e f)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a c d e f,
    ⟨a, 0, c + k, d, e + k, f⟩ [fm]⊢*
    ⟨a + 2 * k, 0, c, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e f)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ d e f,
    ⟨k, 0, 0, d, e, f⟩ [fm]⊢*
    ⟨0, 0, 0, d, e + k, f + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih d (e + 1) (f + 2))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b e f,
    ⟨0, b, 0, k, e, f⟩ [fm]⊢*
    ⟨0, b + k, 0, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b e f
  · exists 0
  · rw [show k + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (b + 1) e f)
    ring_nf; finish

theorem phase_b_even (m f : ℕ) :
    ⟨2, 2 * m + 2, 0, 0, 2 * m + 1, f⟩ [fm]⊢*
    ⟨2 * m + 2, 0, 1, 2 * m + 2, 0, f⟩ := by
  have h1 : ⟨2, 2 * m + 2, 0, 0, 2 * m + 1, f⟩ [fm]⊢*
      ⟨2, 0, m + 1, 2 * m + 2, m, f⟩ := by
    have key := r112_chain (m + 1) 0 0 0 m f
    convert key using 2; ring_nf
  have h2 : ⟨2, 0, m + 1, 2 * m + 2, m, f⟩ [fm]⊢*
      ⟨2 * m + 2, 0, 1, 2 * m + 2, 0, f⟩ := by
    have key := r2_chain m 2 1 (2 * m + 2) 0 f
    convert key using 2; ring_nf
  exact stepStar_trans h1 h2

theorem phase_b_odd (m f : ℕ) :
    ⟨2, 2 * m + 3, 0, 0, 2 * m + 2, f⟩ [fm]⊢*
    ⟨2 * m + 3, 0, 1, 2 * m + 3, 0, f⟩ := by
  have h1 : ⟨2, 2 * m + 3, 0, 0, 2 * m + 2, f⟩ [fm]⊢*
      ⟨2, 1, m + 1, 2 * m + 2, m + 1, f⟩ := by
    have key := r112_chain (m + 1) 1 0 0 (m + 1) f
    convert key using 2; ring_nf
  have h2 : ⟨2, 1, m + 1, 2 * m + 2, m + 1, f⟩ [fm]⊢*
      ⟨1, 0, m + 2, 2 * m + 3, m + 1, f⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring,
        show m + 1 = m + 1 from rfl]
    step fm; finish
  have h3 : ⟨1, 0, m + 2, 2 * m + 3, m + 1, f⟩ [fm]⊢*
      ⟨2 * m + 3, 0, 1, 2 * m + 3, 0, f⟩ := by
    have key := r2_chain (m + 1) 1 1 (2 * m + 3) 0 f
    convert key using 2; ring_nf
  exact stepStar_trans h1 (stepStar_trans h2 h3)

theorem main_trans (n : ℕ) :
    ⟨0, n + 1, 0, 0, n + 2, n * n + 6 * n + 7⟩ [fm]⊢⁺
    ⟨0, n + 2, 0, 0, n + 3, n * n + 8 * n + 14⟩ := by
  rw [show n * n + 6 * n + 7 = (n * n + 6 * n + 6) + 1 from by ring]
  step fm
  rw [show n + 1 + 1 = n + 2 from by ring,
      show n + 2 = (n + 1) + 1 from by ring]
  step fm
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    have hf : 2 * m * (2 * m) + 6 * (2 * m) + 6 = 4 * m * m + 12 * m + 6 := by ring
    rw [show 2 * m + 1 + 1 = 2 * m + 2 from by ring, hf]
    apply stepStar_trans (phase_b_even m (4 * m * m + 12 * m + 6))
    rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
    step fm
    rw [show 4 * m * m + 12 * m + 6 + 2 = 4 * m * m + 12 * m + 8 from by ring,
        show 2 * m + 1 + 2 = 2 * m + 3 from by ring]
    step fm
    have h3 : ⟨2 * m + 3, 0, 0, 2 * m + 2, 0, 4 * m * m + 12 * m + 8⟩ [fm]⊢*
        ⟨0, 0, 0, 2 * m + 2, 2 * m + 3, 4 * m * m + 16 * m + 14⟩ := by
      have key := r3_chain (2 * m + 3) (2 * m + 2) 0 (4 * m * m + 12 * m + 8)
      convert key using 2; ring_nf
    apply stepStar_trans h3
    have h4 : ⟨0, 0, 0, 2 * m + 2, 2 * m + 3, 4 * m * m + 16 * m + 14⟩ [fm]⊢*
        ⟨0, 2 * m + 2, 0, 0, 2 * m + 3, 4 * m * m + 16 * m + 14⟩ := by
      have key := r4_chain (2 * m + 2) 0 (2 * m + 3) (4 * m * m + 16 * m + 14)
      convert key using 2; ring_nf
    apply stepStar_trans h4
    ring_nf; finish
  · subst hm
    have hf : (2 * m + 1) * (2 * m + 1) + 6 * (2 * m + 1) + 6 = 4 * m * m + 16 * m + 13 := by ring
    rw [show 2 * m + 1 + 1 + 1 = 2 * m + 3 from by ring, hf]
    apply stepStar_trans (phase_b_odd m (4 * m * m + 16 * m + 13))
    rw [show 2 * m + 3 = (2 * m + 2) + 1 from by ring]
    step fm
    rw [show 4 * m * m + 16 * m + 13 + 2 = 4 * m * m + 16 * m + 15 from by ring,
        show 2 * m + 2 + 2 = 2 * m + 4 from by ring]
    step fm
    have h3 : ⟨2 * m + 4, 0, 0, 2 * m + 3, 0, 4 * m * m + 16 * m + 15⟩ [fm]⊢*
        ⟨0, 0, 0, 2 * m + 3, 2 * m + 4, 4 * m * m + 20 * m + 23⟩ := by
      have key := r3_chain (2 * m + 4) (2 * m + 3) 0 (4 * m * m + 16 * m + 15)
      convert key using 2; ring_nf
    apply stepStar_trans h3
    have h4 : ⟨0, 0, 0, 2 * m + 3, 2 * m + 4, 4 * m * m + 20 * m + 23⟩ [fm]⊢*
        ⟨0, 2 * m + 3, 0, 0, 2 * m + 4, 4 * m * m + 20 * m + 23⟩ := by
      have key := r4_chain (2 * m + 3) 0 (2 * m + 4) (4 * m * m + 20 * m + 23)
      convert key using 2; ring_nf
    apply stepStar_trans h4
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 0, 2, 7⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, n + 1, 0, 0, n + 2, n * n + 6 * n + 7⟩) 0
  intro n; refine ⟨n + 1, ?_⟩
  convert main_trans n using 2
  ring_nf

end Sz22_2003_unofficial_745
