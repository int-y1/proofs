import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #639: [35/6, 143/2, 4/55, 3/7, 6/13]

Vector representation:
```
-1 -1  1  1  0  0
-1  0  0  0  1  1
 2  0 -1  0 -1  0
 0  1  0 -1  0  0
 1  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_639

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b+1, c, d, e, f⟩
  | _ => none

-- R4 chain: d → b
theorem d_to_b : ∀ k, ∀ b e f, ⟨0, b, 0, d+k, e, f⟩ [fm]⊢* ⟨0, b+k, 0, d, e, f⟩ := by
  intro k; induction' k with k h <;> intro b e f
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- R2 chain: a → e,f
theorem r2_chain : ∀ k, ∀ a c d e f, ⟨a+k, 0, c, d, e, f⟩ [fm]⊢* ⟨a, 0, c, d, e+k, f+k⟩ := by
  intro k; induction' k with k h <;> intro a c d e f
  · exists 0
  rw [← Nat.add_assoc]; step fm
  apply stepStar_trans (h _ _ _ _ _); ring_nf; finish

-- R3+R2+R2 chain: drain c
theorem r3r2r2_chain : ∀ k, ∀ c d e f, ⟨0, 0, c+k, d, e+k, f⟩ [fm]⊢* ⟨0, 0, c, d, e+2*k, f+2*k⟩ := by
  intro k; induction' k with k h <;> intro c d e f
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  rw [show e + k + 1 + 1 = (e + 2) + k from by ring,
      show f + 1 + 1 = (f + 2) + 0 from by ring]
  apply stepStar_trans (h c d (e + 2) (f + 2)); ring_nf; finish

-- R1+R1+R3 chain: interleaved rounds
theorem r1r1r3_chain : ∀ k, ∀ b c d e F, ⟨2, b+2*k, c, d, e+k, F⟩ [fm]⊢* ⟨2, b, c+k, d+2*k, e, F⟩ := by
  intro k; induction' k with k h <;> intro b c d e F
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
      show e + (k + 1) = (e + 1) + k from by ring]
  apply stepStar_trans (h (b + 2) c d (e + 1) F)
  step fm; step fm; step fm; ring_nf; finish

-- Even case: n = 2m
theorem even_trans (m g : ℕ) :
    ⟨0, 0, 0, 2*m, 2*m+1, g+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+1, 2*m+2, g+2*m+2⟩ := by
  have h1 : ⟨0, 0, 0, 0+2*m, 2*m+1, g+1⟩ [fm]⊢* ⟨0, 0+2*m, 0, 0, 2*m+1, g+1⟩ :=
    d_to_b (d := 0) (2*m) 0 (2*m+1) (g+1)
  simp only [Nat.zero_add] at h1
  apply stepStar_stepPlus_stepPlus h1
  step fm; step fm; step fm
  have h2 : ⟨2, 0+2*m, 0, 1, m+m, g⟩ [fm]⊢* ⟨2, 0, 0+m, 1+2*m, m, g⟩ :=
    r1r1r3_chain m 0 0 1 m g
  simp only [Nat.zero_add] at h2
  rw [show m + m = 2 * m from by ring, show 1 + 2 * m = 2 * m + 1 from by ring] at h2
  apply stepStar_trans h2
  have h3 : ⟨0+2, 0, m, 2*m+1, m, g⟩ [fm]⊢* ⟨0, 0, m, 2*m+1, m+2, g+2⟩ :=
    r2_chain 2 0 m (2*m+1) m g
  simp only [Nat.zero_add] at h3
  apply stepStar_trans h3
  have h4 : ⟨0, 0, 0+m, 2*m+1, 2+m, g+2⟩ [fm]⊢* ⟨0, 0, 0, 2*m+1, 2+2*m, (g+2)+2*m⟩ :=
    r3r2r2_chain m 0 (2*m+1) 2 (g+2)
  simp only [Nat.zero_add] at h4
  rw [show 2 + m = m + 2 from by ring, show 2 + 2 * m = 2 * m + 2 from by ring,
      show (g + 2) + 2 * m = g + 2 * m + 2 from by ring] at h4
  exact h4

-- Odd case: n = 2m+1
theorem odd_trans (m g : ℕ) :
    ⟨0, 0, 0, 2*m+1, 2*m+2, g+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+2, 2*m+3, g+2*m+3⟩ := by
  have h1 : ⟨0, 0, 0, 0+(2*m+1), 2*m+2, g+1⟩ [fm]⊢* ⟨0, 0+(2*m+1), 0, 0, 2*m+2, g+1⟩ :=
    d_to_b (d := 0) (2*m+1) 0 (2*m+2) (g+1)
  simp only [Nat.zero_add] at h1
  apply stepStar_stepPlus_stepPlus h1
  step fm; step fm; step fm
  have h2 : ⟨2, 1+2*m, 0, 1, (m+1)+m, g⟩ [fm]⊢* ⟨2, 1, 0+m, 1+2*m, m+1, g⟩ :=
    r1r1r3_chain m 1 0 1 (m+1) g
  simp only [Nat.zero_add] at h2
  rw [show (m + 1) + m = 2 * m + 1 from by ring, show 1 + 2 * m = 2 * m + 1 from by ring] at h2
  apply stepStar_trans h2
  step fm
  have h3 : ⟨0+1, 0, m+1, 2*m+2, m+1, g⟩ [fm]⊢* ⟨0, 0, m+1, 2*m+2, (m+1)+1, g+1⟩ :=
    r2_chain 1 0 (m+1) (2*m+2) (m+1) g
  simp only [Nat.zero_add] at h3
  rw [show (m + 1) + 1 = m + 2 from by ring] at h3
  rw [show 2 * m + 1 + 1 = 2 * m + 2 from by ring]
  apply stepStar_trans h3
  have h4 : ⟨0, 0, 0+(m+1), 2*m+2, 1+(m+1), g+1⟩ [fm]⊢* ⟨0, 0, 0, 2*m+2, 1+2*(m+1), (g+1)+2*(m+1)⟩ :=
    r3r2r2_chain (m+1) 0 (2*m+2) 1 (g+1)
  simp only [Nat.zero_add] at h4
  rw [show 1 + (m + 1) = m + 2 from by ring, show 1 + 2 * (m + 1) = 2 * m + 3 from by ring,
      show (g + 1) + 2 * (m + 1) = g + 2 * m + 3 from by ring] at h4
  exact h4

-- Main transition: canonical states form (0, 0, 0, n, n+1, g+1) with g increasing
theorem main_trans (n g : ℕ) :
    ⟨0, 0, 0, n, n+1, g+1⟩ [fm]⊢⁺ ⟨0, 0, 0, n+1, n+2, g+n+2⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    simp only [show m + m = 2 * m from by ring]
    exact even_trans m g
  · subst hm
    rw [show 2 * m + 1 + 1 = 2 * m + 2 from by ring, show 2 * m + 1 + 2 = 2 * m + 3 from by ring,
        show g + (2 * m + 1) + 2 = g + 2 * m + 3 from by ring]
    exact odd_trans m g

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 1, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, 0, 0, p.1, p.1+1, p.2+1⟩) ⟨0, 0⟩
  intro ⟨n, g⟩; simp only
  refine ⟨⟨n+1, g+n+1⟩, ?_⟩; simp only
  rw [show n + 1 + 1 = n + 2 from by ring, show g + n + 1 + 1 = g + n + 2 from by ring]
  exact main_trans n g
