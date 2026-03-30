import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #861: [385/6, 65/2, 4/91, 3/11, 77/5]

Vector representation:
```
-1 -1  1  1  1  0
-1  0  1  0  0  1
 2  0  0 -1  0 -1
 0  1  0  0 -1  0
 0  0 -1  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_861

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f+1⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | _ => none

-- R4 chain: move e to b
theorem e_to_b : ∀ k b c e f, ⟨0, b, c, 0, e + k, f⟩ [fm]⊢* ⟨0, b + k, c, 0, e, f⟩ := by
  intro k; induction' k with k ih
  · intro b c e f; exists 0
  · intro b c e f
    rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) c e f)
    ring_nf; finish

-- Specialized: (0, 0, c, 0, n, f) →* (0, n, c, 0, 0, f)
theorem e_to_b' (n : ℕ) : ⟨0, 0, c, 0, n, f⟩ [fm]⊢* ⟨0, n, c, 0, 0, f⟩ := by
  have := e_to_b n 0 c 0 f
  simp only [Nat.zero_add] at this; exact this

-- R1,R1,R3 chain: k rounds
theorem r1r1r3_chain : ∀ k b c d e f, ⟨2, b + 2 * k, c, d, e, f + k⟩ [fm]⊢* ⟨2, b, c + 2 * k, d + k, e + 2 * k, f⟩ := by
  intro k; induction' k with k ih
  · intro b c d e f; exists 0
  · intro b c d e f
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show f + (k + 1) = f + k + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 2) (d + 1) (e + 2) f)
    ring_nf; finish

-- Specialized: (2, 2m, c, 0, 1, 2m) →* (2, 0, c+2m, m, 2m+1, m)
theorem r1r1r3_even (m : ℕ) : ⟨2, 2*m, c, 0, 1, 2*m⟩ [fm]⊢* ⟨2, 0, c + 2*m, m, 2*m+1, m⟩ := by
  have := r1r1r3_chain m 0 c 0 1 m
  simp only [Nat.zero_add] at this
  rw [show m + m = 2 * m from by ring, show 1 + 2 * m = 2 * m + 1 from by ring] at this
  exact this

-- Specialized: (2, 2m+1, c, 0, 1, 2m+1) →* (2, 1, c+2m, m, 2m+1, m+1)
theorem r1r1r3_odd (m : ℕ) : ⟨2, 2*m+1, c, 0, 1, 2*m+1⟩ [fm]⊢* ⟨2, 1, c + 2*m, m, 2*m+1, m+1⟩ := by
  have := r1r1r3_chain m 1 c 0 1 (m+1)
  simp only [Nat.zero_add] at this
  rw [show 1 + 2 * m = 2 * m + 1 from by ring,
      show (m + 1) + m = 2 * m + 1 from by ring] at this
  exact this

-- R2,R2,R3 chain: k rounds
theorem r2r2r3_chain : ∀ k c d e f, ⟨2, 0, c, d + k, e, f⟩ [fm]⊢* ⟨2, 0, c + 2 * k, d, e, f + k⟩ := by
  intro k; induction' k with k ih
  · intro c d e f; exists 0
  · intro c d e f
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 2) d e (f + 1))
    ring_nf; finish

-- Specialized: (2, 0, c, m, e, m) →* (2, 0, c+2m, 0, e, 2m)
theorem r2r2r3_m (m : ℕ) : ⟨2, 0, c, m, e, m⟩ [fm]⊢* ⟨2, 0, c + 2*m, 0, e, 2*m⟩ := by
  have := r2r2r3_chain m c 0 e m
  simp only [Nat.zero_add] at this
  rw [show m + m = 2 * m from by ring] at this
  exact this

-- Specialized: (2, 0, c, m, e, m+1) →* (2, 0, c+2m, 0, e, 2m+1)
theorem r2r2r3_m1 (m : ℕ) : ⟨2, 0, c, m, e, m+1⟩ [fm]⊢* ⟨2, 0, c + 2*m, 0, e, 2*m+1⟩ := by
  have := r2r2r3_chain m c 0 e (m+1)
  simp only [Nat.zero_add] at this
  rw [show m + 1 + m = 2 * m + 1 from by ring] at this
  exact this

-- R5+R3: (0, n, c+1, 0, 0, n+1) →⁺ (2, n, c, 0, 1, n)
theorem r5r3 (n : ℕ) : ⟨0, n, c + 1, 0, 0, n + 1⟩ [fm]⊢⁺ ⟨2, n, c, 0, 1, n⟩ := by
  step fm; step fm; finish

-- Even transition: n = 2*m
theorem main_even (m : ℕ) : ⟨0, 0, (2*m) ^ 2 + 1, 0, 2*m, 2*m + 1⟩ [fm]⊢⁺
    ⟨0, 0, (2*m + 1) ^ 2 + 1, 0, 2*m + 1, 2*m + 2⟩ := by
  apply stepStar_stepPlus_stepPlus (e_to_b' (2*m) (c := (2*m)^2+1) (f := 2*m+1))
  apply stepPlus_stepStar_stepPlus (r5r3 (2*m) (c := (2*m)^2))
  apply stepStar_trans (r1r1r3_even m (c := (2*m)^2))
  apply stepStar_trans (r2r2r3_m m (c := (2*m)^2+2*m) (e := 2*m+1))
  step fm; step fm; ring_nf; finish

-- Odd transition: n = 2*m + 1
theorem main_odd (m : ℕ) : ⟨0, 0, (2*m+1) ^ 2 + 1, 0, 2*m+1, 2*m+2⟩ [fm]⊢⁺
    ⟨0, 0, (2*m+2) ^ 2 + 1, 0, 2*m+2, 2*m+3⟩ := by
  apply stepStar_stepPlus_stepPlus (e_to_b' (2*m+1) (c := (2*m+1)^2+1) (f := 2*m+2))
  apply stepPlus_stepStar_stepPlus (r5r3 (2*m+1) (c := (2*m+1)^2))
  apply stepStar_trans (r1r1r3_odd m (c := (2*m+1)^2))
  -- R1 (b=1), R2 (b=0), R3
  step fm; step fm; step fm
  rw [show (2*m+1)^2 + 2*m + 1 + 1 = (2*m+1)^2+2*m+2 from by ring,
      show 2*m+1+1 = 2*m+2 from by ring]
  apply stepStar_trans (r2r2r3_m1 m (c := (2*m+1)^2+2*m+2) (e := 2*m+2))
  step fm; step fm; ring_nf; finish

-- Combined main transition
theorem main_trans : ∀ n, ⟨0, 0, n ^ 2 + 1, 0, n, n + 1⟩ [fm]⊢⁺
    ⟨0, 0, (n + 1) ^ 2 + 1, 0, n + 1, n + 2⟩ := by
  intro n
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    exact main_even m
  · subst hm; exact main_odd m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0 ^ 2 + 1, 0, 0, 0 + 1⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, n ^ 2 + 1, 0, n, n + 1⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_861
