import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #698: [35/6, 4/55, 121/2, 3/7, 12/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  2
 0  1  0 -1  0
 2  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_698

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | _ => none

def e_val : ℕ → ℕ
  | 0 => 0
  | n + 1 => e_val n + n + 3

theorem r3_chain : ∀ k, ∀ d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show k + 1 = (k) + 1 from rfl]
    step fm
    apply stepStar_trans (ih d (e + 2))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b e, ⟨0, b, 0, k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show k + 1 = (k) + 1 from rfl]
    step fm
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

theorem r2_drain : ∀ k, ∀ a d e, ⟨a, 0, k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring,
        show k + 1 = (k) + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 2) d e)
    ring_nf; finish

theorem r1r1r2_chain : ∀ k, ∀ b c d e,
    ⟨2, b + 2 * k, c, d, e + k⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih b (c + 1) (d + 2) e)
    ring_nf; finish

theorem r5_r1r1_r2 (b e : ℕ) :
    ⟨0, b + 1, 0, 0, e + 2⟩ [fm]⊢⁺ ⟨2, b, 1, 2, e⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, b + 1, 0, 0, (e + 1) + 1⟩ = some ⟨2, (b + 1) + 1, 0, 0, e + 1⟩
    simp [fm]
  rw [show (b + 1) + 1 = b + 1 + 1 from rfl]
  step fm; step fm
  rw [show e + 1 = (e) + 1 from rfl]
  step fm
  finish

theorem full_even (m E : ℕ) :
    ⟨0, 2 * m + 1, 0, 0, E + 4 * m + 6⟩ [fm]⊢⁺
    ⟨2 * m + 4, 0, 0, 2 * m + 2, E + 2 * m + 3⟩ := by
  -- R5+R1R1+R2
  rw [show E + 4 * m + 6 = (E + 4 * m + 4) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (r5_r1r1_r2 (2 * m) (E + 4 * m + 4))
  -- R1R1R2 chain (m rounds)
  have h1 := r1r1r2_chain m 0 1 2 (E + 3 * m + 4)
  have h1' : ⟨2, 2 * m, 1, 2, E + 4 * m + 4⟩ [fm]⊢*
             ⟨2, 0, m + 1, 2 * m + 2, E + 3 * m + 4⟩ := by
    convert h1 using 2; ring_nf
  apply stepStar_trans h1'
  -- R2 drain (m+1 steps)
  have h2 := r2_drain (m + 1) 2 (2 * m + 2) (E + 2 * m + 3)
  have h2' : ⟨2, 0, m + 1, 2 * m + 2, E + 3 * m + 4⟩ [fm]⊢*
             ⟨2 * m + 4, 0, 0, 2 * m + 2, E + 2 * m + 3⟩ := by
    convert h2 using 2; ring_nf
  exact h2'

theorem full_odd (m E : ℕ) :
    ⟨0, 2 * m + 2, 0, 0, E + 4 * m + 8⟩ [fm]⊢⁺
    ⟨2 * m + 5, 0, 0, 2 * m + 3, E + 2 * m + 4⟩ := by
  -- R5+R1R1+R2
  rw [show E + 4 * m + 8 = (E + 4 * m + 6) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (r5_r1r1_r2 (2 * m + 1) (E + 4 * m + 6))
  -- R1R1R2 chain (m rounds)
  have h1 := r1r1r2_chain m 1 1 2 (E + 3 * m + 6)
  have h1' : ⟨2, 2 * m + 1, 1, 2, E + 4 * m + 6⟩ [fm]⊢*
             ⟨2, 1, m + 1, 2 * m + 2, E + 3 * m + 6⟩ := by
    convert h1 using 2; ring_nf
  apply stepStar_trans h1'
  -- R1 step
  rw [show (2 : ℕ) = (1) + 1 from rfl,
      show (1 : ℕ) = (0) + 1 from rfl]
  step fm
  -- R2 drain (m+2 steps)
  have h2 := r2_drain (m + 2) 1 (2 * m + 3) (E + 2 * m + 4)
  have h2' : ⟨1, 0, m + 2, 2 * m + 3, E + 3 * m + 6⟩ [fm]⊢*
             ⟨2 * m + 5, 0, 0, 2 * m + 3, E + 2 * m + 4⟩ := by
    convert h2 using 2; ring_nf
  exact h2'

theorem main_trans_even (m : ℕ) :
    ⟨2 * m + 3, 0, 0, 2 * m + 1, e_val (2 * m)⟩ [fm]⊢⁺
    ⟨2 * m + 4, 0, 0, 2 * m + 2, e_val (2 * m) + 2 * m + 3⟩ := by
  apply stepStar_stepPlus_stepPlus (r3_chain (2 * m + 3) (2 * m + 1) (e_val (2 * m)))
  have h2 := r4_chain (2 * m + 1) 0 (e_val (2 * m) + 2 * (2 * m + 3))
  simp at h2
  apply stepStar_stepPlus_stepPlus h2
  have key := full_even m (e_val (2 * m))
  convert key using 2; ring_nf

theorem main_trans_odd (m : ℕ) :
    ⟨2 * m + 4, 0, 0, 2 * m + 2, e_val (2 * m + 1)⟩ [fm]⊢⁺
    ⟨2 * m + 5, 0, 0, 2 * m + 3, e_val (2 * m + 1) + 2 * m + 4⟩ := by
  apply stepStar_stepPlus_stepPlus (r3_chain (2 * m + 4) (2 * m + 2) (e_val (2 * m + 1)))
  have h2 := r4_chain (2 * m + 2) 0 (e_val (2 * m + 1) + 2 * (2 * m + 4))
  simp at h2
  apply stepStar_stepPlus_stepPlus h2
  have key := full_odd m (e_val (2 * m + 1))
  convert key using 2; ring_nf

theorem main_trans (n : ℕ) :
    ⟨n + 3, 0, 0, n + 1, e_val n⟩ [fm]⊢⁺ ⟨n + 4, 0, 0, n + 2, e_val (n + 1)⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show m + m = 2 * m from by ring] at hm; subst hm
    have : e_val (2 * m + 1) = e_val (2 * m) + 2 * m + 3 := by simp [e_val]
    rw [this]
    exact main_trans_even m
  · subst hm
    rw [show 2 * m + 1 + 3 = 2 * m + 4 from by ring,
        show 2 * m + 1 + 4 = 2 * m + 5 from by ring,
        show 2 * m + 1 + 1 = 2 * m + 2 from by ring,
        show 2 * m + 1 + 2 = 2 * m + 3 from by ring]
    have : e_val (2 * m + 2) = e_val (2 * m + 1) + 2 * m + 4 := by simp [e_val]; ring
    rw [this]
    exact main_trans_odd m

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 1, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 3, 0, 0, n + 1, e_val n⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_698
