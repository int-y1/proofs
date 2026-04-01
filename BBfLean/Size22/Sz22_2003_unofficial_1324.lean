import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1324: [63/10, 175/33, 2/3, 11/7, 15/2]

Vector representation:
```
-1  2 -1  1  0
 0 -1  2  1 -1
 1 -1  0  0  0
 0  0  0 -1  1
-1  1  1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1324

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+2, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem d_to_e : ∀ k, ∀ d e, ⟨a, (0 : ℕ), 0, d + k, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · ring_nf; finish
  · rw [Nat.add_succ, show e + (k + 1) = (e + 1) + k from by ring]
    step fm; apply stepStar_trans (ih d (e + 1)); ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ r B D e,
    ⟨2 * k + r, B + 1, (0 : ℕ), D, e + k⟩ [fm]⊢*
    ⟨r, B + 3 * k + 1, 0, D + 3 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro r B D e
  · ring_nf; finish
  · rw [show 2 * (k + 1) + r = (2 * k + r) + 2 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    step fm; step fm; step fm
    rw [show B + 3 * (k + 1) + 1 = (B + 3) + 3 * k + 1 from by ring,
        show D + 3 * (k + 1) = (D + 3) + 3 * k from by ring]
    apply stepStar_trans (ih r (B + 3) (D + 3) e); ring_nf; finish

theorem r2_drain : ∀ k, ∀ b c d,
    ⟨(0 : ℕ), b + k, c, d, k⟩ [fm]⊢* ⟨0, b, c + 2 * k, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · ring_nf; finish
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show c + 2 * (k + 1) = (c + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    step fm; apply stepStar_trans (ih b (c + 2) (d + 1)); ring_nf; finish

theorem r3r1_chain : ∀ k, ∀ b d,
    ⟨(0 : ℕ), b + 1, k, d, 0⟩ [fm]⊢* ⟨0, b + k + 1, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · ring_nf; finish
  · rw [show b + (k + 1) + 1 = (b + 1) + k + 1 from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) (d + 1)); ring_nf; finish

theorem r3_drain : ∀ k, ∀ a d,
    ⟨a, k, (0 : ℕ), d, 0⟩ [fm]⊢* ⟨a + k, 0, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · ring_nf; finish
  · rw [show a + (k + 1) = (a + 1) + k from by ring]
    step fm; apply stepStar_trans (ih (a + 1) d); ring_nf; finish

-- Even: a = 2(m+1), d = m+e, b'+1+e = 3m+3
theorem main_even (m b' e : ℕ) (hbe : b' + 1 + e = 3 * m + 3) :
    ⟨2 * m + 2, (0 : ℕ), 0, m + e, 0⟩ [fm]⊢⁺
    ⟨b' + 2 * e + 1, 0, 0, 3 * m + 3 * e + 1, 0⟩ := by
  have h1 : ⟨2 * m + 2, (0 : ℕ), 0, m + e, 0⟩ [fm]⊢*
      ⟨2 * m + 2, 0, 0, 0, m + e⟩ := by
    have := d_to_e (a := 2 * m + 2) (m + e) 0 0
    rw [show (0 : ℕ) + (m + e) = m + e from by ring] at this; exact this
  have h2 : ⟨2 * m + 2, (0 : ℕ), 0, 0, m + e⟩ [fm]⊢⁺
      ⟨2 * m, 3, 0, 1, m + e⟩ := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring,
        show (3 : ℕ) = 2 + 1 from by ring]
    step fm; step fm; finish
  have h3 : ⟨2 * m, (3 : ℕ), 0, 1, m + e⟩ [fm]⊢*
      ⟨0, 3 * m + 3, 0, 3 * m + 1, e⟩ := by
    rw [show m + e = e + m from by ring,
        show 2 * m = 2 * m + 0 from by ring]
    have := r2r1r1_chain m 0 2 1 e
    rw [show 2 + 3 * m + 1 = 3 * m + 3 from by ring,
        show 1 + 3 * m = 3 * m + 1 from by ring] at this; exact this
  have h4 : ⟨(0 : ℕ), 3 * m + 3, 0, 3 * m + 1, e⟩ [fm]⊢*
      ⟨0, b' + 1, 2 * e, 3 * m + 1 + e, 0⟩ := by
    rw [show 3 * m + 3 = (b' + 1) + e from by omega,
        show 2 * e = 0 + 2 * e from by ring,
        show 3 * m + 1 + e = (3 * m + 1) + e from by ring]
    exact r2_drain e (b' + 1) 0 (3 * m + 1)
  have h5 : ⟨(0 : ℕ), b' + 1, 2 * e, 3 * m + 1 + e, 0⟩ [fm]⊢*
      ⟨0, b' + 2 * e + 1, 0, 3 * m + 3 * e + 1, 0⟩ := by
    rw [show b' + 2 * e + 1 = b' + 2 * e + 1 from rfl,
        show 3 * m + 3 * e + 1 = (3 * m + 1 + e) + 2 * e from by ring]
    exact r3r1_chain (2 * e) b' (3 * m + 1 + e)
  have h6 : ⟨(0 : ℕ), b' + 2 * e + 1, 0, 3 * m + 3 * e + 1, 0⟩ [fm]⊢*
      ⟨b' + 2 * e + 1, 0, 0, 3 * m + 3 * e + 1, 0⟩ := by
    have := r3_drain (b' + 2 * e + 1) 0 (3 * m + 3 * e + 1)
    rw [show (0 : ℕ) + (b' + 2 * e + 1) = b' + 2 * e + 1 from by ring] at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 h6))))

-- Odd: a = 2m+3, d = m+e'+1, b'+1+e' = 3m+4
theorem main_odd (m b' e' : ℕ) (hbe : b' + 1 + e' = 3 * m + 4) :
    ⟨2 * m + 3, (0 : ℕ), 0, m + e' + 1, 0⟩ [fm]⊢⁺
    ⟨b' + 2 * e' + 2, 0, 0, 3 * m + 3 * e' + 4, 0⟩ := by
  have h1 : ⟨2 * m + 3, (0 : ℕ), 0, m + e' + 1, 0⟩ [fm]⊢*
      ⟨2 * m + 3, 0, 0, 0, m + e' + 1⟩ := by
    have := d_to_e (a := 2 * m + 3) (m + e' + 1) 0 0
    rw [show (0 : ℕ) + (m + e' + 1) = m + e' + 1 from by ring] at this; exact this
  have h2 : ⟨2 * m + 3, (0 : ℕ), 0, 0, m + e' + 1⟩ [fm]⊢⁺
      ⟨2 * m + 1, 3, 0, 1, m + e' + 1⟩ := by
    rw [show 2 * m + 3 = (2 * m + 2) + 1 from by ring,
        show (3 : ℕ) = 2 + 1 from by ring]
    step fm; step fm; finish
  have h3 : ⟨2 * m + 1, (3 : ℕ), 0, 1, m + e' + 1⟩ [fm]⊢*
      ⟨1, 3 * m + 3, 0, 3 * m + 1, e' + 1⟩ := by
    rw [show m + e' + 1 = (e' + 1) + m from by ring,
        show 2 * m + 1 = 2 * m + 1 from rfl]
    have := r2r1r1_chain m 1 2 1 (e' + 1)
    rw [show 2 + 3 * m + 1 = 3 * m + 3 from by ring,
        show 1 + 3 * m = 3 * m + 1 from by ring] at this; exact this
  have h4 : ⟨(1 : ℕ), 3 * m + 3, 0, 3 * m + 1, e' + 1⟩ [fm]⊢*
      ⟨0, 3 * m + 4, 1, 3 * m + 3, e'⟩ := by
    rw [show 3 * m + 3 = (3 * m + 2) + 1 from by ring,
        show e' + 1 = e' + 1 from rfl,
        show 3 * m + 4 = (3 * m + 2) + 2 from by ring,
        show 3 * m + 3 = (3 * m + 1) + 2 from by ring]
    step fm; step fm; finish
  have h5 : ⟨(0 : ℕ), 3 * m + 4, 1, 3 * m + 3, e'⟩ [fm]⊢*
      ⟨0, b' + 1, 2 * e' + 1, 3 * m + 3 + e', 0⟩ := by
    rw [show 3 * m + 4 = (b' + 1) + e' from by omega,
        show 2 * e' + 1 = 1 + 2 * e' from by ring,
        show 3 * m + 3 + e' = (3 * m + 3) + e' from by ring]
    exact r2_drain e' (b' + 1) 1 (3 * m + 3)
  have h6 : ⟨(0 : ℕ), b' + 1, 2 * e' + 1, 3 * m + 3 + e', 0⟩ [fm]⊢*
      ⟨0, b' + 2 * e' + 2, 0, 3 * m + 3 * e' + 4, 0⟩ := by
    rw [show b' + 2 * e' + 2 = b' + (2 * e' + 1) + 1 from by ring,
        show 3 * m + 3 * e' + 4 = (3 * m + 3 + e') + (2 * e' + 1) from by ring]
    exact r3r1_chain (2 * e' + 1) b' (3 * m + 3 + e')
  have h7 : ⟨(0 : ℕ), b' + 2 * e' + 2, 0, 3 * m + 3 * e' + 4, 0⟩ [fm]⊢*
      ⟨b' + 2 * e' + 2, 0, 0, 3 * m + 3 * e' + 4, 0⟩ := by
    have := r3_drain (b' + 2 * e' + 2) 0 (3 * m + 3 * e' + 4)
    rw [show (0 : ℕ) + (b' + 2 * e' + 2) = b' + 2 * e' + 2 from by ring] at this; exact this
  exact stepStar_stepPlus_stepPlus h1
    (stepPlus_stepStar_stepPlus h2
      (stepStar_trans h3
        (stepStar_trans h4 (stepStar_trans h5 (stepStar_trans h6 h7)))))

theorem main_trans (a d : ℕ) (hd : d ≥ 1) (ha : a ≤ d + 1) (hd2 : d + 2 ≤ 2 * a) :
    ⟨a, (0 : ℕ), 0, d, 0⟩ [fm]⊢⁺ ⟨a + d + 1, 0, 0, 3 * d + 1, 0⟩ := by
  rcases Nat.even_or_odd a with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le (show m ≥ 1 by omega)
    have key := main_even m' (4 * m' + 2 - d) (d - m')
      (show (4 * m' + 2 - d) + 1 + (d - m') = 3 * m' + 3 by omega)
    have h1 : m' + (d - m') = d := by omega
    have h2 : 2 * m' + 2 = (1 + m') + (1 + m') := by omega
    have h3 : (4 * m' + 2 - d) + 2 * (d - m') + 1 = (1 + m') + (1 + m') + d + 1 := by omega
    have h4 : 3 * m' + 3 * (d - m') + 1 = 3 * d + 1 := by omega
    rw [h1, h2, h3, h4] at key; exact key
  · subst hm
    obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le (show m ≥ 1 by omega)
    have key := main_odd m' (4 * m' + 4 - d) (d - m' - 1)
      (show (4 * m' + 4 - d) + 1 + (d - m' - 1) = 3 * m' + 4 by omega)
    have h1 : m' + (d - m' - 1) + 1 = d := by omega
    have h2 : 2 * m' + 3 = 2 * (1 + m') + 1 := by omega
    have h3 : (4 * m' + 4 - d) + 2 * (d - m' - 1) + 2 = 2 * (1 + m') + 1 + d + 1 := by omega
    have h4 : 3 * m' + 3 * (d - m' - 1) + 4 = 3 * d + 1 := by omega
    rw [h1, h2, h3, h4] at key; exact key

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 5)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 1 ∧ a ≤ d + 1 ∧ d + 2 ≤ 2 * a)
  · intro c ⟨a, d, hq, hd, ha, hd2⟩
    exact ⟨⟨a + d + 1, 0, 0, 3 * d + 1, 0⟩,
      ⟨a + d + 1, 3 * d + 1, rfl, by omega, by omega, by omega⟩,
      hq ▸ main_trans a d hd ha hd2⟩
  · exact ⟨2, 1, rfl, by omega, by omega, by omega⟩

end Sz22_2003_unofficial_1324
