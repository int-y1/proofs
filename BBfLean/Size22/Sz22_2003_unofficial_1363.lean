import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1363: [63/10, 4/33, 143/2, 5/7, 21/13]

Vector representation:
```
-1  2 -1  1  0  0
 2 -1  0  0 -1  0
-1  0  0  0  1  1
 0  0  1 -1  0  0
 0  1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1363

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e, f⟩ => some ⟨a, b+2, c, d+1, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | _ => none

def E : ℕ → ℕ
  | 0 => 1
  | n + 1 => E n + n + 1

def F : ℕ → ℕ
  | 0 => 1
  | n + 1 => F n + 3 * n + 1

theorem E_pos : ∀ n, E n ≥ 1 := by
  intro n; induction n with
  | zero => simp [E]
  | succ n ih => simp only [E]; omega

theorem F_pos : ∀ n, F n ≥ 1 := by
  intro n; induction n with
  | zero => simp [F]
  | succ n ih => simp only [F]; omega

-- R4 repeated: move d to c.
theorem d_to_c : ∀ k, ⟨(0 : ℕ), 0, c, d + k, e, f⟩ [fm]⊢* ⟨0, 0, c + k, d, e, f⟩ := by
  intro k; induction' k with k ih generalizing c d
  · exists 0
  · rw [Nat.add_succ d k]; step fm
    apply stepStar_trans (ih (c := c + 1)); ring_nf; finish

-- R3 drain: decrease a, increase e and f.
theorem r3_drain : ∀ k, ⟨a + k, (0 : ℕ), 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih generalizing a e f
  · exists 0
  · rw [Nat.add_succ a k]; step fm
    apply stepStar_trans (ih (a := a) (e := e + 1) (f := f + 1)); ring_nf; finish

-- R1R1R2 chain: k rounds of (R1, R1, R2).
theorem r1r1r2_chain : ∀ k, ∀ b c d,
    ⟨(2 : ℕ), b, c + 2 * k, d, e + k, f⟩ [fm]⊢* ⟨2, b + 3 * k, c, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b c d
  · exists 0
  · rw [show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (b + 3) c (d + 2)); ring_nf; finish

-- Mixed drain by strong induction on A + 3*B.
theorem mixed_drain : ∀ n, ∀ A B D E F, A + 3 * B = n → A + E ≥ B →
    ⟨A, B, (0 : ℕ), D, E, F⟩ [fm]⊢* ⟨0, 0, 0, D, E + A + B, F + A + 2 * B⟩ := by
  intro n; induction' n using Nat.strongRecOn with n ih
  intro A B D E F hn hae
  rcases B with _ | B
  · -- B = 0
    have hA : A = n := by omega
    subst hA
    have h := r3_drain A (a := 0) (d := D) (e := E) (f := F)
    simp only [Nat.zero_add] at h
    exact h
  · -- B + 1 ≥ 1
    rcases E with _ | E
    · -- E = 0
      rcases A with _ | A
      · omega
      · step fm; step fm
        rw [show 0 + (A + 1) + (B + 1) = 0 + (A + 2) + B from by ring,
            show F + (A + 1) + 2 * (B + 1) = (F + 1) + (A + 2) + 2 * B from by ring]
        exact ih (A + 2 + 3 * B) (by omega) (A + 2) B D 0 (F + 1) rfl (by omega)
    · -- E + 1 ≥ 1
      step fm
      rw [show (E + 1) + A + (B + 1) = E + (A + 2) + B from by ring,
          show F + A + 2 * (B + 1) = F + (A + 2) + 2 * B from by ring]
      exact ih (A + 2 + 3 * B) (by omega) (A + 2) B D E F rfl (by omega)

-- Bounds.
theorem E_even_bound : ∀ k, E (2 * k) ≥ k + 1 := by
  intro k; induction k with
  | zero => simp [E]
  | succ k ih => show E (2 * k + 1 + 1) ≥ k + 1 + 1; simp only [E]; omega

theorem E_even_mixed : ∀ k, 2 + (E (2 * k) - k - 1) ≥ 3 * k := by
  intro k; induction k with
  | zero => simp [E]
  | succ k ih =>
    show 2 + (E (2 * k + 1 + 1) - (k + 1) - 1) ≥ 3 * (k + 1); simp only [E]; omega

theorem E_odd_bound : ∀ k, E (2 * k + 1) ≥ k + 1 := by
  intro k; induction k with
  | zero => simp [E]
  | succ k ih => show E (2 * k + 1 + 1 + 1) ≥ k + 1 + 1; simp only [E]; omega

theorem E_odd_mixed : ∀ k, 1 + (E (2 * k + 1) - k - 1) ≥ 3 * k + 2 := by
  intro k; induction k with
  | zero => simp [E]
  | succ k ih =>
    show 1 + (E (2 * k + 1 + 1 + 1) - (k + 1) - 1) ≥ 3 * (k + 1) + 2; simp only [E]; omega

-- Helper: E(2k) decomposition for even case.
theorem E_even_decomp (k : ℕ) :
    ∃ e₀, E (2 * k) = e₀ + k + 1 ∧ E (2 * k + 1) = e₀ + 3 * k + 2 ∧
    2 + e₀ ≥ 3 * k := by
  refine ⟨E (2 * k) - k - 1, ?_, ?_, ?_⟩
  · have := E_even_bound k; omega
  · have := E_even_bound k; simp only [E]; omega
  · exact E_even_mixed k

-- Helper: F(2k) decomposition for even case.
theorem F_even_decomp (k : ℕ) :
    ∃ f₀, F (2 * k) = f₀ + 1 ∧ F (2 * k + 1) = f₀ + 6 * k + 2 := by
  refine ⟨F (2 * k) - 1, ?_, ?_⟩
  · have := F_pos (2 * k); omega
  · have := F_pos (2 * k); simp only [F]; omega

-- Helper: E(2k+1) decomposition for odd case.
theorem E_odd_decomp (k : ℕ) :
    ∃ e₀, E (2 * k + 1) = e₀ + k + 1 ∧ E (2 * k + 2) = e₀ + 3 * k + 3 ∧
    1 + e₀ ≥ 3 * k + 2 := by
  refine ⟨E (2 * k + 1) - k - 1, ?_, ?_, ?_⟩
  · have := E_odd_bound k; omega
  · show E (2 * k + 1 + 1) = _; simp only [E]; omega
  · exact E_odd_mixed k

-- Helper: F(2k+1) decomposition for odd case.
theorem F_odd_decomp (k : ℕ) :
    ∃ f₀, F (2 * k + 1) = f₀ + 1 ∧ F (2 * k + 2) = f₀ + 6 * k + 5 := by
  refine ⟨F (2 * k + 1) - 1, ?_, ?_⟩
  · have := F_pos (2 * k + 1); omega
  · show F (2 * k + 1 + 1) = _; simp only [F]; omega

-- Even transition.
theorem trans_even (k : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * k, E (2 * k), F (2 * k)⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * k + 1, E (2 * k + 1), F (2 * k + 1)⟩ := by
  obtain ⟨e₀, hEk, hE1, hmixed⟩ := E_even_decomp k
  obtain ⟨f₀, hFk, hF1⟩ := F_even_decomp k
  rw [hEk, hFk, hE1, hF1, show (2 * k : ℕ) = 0 + 2 * k from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (2 * k) (c := 0) (d := 0))
  step fm
  rw [show e₀ + k + 1 = (e₀ + k) + 1 from by ring]; step fm
  apply stepStar_trans (r1r1r2_chain k 0 0 1 (e := e₀) (f := f₀))
  simp only [Nat.zero_add]
  rw [show e₀ + 3 * k + 2 = e₀ + 2 + 3 * k from by ring,
      show f₀ + 6 * k + 2 = f₀ + 2 + 2 * (3 * k) from by ring,
      show (2 * k + 1 : ℕ) = 1 + 2 * k from by ring]
  exact mixed_drain _ 2 (3 * k) (1 + 2 * k) e₀ f₀ rfl (by omega)

-- Odd transition.
theorem trans_odd (k : ℕ) :
    ⟨(0 : ℕ), 0, 0, 2 * k + 1, E (2 * k + 1), F (2 * k + 1)⟩ [fm]⊢⁺
    ⟨0, 0, 0, 2 * k + 2, E (2 * k + 2), F (2 * k + 2)⟩ := by
  obtain ⟨e₀, hEk, hE1, hmixed⟩ := E_odd_decomp k
  obtain ⟨f₀, hFk, hF1⟩ := F_odd_decomp k
  rw [hEk, hFk, hE1, hF1, show (2 * k + 1 : ℕ) = 0 + (2 * k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_c (2 * k + 1) (c := 0) (d := 0))
  step fm
  rw [show e₀ + k + 1 = (e₀ + k) + 1 from by ring]; step fm
  rw [show (0 : ℕ) + (2 * k + 1) = 1 + 2 * k from by ring]
  apply stepStar_trans (r1r1r2_chain k 0 1 1 (e := e₀) (f := f₀))
  simp only [Nat.zero_add]
  step fm
  rw [show e₀ + 3 * k + 3 = e₀ + 1 + (3 * k + 2) from by ring,
      show f₀ + 6 * k + 5 = f₀ + 1 + 2 * (3 * k + 2) from by ring]
  show ⟨1, 3 * k + 2, 0, 1 + 2 * k + 1, e₀, f₀⟩ [fm]⊢*
    ⟨0, 0, 0, 2 * k + 2, e₀ + 1 + (3 * k + 2), f₀ + 1 + 2 * (3 * k + 2)⟩
  rw [show (1 : ℕ) + 2 * k + 1 = 2 * k + 2 from by ring]
  exact mixed_drain _ 1 (3 * k + 2) (2 * k + 2) e₀ f₀ rfl (by omega)

theorem main_trans (n : ℕ) :
    ⟨(0 : ℕ), 0, 0, n, E n, F n⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 1, E (n + 1), F (n + 1)⟩ := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk; exact trans_even k
  · subst hk; exact trans_odd k

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, E 0, F 0⟩)
  · simp only [E, F]; execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n, E n, F n⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1363
