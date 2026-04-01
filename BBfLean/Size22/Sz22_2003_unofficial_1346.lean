import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1346: [63/10, 33/2, 8/77, 5/3, 7/5]

Vector representation:
```
-1  2 -1  1  0
-1  1  0  0  1
 3  0  0 -1 -1
 0 -1  1  0  0
 0  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1346

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R4 chain: transfer b to c (a=0, d=0)
theorem b_to_c : ∀ k, ∀ b c e,
    ⟨(0 : ℕ), b + k, c, (0 : ℕ), e⟩ [fm]⊢* ⟨(0 : ℕ), b, c + k, (0 : ℕ), e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih b (c + 1) e); ring_nf; finish

-- R1^3/R3 interleaved chain
theorem r1r3_chain : ∀ k, ∀ b c d e,
    ⟨(3 : ℕ), b, c + 3 * k, d, e + k⟩ [fm]⊢*
    ⟨(3 : ℕ), b + 6 * k, c, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · simp; exists 0
  · rw [show c + 3 * (k + 1) = (c + 3 * k + 2) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show c + 3 * k + 2 = (c + 3 * k + 1) + 1 from by ring]
    step fm
    rw [show c + 3 * k + 1 = (c + 3 * k) + 1 from by ring]
    step fm; step fm
    rw [show b + 2 + 2 + 2 = (b + 6) from by ring]
    apply stepStar_trans (ih (b + 6) c (d + 2) e); ring_nf; finish

-- R3/R2^3 chain
theorem r3r2_chain : ∀ k, ∀ b d e,
    ⟨(0 : ℕ), b, (0 : ℕ), d + k, e + 1⟩ [fm]⊢*
    ⟨(0 : ℕ), b + 3 * k, (0 : ℕ), d, e + 2 * k + 1⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · simp; exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm; step fm
    rw [show e + 1 + 1 + 1 = (e + 2) + 1 from by ring]
    apply stepStar_trans (ih (b + 3) d (e + 2)); ring_nf; finish

-- Case c mod 3 = 0
theorem main_mod0 (q e : ℕ) (he : e ≥ q) :
    ⟨(0 : ℕ), (0 : ℕ), 3 * q + 1, (0 : ℕ), e + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 12 * q + 3, (0 : ℕ), 3 * q + e + 3⟩ := by
  rw [show 3 * q + 1 = (3 * q) + 1 from by ring]
  step fm; step fm
  rw [show 3 * q = 0 + 3 * q from by ring,
      show (e : ℕ) = (e - q) + q from by omega]
  apply stepStar_trans (r1r3_chain q 0 0 0 (e - q))
  rw [show 0 + 6 * q = 6 * q from by ring, show 0 + 2 * q = 2 * q from by ring]
  step fm; step fm; step fm
  rw [show 6 * q + 1 + 1 + 1 = 6 * q + 3 from by ring,
      show e - q + 1 + 1 + 1 = (e - q + 2) + 1 from by ring,
      show 2 * q = 0 + 2 * q from by ring]
  apply stepStar_trans (r3r2_chain (2 * q) (6 * q + 3) 0 (e - q + 2))
  rw [show 6 * q + 3 + 3 * (2 * q) = 0 + (12 * q + 3) from by ring]
  apply stepStar_trans (b_to_c (12 * q + 3) 0 0 (e - q + 2 + 2 * (2 * q) + 1))
  rw [show 0 + (12 * q + 3) = 12 * q + 3 from by ring,
      show e - q + 2 + 2 * (2 * q) + 1 = 3 * q + (e - q + q) + 3 from by omega,
      Nat.sub_add_cancel he, show 0 + 3 * q + e + 3 = 3 * q + e + 3 from by ring]
  finish

-- Case c mod 3 = 1
theorem main_mod1 (q e : ℕ) (he : e ≥ q) :
    ⟨(0 : ℕ), (0 : ℕ), 3 * q + 2, (0 : ℕ), e + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 12 * q + 7, (0 : ℕ), 3 * q + e + 4⟩ := by
  rw [show 3 * q + 2 = (3 * q + 1) + 1 from by ring]
  step fm; step fm
  rw [show 3 * q + 1 = 1 + 3 * q from by ring,
      show (e : ℕ) = (e - q) + q from by omega]
  apply stepStar_trans (r1r3_chain q 0 1 0 (e - q))
  rw [show 0 + 6 * q = 6 * q from by ring, show 0 + 2 * q = 2 * q from by ring]
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm; step fm; step fm
  rw [show 6 * q + 2 + 1 + 1 = 6 * q + 4 from by ring,
      show e - q + 1 + 1 = (e - q + 1) + 1 from by ring,
      show 2 * q + 1 = 0 + (2 * q + 1) from by ring]
  apply stepStar_trans (r3r2_chain (2 * q + 1) (6 * q + 4) 0 (e - q + 1))
  rw [show 6 * q + 4 + 3 * (2 * q + 1) = 0 + (12 * q + 7) from by ring]
  apply stepStar_trans (b_to_c (12 * q + 7) 0 0 (e - q + 1 + 2 * (2 * q + 1) + 1))
  rw [show 0 + (12 * q + 7) = 12 * q + 7 from by ring,
      show e - q + 1 + 2 * (2 * q + 1) + 1 = 3 * q + (e - q + q) + 4 from by omega,
      Nat.sub_add_cancel he]
  finish

-- Case c mod 3 = 2
theorem main_mod2 (q e : ℕ) (he : e ≥ q) :
    ⟨(0 : ℕ), (0 : ℕ), 3 * q + 3, (0 : ℕ), e + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 12 * q + 11, (0 : ℕ), 3 * q + e + 5⟩ := by
  rw [show 3 * q + 3 = (3 * q + 2) + 1 from by ring]
  step fm; step fm
  rw [show 3 * q + 2 = 2 + 3 * q from by ring,
      show (e : ℕ) = (e - q) + q from by omega]
  apply stepStar_trans (r1r3_chain q 0 2 0 (e - q))
  rw [show 0 + 6 * q = 6 * q from by ring, show 0 + 2 * q = 2 * q from by ring]
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm; step fm
  rw [show 6 * q + 2 + 2 + 1 = 6 * q + 5 from by ring,
      show 2 * q + 1 + 1 = 2 * q + 2 from by ring,
      show e - q + 1 = (e - q) + 1 from by ring,
      show 2 * q + 2 = 0 + (2 * q + 2) from by ring]
  apply stepStar_trans (r3r2_chain (2 * q + 2) (6 * q + 5) 0 (e - q))
  rw [show 6 * q + 5 + 3 * (2 * q + 2) = 0 + (12 * q + 11) from by ring]
  apply stepStar_trans (b_to_c (12 * q + 11) 0 0 (e - q + 2 * (2 * q + 2) + 1))
  rw [show 0 + (12 * q + 11) = 12 * q + 11 from by ring,
      show e - q + 2 * (2 * q + 2) + 1 = 3 * q + (e - q + q) + 5 from by omega,
      Nat.sub_add_cancel he]
  finish

-- Combined main transition
theorem main_trans (c e : ℕ) (he : 3 * e ≥ c) :
    ⟨(0 : ℕ), (0 : ℕ), c + 1, (0 : ℕ), e + 1⟩ [fm]⊢⁺
    ⟨(0 : ℕ), (0 : ℕ), 4 * c + 3, (0 : ℕ), c + e + 3⟩ := by
  have hmod : c % 3 < 3 := Nat.mod_lt _ (by omega)
  have hq_eq := Nat.div_add_mod c 3
  set q := c / 3
  have hr : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by omega
  rcases hr with hr | hr | hr
  · have hc : c = 3 * q := by omega
    rw [hc, show 4 * (3 * q) + 3 = 12 * q + 3 from by ring,
        show 3 * q + e + 3 = 3 * q + e + 3 from rfl,
        show 3 * q + 1 = 3 * q + 1 from rfl]
    exact main_mod0 q e (by omega)
  · have hc : c = 3 * q + 1 := by omega
    rw [hc, show 4 * (3 * q + 1) + 3 = 12 * q + 7 from by ring,
        show 3 * q + 1 + e + 3 = 3 * q + e + 4 from by ring,
        show 3 * q + 1 + 1 = 3 * q + 2 from by ring]
    exact main_mod1 q e (by omega)
  · have hc : c = 3 * q + 2 := by omega
    rw [hc, show 4 * (3 * q + 2) + 3 = 12 * q + 11 from by ring,
        show 3 * q + 2 + e + 3 = 3 * q + e + 5 from by ring,
        show 3 * q + 2 + 1 = 3 * q + 3 from by ring]
    exact main_mod2 q e (by omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ c e, q = ⟨0, 0, c + 1, 0, e + 1⟩ ∧ 3 * e ≥ c)
  · intro s ⟨c, e, hq, he⟩
    subst hq
    exact ⟨⟨0, 0, 4 * c + 3, 0, c + e + 3⟩,
      ⟨4 * c + 2, c + e + 2, by ring_nf, by omega⟩,
      main_trans c e he⟩
  · exact ⟨0, 0, rfl, by omega⟩

end Sz22_2003_unofficial_1346
