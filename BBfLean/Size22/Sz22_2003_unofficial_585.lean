import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #585: [35/6, 11/2, 8/55, 3/7, 28/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  1
 3  0 -1  0 -1
 0  1  0 -1  0
 2  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6

---

Canonical states are (0, 0, 0, d, e) with e = d*(d+1)/2 + 1.
Each cycle maps (0, 0, 0, d, e) to (0, 0, 0, d+1, e+d+1).
The proof uses progress_nonhalt_simple with A = ℕ x ℕ.
-/

namespace Sz22_2003_unofficial_585

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | _ => none

-- R4 repeated: transfer d to b
theorem d_to_b : ∀ k, ∀ b d e, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R3+R2x3 drain: each round c-=1, e+=2
theorem drain_c : ∀ k, ∀ c D e, ⟨0, 0, c+k, D, e+1⟩ [fm]⊢* ⟨0, 0, c, D, e+2*k+1⟩ := by
  intro k; induction' k with k ih <;> intro c D e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R3+R1x3 chain: b-=3, c+=2, D+=3, E-=1 per round
theorem r3r1_chain : ∀ k, ∀ b c D E,
    ⟨0, b+3*k, c+1, D, E+k⟩ [fm]⊢* ⟨0, b, c+2*k+1, D+3*k, E⟩ := by
  intro k; induction' k with k ih <;> intro b c D E
  · exists 0
  rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring,
      show E + (k + 1) = (E + k) + 1 from by ring]
  step fm; step fm; step fm; step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- tail_b1: b=1 after chain
theorem tail_b1 : ⟨0, 1, c+1, D, E+1⟩ [fm]⊢* ⟨0, 0, c+1, D+1, E+2⟩ := by
  step fm; step fm; step fm; step fm; finish

-- tail_b2: b=2 after chain
theorem tail_b2 : ⟨0, 2, c+1, D, E+1⟩ [fm]⊢* ⟨0, 0, c+2, D+2, E+1⟩ := by
  step fm; step fm; step fm; step fm; finish

-- Opening: d_to_b + R5 + R1x2 (at least 4 steps, so ⊢⁺)
theorem opening : ⟨0, 0, 0, d+2, e+1⟩ [fm]⊢⁺ ⟨0, d, 2, 3, e⟩ := by
  rw [show d+2 = 0 + (d+2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (d+2) 0 0 (e+1))
  simp only [Nat.zero_add]
  step fm; step fm; step fm; finish

-- d=1 base: 7 fixed steps
theorem d1_trans : ⟨0, 0, 0, 1, f+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2, f+3⟩ := by
  step fm; step fm; step fm; step fm
  have h := drain_c 1 0 2 f
  simp only [Nat.zero_add] at h
  convert h using 2

-- d = 3*q+2: opening -> chain -> drain
theorem trans_r0 :
    ⟨0, 0, 0, 3*q+2, 3*q+f+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 3*q+3, 6*q+f+5⟩ := by
  have hopening : (⟨0, 0, 0, 3*q+2, 3*q+f+2⟩ : Q) [fm]⊢⁺ ⟨0, 3*q, 2, 3, 3*q+f+1⟩ := by
    convert opening (d := 3*q) (e := 3*q+f+1) using 2
  have hchain : (⟨0, 3*q, 2, 3, 3*q+f+1⟩ : Q) [fm]⊢* ⟨0, 0, 2*q+2, 3*q+3, 2*q+f+1⟩ := by
    convert r3r1_chain q 0 1 3 (2*q+f+1) using 2; ring_nf
  have hdrain : (⟨0, 0, 2*q+2, 3*q+3, 2*q+f+1⟩ : Q) [fm]⊢* ⟨0, 0, 0, 3*q+3, 6*q+f+5⟩ := by
    convert drain_c (2*q+2) 0 (3*q+3) (2*q+f) using 2; ring_nf
  exact stepPlus_stepStar_stepPlus hopening
    (stepStar_trans hchain hdrain)

-- d = 3*q+3: opening -> chain -> tail_b1 -> drain
theorem trans_r1 :
    ⟨0, 0, 0, 3*q+3, 3*q+f+3⟩ [fm]⊢⁺ ⟨0, 0, 0, 3*q+4, 6*q+f+7⟩ := by
  have hopening : (⟨0, 0, 0, 3*q+3, 3*q+f+3⟩ : Q) [fm]⊢⁺ ⟨0, 3*q+1, 2, 3, 3*q+f+2⟩ := by
    convert opening (d := 3*q+1) (e := 3*q+f+2) using 2
  have hchain : (⟨0, 3*q+1, 2, 3, 3*q+f+2⟩ : Q) [fm]⊢* ⟨0, 1, 2*q+2, 3*q+3, 2*q+f+2⟩ := by
    convert r3r1_chain q 1 1 3 (2*q+f+2) using 2; ring_nf
  have htail : (⟨0, 1, 2*q+2, 3*q+3, 2*q+f+2⟩ : Q) [fm]⊢* ⟨0, 0, 2*q+2, 3*q+4, 2*q+f+3⟩ := by
    convert tail_b1 (c := 2*q+1) (D := 3*q+3) (E := 2*q+f+1) using 2
  have hdrain : (⟨0, 0, 2*q+2, 3*q+4, 2*q+f+3⟩ : Q) [fm]⊢* ⟨0, 0, 0, 3*q+4, 6*q+f+7⟩ := by
    convert drain_c (2*q+2) 0 (3*q+4) (2*q+f+2) using 2; ring_nf
  exact stepPlus_stepStar_stepPlus hopening
    (stepStar_trans hchain (stepStar_trans htail hdrain))

-- d = 3*q+4: opening -> chain -> tail_b2 -> drain
theorem trans_r2 :
    ⟨0, 0, 0, 3*q+4, 3*q+f+4⟩ [fm]⊢⁺ ⟨0, 0, 0, 3*q+5, 6*q+f+9⟩ := by
  have hopening : (⟨0, 0, 0, 3*q+4, 3*q+f+4⟩ : Q) [fm]⊢⁺ ⟨0, 3*q+2, 2, 3, 3*q+f+3⟩ := by
    convert opening (d := 3*q+2) (e := 3*q+f+3) using 2
  have hchain : (⟨0, 3*q+2, 2, 3, 3*q+f+3⟩ : Q) [fm]⊢* ⟨0, 2, 2*q+2, 3*q+3, 2*q+f+3⟩ := by
    convert r3r1_chain q 2 1 3 (2*q+f+3) using 2; ring_nf
  have htail : (⟨0, 2, 2*q+2, 3*q+3, 2*q+f+3⟩ : Q) [fm]⊢* ⟨0, 0, 2*q+3, 3*q+5, 2*q+f+3⟩ := by
    convert tail_b2 (c := 2*q+1) (D := 3*q+3) (E := 2*q+f+2) using 2
  have hdrain : (⟨0, 0, 2*q+3, 3*q+5, 2*q+f+3⟩ : Q) [fm]⊢* ⟨0, 0, 0, 3*q+5, 6*q+f+9⟩ := by
    convert drain_c (2*q+3) 0 (3*q+5) (2*q+f+2) using 2; ring_nf
  exact stepPlus_stepStar_stepPlus hopening
    (stepStar_trans hchain (stepStar_trans htail hdrain))

-- Main transition: C(d,f) = (0,0,0,d+1,d+f+1) -> (0,0,0,d+2,2*d+f+3)
theorem main_trans (d f : ℕ) :
    (⟨0, 0, 0, d+1, d+f+1⟩ : Q) [fm]⊢⁺ ⟨0, 0, 0, d+2, 2*d+f+3⟩ := by
  rcases d with _ | d
  · simp only [Nat.zero_add, show 2*0+f+3 = f+3 from by ring]
    exact d1_trans
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ d = 3 * q + r :=
    ⟨d / 3, d % 3, Nat.mod_lt _ (by omega), by omega⟩
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 from by omega) with rfl | rfl | rfl
  · convert trans_r0 (q := q) (f := f) using 2 ; ring_nf
  · convert trans_r1 (q := q) (f := f) using 2 ; ring_nf
  · convert trans_r2 (q := q) (f := f) using 2 ; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, f⟩ ↦ ⟨0, 0, 0, d+1, d+f+1⟩) ⟨0, 1⟩
  intro ⟨d, f⟩
  exact ⟨⟨d+1, d+f+1⟩, by convert main_trans d f using 2 ; ring_nf⟩

end Sz22_2003_unofficial_585
