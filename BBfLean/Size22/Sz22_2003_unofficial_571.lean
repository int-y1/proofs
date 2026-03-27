import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #571: [35/6, 100/77, 121/2, 3/5, 7/11]

Vector representation:
```
-1 -1  1  1  0
 2  0  2 -1 -1
-1  0  0  0  2
 0  1 -1  0  0
 0  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_571

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b, c+2, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | _ => none

-- R3 repeated: drain a to e
theorem a_to_e : ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e+2*k⟩ := by
  have many_step : ∀ k a e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e+2*k⟩ := by
    intro k; induction' k with k h <;> intro a e
    · exists 0
    rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (h _ _); ring_nf; finish
  exact many_step k a e

-- R4 repeated: drain c to b
theorem c_to_b : ⟨0, b, c+k, 0, e⟩ [fm]⊢* ⟨0, b+k, c, 0, e⟩ := by
  have many_step : ∀ k b, ⟨0, b, c+k, 0, e⟩ [fm]⊢* ⟨0, b+k, c, 0, e⟩ := by
    intro k; induction' k with k h <;> intro b
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring]; step fm
    apply stepStar_trans (h _); ring_nf; finish
  exact many_step k b

-- R2 repeated: consume d and e in parallel
theorem r2_chain : ⟨a, 0, c, d+m, e+m⟩ [fm]⊢* ⟨a+2*m, 0, c+2*m, d, e⟩ := by
  have many_step : ∀ m a c, ⟨a, 0, c, d+m, e+m⟩ [fm]⊢* ⟨a+2*m, 0, c+2*m, d, e⟩ := by
    intro m; induction' m with m h <;> intro a c
    · exists 0
    rw [show d + (m + 1) = d + m + 1 from by ring,
        show e + (m + 1) = e + m + 1 from by ring]
    step fm; apply stepStar_trans (h _ _); ring_nf; finish
  exact many_step m a c

-- R3,R2,R2 drain: convert d (even) to a and c
theorem drain : ⟨a+1, 0, c, d+2*k, 0⟩ [fm]⊢* ⟨a+3*k+1, 0, c+4*k, d, 0⟩ := by
  have many_step : ∀ k a c, ⟨a+1, 0, c, d+2*k, 0⟩ [fm]⊢* ⟨a+3*k+1, 0, c+4*k, d, 0⟩ := by
    intro k; induction' k with k h <;> intro a c
    · exists 0
    rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (h _ _); ring_nf; finish
  exact many_step k a c

-- One round of R1,R1,R2
theorem r1r1r2_round : ⟨2, b+2, c, d, e+1⟩ [fm]⊢* ⟨2, b, c+4, d+1, e⟩ := by
  step fm; step fm; step fm; ring_nf; finish

-- Chain of R1,R1,R2 rounds
theorem r1r1r2_chain : ⟨2, b+2*k, c, d, e+k⟩ [fm]⊢* ⟨2, b, c+4*k, d+k, e⟩ := by
  have many_step : ∀ k b c d e, ⟨2, b+2*k, c, d, e+k⟩ [fm]⊢* ⟨2, b, c+4*k, d+k, e⟩ := by
    intro k; induction' k with k h <;> intro b c d e
    · exists 0
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    apply stepStar_trans r1r1r2_round
    apply stepStar_trans (h _ _ _ _); ring_nf; finish
  exact many_step k b c d e

-- Final R1,R1 when b=2 (last pair)
theorem last_r1r1 : ⟨2, 2, c, d, e⟩ [fm]⊢* ⟨0, 0, c+2, d+2, e⟩ := by
  step fm; step fm; ring_nf; finish

-- Full interleaved phase: (2, 2k+2, 2, 0, e+k) -> (0, 0, 4k+4, k+2, e)
theorem interleaved : ⟨2, 2*k+2, 2, 0, e+k⟩ [fm]⊢* ⟨0, 0, 4*k+4, k+2, e⟩ := by
  rw [show 2 * k + 2 = 2 + 2 * k from by ring]
  apply stepStar_trans (r1r1r2_chain (b := 2))
  simp only [Nat.zero_add]
  apply stepStar_trans last_r1r1
  ring_nf; finish

-- R5+R2 opening
theorem r5_r2_open : ⟨0, b, 0, 0, e+1+1⟩ [fm]⊢* ⟨2, b, 2, 0, e⟩ := by
  step fm; step fm; ring_nf; finish

-- Full cycle (⊢* version): parameterized with m = 2a-k >= 1 and j = k-a >= 0.
theorem main_star (ha : 2*a ≥ k+1) (hak : a ≤ k) :
    ⟨a+1, 0, 2*k+2, 0, 0⟩ [fm]⊢* ⟨a+k+3, 0, 6*k+8, 0, 0⟩ := by
  obtain ⟨m, hm⟩ : ∃ m, 2*a = m + k := ⟨2*a - k, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, k = a + j := ⟨k - a, by omega⟩
  have hm1 : m ≥ 1 := by omega
  have ha_eq : a = m + j := by omega
  subst ha_eq; rw [hj]
  -- Phase 1: R3 drains a to e
  rw [show (m + j) + 1 = 0 + ((m + j) + 1) from by ring]
  apply stepStar_trans (a_to_e (c := 2*((m+j)+j)+2) (k := (m+j)+1) (a := 0) (e := 0))
  simp only [Nat.zero_add]
  -- Phase 2: R4 drains c to b
  rw [show 2 * ((m + j) + j) + 2 = 0 + (2 * ((m + j) + j) + 2) from by ring]
  apply stepStar_trans (c_to_b (c := 0) (b := 0))
  simp only [Nat.zero_add]
  -- Phase 3: R5, R2 opening
  rw [show 2 * ((m + j) + 1) = (2 * (m + j)) + 1 + 1 from by ring]
  apply stepStar_trans (r5_r2_open (b := 2*((m+j)+j)+2) (e := 2*(m+j)))
  -- Phase 4: interleaved [R1,R1,R2] x k + final R1,R1
  rw [show 2 * (m + j) = m + ((m + j) + j) from by ring]
  apply stepStar_trans (interleaved (k := (m+j)+j) (e := m))
  -- Phase 5: R2 x m (via suffices to match tuple form exactly)
  suffices h : (0, 0, 4*((m+j)+j)+4, (2*j+2)+m, 0+m) [fm]⊢*
      (m+j + ((m+j)+j) + 3, 0, 6*((m+j)+j) + 8, 0, 0) by
    refine stepStar_trans ?_ h; ring_nf; finish
  apply stepStar_trans (r2_chain (a := 0) (c := 4*((m+j)+j)+4) (d := 2*j+2) (m := m) (e := 0))
  simp only [Nat.zero_add]
  -- Phase 6: R3,R2,R2 drain x (j+1) (via suffices to match tuple form exactly)
  suffices hdr : ((2*m-1)+1, 0, 4*((m+j)+j)+4+2*m, 0+2*(j+1), 0) [fm]⊢*
      (m+j+((m+j)+j)+3, 0, 6*((m+j)+j)+8, 0, 0) by
    have : (2*m, 0, 4*((m+j)+j)+4+2*m, 2*j+2, 0) =
        ((2*m-1)+1, 0, 4*((m+j)+j)+4+2*m, 0+2*(j+1), 0) := by ext <;> simp <;> omega
    rw [this]; exact hdr
  apply stepStar_trans (drain (a := 2*m-1) (c := 4*((m+j)+j)+4+2*m) (d := 0) (k := j+1))
  rw [show 2*m-1 + 3*(j+1) + 1 = m+j+((m+j)+j)+3 from by omega,
      show 4*((m+j)+j)+4+2*m + 4*(j+1) = 6*((m+j)+j)+8 from by ring]
  finish

theorem main_trans (ha : 2*a ≥ k+1) (hak : a ≤ k) :
    ⟨a+1, 0, 2*k+2, 0, 0⟩ [fm]⊢⁺ ⟨a+k+3, 0, 6*k+8, 0, 0⟩ :=
  stepStar_stepPlus (main_star ha hak) (by simp [Q]; omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 8, 0, 0⟩) (by execute fm 13)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a k, q = ⟨a+1, 0, 2*k+2, 0, 0⟩ ∧ 2*a ≥ k+1 ∧ a ≤ k)
  · intro c ⟨a, k, hq, ha, hak⟩; subst hq
    exact ⟨⟨a+k+3, 0, 6*k+8, 0, 0⟩,
      ⟨a+k+2, 3*k+3, by ring_nf, by omega, by omega⟩,
      main_trans ha hak⟩
  · exact ⟨3, 3, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_571
