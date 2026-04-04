import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1878: [9/35, 5/33, 14/3, 121/7, 63/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  1  0 -1
 1 -1  0  1  0
 0  0  0 -1  2
-1  2  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1878

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

theorem d_to_e : ∀ k, ∀ d, ⟨a, 0, 0, d + k, 0⟩ [fm]⊢* ⟨a, 0, 0, d, 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (d + 1))
    step fm; ring_nf; finish

theorem drain_c0 : ⟨a + 1, 0, 0, 0, e + 4⟩ [fm]⊢* ⟨a, 0, 3, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem drain_cpos : ⟨a + 1, 0, c + 1, 0, e + 4⟩ [fm]⊢* ⟨a, 0, c + 4, 0, e⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; finish

theorem drain_loop : ∀ k, ∀ a r, ⟨a + k, 0, 3, 0, 4 * k + r⟩ [fm]⊢*
    ⟨a, 0, 3 * k + 3, 0, r⟩ := by
  intro k; induction' k with k ih <;> intro a r
  · ring_nf; exists 0
  · rw [show a + (k + 1) = (a + 1) + k from by ring,
        show 4 * (k + 1) + r = 4 * k + (r + 4) from by ring]
    apply stepStar_trans (ih (a + 1) (r + 4))
    rw [show 3 * k + 3 = (3 * k + 2) + 1 from by omega]
    apply stepStar_trans (drain_cpos (a := a) (c := 3 * k + 2) (e := r))
    rw [show 3 * k + 2 + 4 = 3 * (k + 1) + 3 from by omega]; finish

theorem r3_chain : ∀ k, ∀ a d, ⟨a, k, 0, d, 0⟩ [fm]⊢* ⟨a + k, 0, 0, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 1) (d + 1))
    ring_nf; finish

theorem r3r1_to_canonical : ∀ k, ∀ a b,
    ⟨a, b + 1, k, 0, 0⟩ [fm]⊢* ⟨a + 2 * k + b + 1, 0, 0, b + k + 1, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · have h := r3_chain (b + 1) a 0
    rw [show 0 + (b + 1) = b + 0 + 1 from by ring,
        show a + (b + 1) = a + 2 * 0 + b + 1 from by ring] at h
    exact h
  · step fm
    step fm
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (b + 1))
    ring_nf; finish

theorem phase3_e0 :
    ⟨a + 1, 0, c + 1, 0, 0⟩ [fm]⊢⁺ ⟨a + 2 * c + 4, 0, 0, c + 4, 0⟩ := by
  step fm -- R5: (a, 2, c+1, 1, 0)
  step fm -- R1: (a, 4, c, 0, 0)
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  have h := r3r1_to_canonical c a 3
  rw [show a + 2 * c + 3 + 1 = a + 2 * c + 4 from by ring,
      show 3 + c + 1 = c + 4 from by ring] at h
  exact h

theorem phase3_e2_cpos :
    ⟨a + 1, 0, c + 1, 0, 2⟩ [fm]⊢⁺ ⟨a + 2 * c + 6, 0, 0, c + 4, 0⟩ := by
  step fm -- R5
  step fm -- R1
  step fm -- R2
  step fm -- R2
  step fm -- R3
  step fm -- R1
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  have h := r3r1_to_canonical (c + 1) (a + 1) 2
  rw [show a + 1 + 2 * (c + 1) + 2 + 1 = a + 2 * c + 6 from by ring,
      show 2 + (c + 1) + 1 = c + 4 from by ring] at h
  exact h

theorem phase3_e2_c0 : ⟨a + 1, 0, 0, 0, 2⟩ [fm]⊢⁺ ⟨a + 4, 0, 0, 3, 0⟩ := by
  execute fm 9

theorem full_drain_even : ∀ m, ⟨a + m + 1, 0, 0, 0, 4 * m + 4⟩ [fm]⊢*
    ⟨a, 0, 3 * m + 3, 0, 0⟩ := by
  intro m
  rw [show 4 * m + 4 = (4 * m) + 4 from by ring]
  apply stepStar_trans
  show ⟨a + m + 1, 0, 0, 0, 4 * m + 4⟩ [fm]⊢* ⟨a + m, 0, 3, 0, 4 * m⟩
  · exact drain_c0 (a := a + m) (e := 4 * m)
  rw [show 4 * m = 4 * m + 0 from by ring]
  exact drain_loop m a 0

theorem full_drain_odd : ∀ m, ⟨a + m, 0, 0, 0, 4 * m + 2⟩ [fm]⊢*
    ⟨a, 0, 3 * m, 0, 2⟩ := by
  intro m; rcases m with _ | m
  · simp; exists 0
  · rw [show a + (m + 1) = a + m + 1 from by ring,
        show 4 * (m + 1) + 2 = (4 * m + 2) + 4 from by ring]
    apply stepStar_trans
    show ⟨a + m + 1, 0, 0, 0, (4 * m + 2) + 4⟩ [fm]⊢* ⟨a + m, 0, 3, 0, 4 * m + 2⟩
    · exact drain_c0 (a := a + m) (e := 4 * m + 2)
    exact drain_loop m a 2

theorem trans_even : ∀ m,
    ⟨a + m + 2, 0, 0, 2 * m + 2, 0⟩ [fm]⊢⁺ ⟨a + 6 * m + 8, 0, 0, 3 * m + 6, 0⟩ := by
  intro m
  rw [show 2 * m + 2 = 0 + (2 * m + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e (2 * m + 2) 0 (a := a + m + 2))
  rw [show 2 * (2 * m + 2) = 4 * m + 4 from by ring,
      show a + m + 2 = (a + 1) + m + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (full_drain_even m (a := a + 1))
  rw [show 3 * m + 3 = (3 * m + 2) + 1 from by omega]
  have h := phase3_e0 (a := a) (c := 3 * m + 2)
  rw [show a + 2 * (3 * m + 2) + 4 = a + 6 * m + 8 from by ring,
      show 3 * m + 2 + 4 = 3 * m + 6 from by ring] at h
  exact h

theorem trans_odd_pos : ∀ m,
    ⟨a + m + 2, 0, 0, 2 * m + 3, 0⟩ [fm]⊢⁺ ⟨a + 6 * m + 10, 0, 0, 3 * m + 6, 0⟩ := by
  intro m
  rw [show 2 * m + 3 = 0 + (2 * m + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e (2 * m + 3) 0 (a := a + m + 2))
  rw [show 2 * (2 * m + 3) = 4 * (m + 1) + 2 from by ring,
      show a + m + 2 = (a + 1) + (m + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (full_drain_odd (m + 1) (a := a + 1))
  rw [show 3 * (m + 1) = (3 * m + 2) + 1 from by omega]
  have h := phase3_e2_cpos (a := a) (c := 3 * m + 2)
  rw [show a + 2 * (3 * m + 2) + 6 = a + 6 * m + 10 from by ring,
      show 3 * m + 2 + 4 = 3 * m + 6 from by ring] at h
  exact h

theorem trans_d1 : ⟨a + 1, 0, 0, 1, 0⟩ [fm]⊢⁺ ⟨a + 4, 0, 0, 3, 0⟩ := by
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_e 1 0 (a := a + 1))
  exact phase3_e2_c0 (a := a)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 3, 0⟩) (by execute fm 3)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ d ≥ 1 ∧ 2 * a ≥ d + 1)
  · intro c ⟨A, D, hq, hd, ha⟩; subst hq
    rcases Nat.even_or_odd D with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      rcases K with _ | m
      · omega
      · obtain ⟨F, rfl⟩ : ∃ F, A = F + m + 2 := ⟨A - m - 2, by omega⟩
        refine ⟨⟨F + 6 * m + 8, 0, 0, 3 * m + 6, 0⟩,
          ⟨F + 6 * m + 8, 3 * m + 6, rfl, by omega, by omega⟩, ?_⟩
        show ⟨F + m + 2, 0, 0, 2 * (m + 1), 0⟩ [fm]⊢⁺ _
        rw [show 2 * (m + 1) = 2 * m + 2 from by ring]
        exact trans_even m
    · subst hK
      rcases K with _ | m
      · obtain ⟨F, rfl⟩ : ∃ F, A = F + 1 := ⟨A - 1, by omega⟩
        exact ⟨⟨F + 4, 0, 0, 3, 0⟩,
          ⟨F + 4, 3, rfl, by omega, by omega⟩, trans_d1⟩
      · obtain ⟨F, rfl⟩ : ∃ F, A = F + m + 2 := ⟨A - m - 2, by omega⟩
        refine ⟨⟨F + 6 * m + 10, 0, 0, 3 * m + 6, 0⟩,
          ⟨F + 6 * m + 10, 3 * m + 6, rfl, by omega, by omega⟩, ?_⟩
        show ⟨F + m + 2, 0, 0, 2 * (m + 1) + 1, 0⟩ [fm]⊢⁺ _
        rw [show 2 * (m + 1) + 1 = 2 * m + 3 from by ring]
        exact trans_odd_pos m
  · exact ⟨2, 3, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1878
