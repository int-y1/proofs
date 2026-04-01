import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1445: [7/15, 242/3, 9/77, 5/11, 847/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  2
 0  2  0 -1 -1
 0  0  1  0 -1
-1  0  0  1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1445

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | _ => none

theorem inner_step : ∀ k, ∀ a c d,
    ⟨a + k, 0, c + 4 * k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 4 * (k + 1) = (c + 4 * k) + 4 from by ring]
    step fm; step fm; step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 3)); ring_nf; finish

theorem r3r2r2_chain : ∀ k, ∀ a d e,
    ⟨a, 0, 0, d + k, e + 1⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e + 1 + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (a + 2) d (e + 3)); ring_nf; finish

theorem r4_chain : ∀ k, ∀ a c e,
    ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e); ring_nf; finish

theorem escape_c0 (a d : ℕ) :
    ⟨a + 1, 0, 0, d, 0⟩ [fm]⊢⁺ ⟨a + 2 * d + 2, 0, 3 * d + 5, 0, 0⟩ := by
  step fm
  rw [show d + 1 = 0 + (d + 1) from by ring, show (2 : ℕ) = 1 + 1 from rfl]
  apply stepStar_trans (r3r2r2_chain (d + 1) a 0 1)
  rw [show a + 2 * (d + 1) = a + 2 * d + 2 from by ring,
      show 1 + 1 + 3 * (d + 1) = 0 + (3 * d + 5) from by ring]
  apply stepStar_trans (r4_chain (3 * d + 5) (a + 2 * d + 2) 0 0)
  ring_nf; finish

theorem escape_c1 (a d : ℕ) :
    ⟨a + 1, 0, 1, d, 0⟩ [fm]⊢⁺ ⟨a + 2 * d + 3, 0, 3 * d + 6, 0, 0⟩ := by
  step fm; step fm; step fm; step fm
  rw [show d + 1 = 0 + (d + 1) from by ring, show (3 : ℕ) = 2 + 1 from rfl]
  apply stepStar_trans (r3r2r2_chain (d + 1) (a + 1) 0 2)
  rw [show a + 1 + 2 * (d + 1) = a + 2 * d + 3 from by ring,
      show 2 + 1 + 3 * (d + 1) = 0 + (3 * d + 6) from by ring]
  apply stepStar_trans (r4_chain (3 * d + 6) (a + 2 * d + 3) 0 0)
  ring_nf; finish

theorem escape_c2 (a d : ℕ) :
    ⟨a + 1, 0, 2, d, 0⟩ [fm]⊢⁺ ⟨a + 2 * d + 4, 0, 3 * d + 7, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  rw [show d + 1 = 0 + (d + 1) from by ring, show (4 : ℕ) = 3 + 1 from rfl]
  apply stepStar_trans (r3r2r2_chain (d + 1) (a + 2) 0 3)
  rw [show a + 2 + 2 * (d + 1) = a + 2 * d + 4 from by ring,
      show 3 + 1 + 3 * (d + 1) = 0 + (3 * d + 7) from by ring]
  apply stepStar_trans (r4_chain (3 * d + 7) (a + 2 * d + 4) 0 0)
  ring_nf; finish

theorem escape_c3 (a d : ℕ) :
    ⟨a + 1, 0, 3, d, 0⟩ [fm]⊢⁺ ⟨a + 2 * d + 5, 0, 3 * d + 8, 0, 0⟩ := by
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  rw [show d + 2 = 0 + (d + 2) from by ring, show (2 : ℕ) = 1 + 1 from rfl]
  apply stepStar_trans (r3r2r2_chain (d + 2) (a + 1) 0 1)
  rw [show a + 1 + 2 * (d + 2) = a + 2 * d + 5 from by ring,
      show 1 + 1 + 3 * (d + 2) = 0 + (3 * d + 8) from by ring]
  apply stepStar_trans (r4_chain (3 * d + 8) (a + 2 * d + 5) 0 0)
  ring_nf; finish

theorem trans_r0 (a q : ℕ) :
    ⟨a + q + 1, 0, 4 * q, 0, 0⟩ [fm]⊢⁺ ⟨a + 6 * q + 2, 0, 9 * q + 5, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show a + q + 1 = (a + 1) + q from by ring, show 4 * q = 0 + 4 * q from by ring]
    exact inner_step q (a + 1) 0 0
  · rw [show 0 + 3 * q = 3 * q from by ring]
    have h := escape_c0 a (3 * q)
    rw [show a + 2 * (3 * q) + 2 = a + 6 * q + 2 from by ring,
        show 3 * (3 * q) + 5 = 9 * q + 5 from by ring] at h
    exact h

theorem trans_r1 (a q : ℕ) :
    ⟨a + q + 1, 0, 4 * q + 1, 0, 0⟩ [fm]⊢⁺ ⟨a + 6 * q + 3, 0, 9 * q + 6, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show a + q + 1 = (a + 1) + q from by ring, show 4 * q + 1 = 1 + 4 * q from by ring]
    exact inner_step q (a + 1) 1 0
  · rw [show 0 + 3 * q = 3 * q from by ring]
    have h := escape_c1 a (3 * q)
    rw [show a + 2 * (3 * q) + 3 = a + 6 * q + 3 from by ring,
        show 3 * (3 * q) + 6 = 9 * q + 6 from by ring] at h
    exact h

theorem trans_r2 (a q : ℕ) :
    ⟨a + q + 1, 0, 4 * q + 2, 0, 0⟩ [fm]⊢⁺ ⟨a + 6 * q + 4, 0, 9 * q + 7, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show a + q + 1 = (a + 1) + q from by ring, show 4 * q + 2 = 2 + 4 * q from by ring]
    exact inner_step q (a + 1) 2 0
  · rw [show 0 + 3 * q = 3 * q from by ring]
    have h := escape_c2 a (3 * q)
    rw [show a + 2 * (3 * q) + 4 = a + 6 * q + 4 from by ring,
        show 3 * (3 * q) + 7 = 9 * q + 7 from by ring] at h
    exact h

theorem trans_r3 (a q : ℕ) :
    ⟨a + q + 1, 0, 4 * q + 3, 0, 0⟩ [fm]⊢⁺ ⟨a + 6 * q + 5, 0, 9 * q + 8, 0, 0⟩ := by
  apply stepStar_stepPlus_stepPlus
  · rw [show a + q + 1 = (a + 1) + q from by ring, show 4 * q + 3 = 3 + 4 * q from by ring]
    exact inner_step q (a + 1) 3 0
  · rw [show 0 + 3 * q = 3 * q from by ring]
    have h := escape_c3 a (3 * q)
    rw [show a + 2 * (3 * q) + 5 = a + 6 * q + 5 from by ring,
        show 3 * (3 * q) + 8 = 9 * q + 8 from by ring] at h
    exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 5, 0, 0⟩)
  · execute fm 9
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a c, q = (⟨a + 1, 0, c + 1, 0, 0⟩ : Q) ∧ a + 1 > (c + 1) / 4)
  · intro q ⟨a, c, hq, hinv⟩; subst hq
    have hCeq : c + 1 = 4 * ((c + 1) / 4) + (c + 1) % 4 := (Nat.div_add_mod (c + 1) 4).symm
    obtain ⟨qq, r, hqq, hrc, hr⟩ : ∃ qq r, qq = (c + 1) / 4 ∧ c + 1 = 4 * qq + r ∧ r < 4 := by
      exact ⟨(c + 1) / 4, (c + 1) % 4, rfl, hCeq, Nat.mod_lt _ (by omega)⟩
    have ha_ge_qq : a ≥ qq := by omega
    obtain ⟨a', ha_eq⟩ : ∃ a', a = a' + qq := ⟨a - qq, by omega⟩
    subst ha_eq
    have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · -- r = 0: c + 1 = 4 * qq
      have hqq_pos : qq ≥ 1 := by omega
      have hc : c = 4 * qq - 1 := by omega
      subst hc
      refine ⟨⟨a' + 6 * qq + 2, 0, 9 * qq + 5, 0, 0⟩,
              ⟨a' + 6 * qq + 1, 9 * qq + 4, rfl, ?_⟩, ?_⟩
      · omega
      · rw [show 4 * qq - 1 + 1 = 4 * qq from by omega]
        exact trans_r0 a' qq
    · -- r = 1: c + 1 = 4 * qq + 1
      have hc : c = 4 * qq := by omega
      subst hc
      refine ⟨⟨a' + 6 * qq + 3, 0, 9 * qq + 6, 0, 0⟩,
              ⟨a' + 6 * qq + 2, 9 * qq + 5, rfl, ?_⟩, ?_⟩
      · omega
      · exact trans_r1 a' qq
    · -- r = 2: c + 1 = 4 * qq + 2
      have hc : c = 4 * qq + 1 := by omega
      subst hc
      refine ⟨⟨a' + 6 * qq + 4, 0, 9 * qq + 7, 0, 0⟩,
              ⟨a' + 6 * qq + 3, 9 * qq + 6, rfl, ?_⟩, ?_⟩
      · omega
      · rw [show 4 * qq + 1 + 1 = 4 * qq + 2 from by ring]
        exact trans_r2 a' qq
    · -- r = 3: c + 1 = 4 * qq + 3
      have hc : c = 4 * qq + 2 := by omega
      subst hc
      refine ⟨⟨a' + 6 * qq + 5, 0, 9 * qq + 8, 0, 0⟩,
              ⟨a' + 6 * qq + 4, 9 * qq + 7, rfl, ?_⟩, ?_⟩
      · omega
      · rw [show 4 * qq + 2 + 1 = 4 * qq + 3 from by ring]
        exact trans_r3 a' qq
  · exact ⟨1, 4, rfl, by omega⟩

end Sz22_2003_unofficial_1445
