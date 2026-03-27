import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #542: [28/15, 9/22, 65/2, 11/7, 33/13]

Vector representation:
```
 2 -1 -1  1  0  0
-1  2  0  0 -1  0
-1  0  1  0  0  1
 0  0  0 -1  1  0
 0  1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_542

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+2, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+1, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | _ => none

private theorem r4_step_eq (c d e f : ℕ) :
    fm ⟨0, 0, c, d+1, e, f⟩ = some ⟨0, 0, c, d, e+1, f⟩ := by unfold fm; simp [Q]
private theorem r2_step_eq (a b d e f : ℕ) :
    fm ⟨a+1, b, 0, d, e+1, f⟩ = some ⟨a, b+2, 0, d, e, f⟩ := by unfold fm; simp [Q]

theorem r3_chain : ∀ k, ∀ a c d f,
    ⟨a+k, 0, c, d, 0, f⟩ [fm]⊢* ⟨a, 0, c+k, d, 0, f+k⟩ := by
  intro k; induction' k with k h <;> intro a c d f
  · exists 0
  · rw [← Nat.add_assoc]; step fm; apply stepStar_trans (h _ _ _ _); ring_nf; finish

theorem r4_chain : ∀ k, ∀ c d e f,
    ⟨0, 0, c, d+k, e, f⟩ [fm]⊢* ⟨0, 0, c, d, e+k, f⟩ := by
  intro k; induction' k with k h <;> intro c d e f
  · exists 0
  · rw [show d+(k+1) = (d+k)+1 from by ring]
    exact stepStar_trans (step_stepStar (r4_step_eq c (d+k) e f))
      (by apply stepStar_trans (h c d (e+1) f); ring_nf; finish)

theorem r2_drain_all : ∀ k, ∀ a b d f,
    ⟨a+1+k, b, 0, d, k, f⟩ [fm]⊢* ⟨a+1, b+2*k, 0, d, 0, f⟩ := by
  intro k; induction' k with k h <;> intro a b d f
  · exists 0
  · rw [show a+1+(k+1) = (a+1+k)+1 from by ring]
    exact stepStar_trans (step_stepStar (r2_step_eq (a+1+k) b d k f))
      (by apply stepStar_trans (h a (b+2) d f); ring_nf; finish)

theorem r3r1_chain : ∀ k, ∀ a b d f,
    ⟨a+1, b+k, 0, d, 0, f⟩ [fm]⊢* ⟨a+1+k, b, 0, d+k, 0, f+k⟩ := by
  intro k; induction' k with k h <;> intro a b d f
  · exists 0
  · rw [show b+(k+1) = (b+k)+1 from by ring]; step fm; step fm
    apply stepStar_trans (h _ _ _ _); ring_nf; finish

theorem r2r1r1_chain : ∀ k, ∀ a c d e f,
    ⟨a+1, 0, c+2*k, d, e+1+k, f⟩ [fm]⊢* ⟨a+1+3*k, 0, c, d+2*k, e+1, f⟩ := by
  intro k; induction' k with k h <;> intro a c d e f
  · exists 0
  · rw [show c+2*(k+1) = (c+2)+2*k from by ring, show e+1+(k+1) = (e+1)+1+k from by ring]
    apply stepStar_trans (h _ (c+2) _ (e+1) _)
    rw [show a+1+3*k = (a+3*k)+1 from by ring]; step fm; step fm; step fm; ring_nf; finish

theorem opening_5 : ∀ c e g,
    ⟨0, 0, c+3, 0, e+1, g+1⟩ [fm]⊢* ⟨5, 0, c, 3, e+1, g⟩ := by
  intro c e g; step fm; step fm; step fm; step fm; step fm; finish

theorem main_trans_even (k d f : ℕ) (hdk : d ≥ k) (hda : d ≤ 4*k + 3) :
    ⟨2*k+3, 0, 0, d+1, 0, f⟩ [fm]⊢⁺ ⟨2*k+d+6, 0, 0, 2*d+5, 0, f+2*d+4⟩ := by
  rw [show (2*k+3 : ℕ) = (2*k+2)+1 from by ring]; step fm
  have h1 := r3_chain (2*k+2) 0 1 (d+1) (f+1); simp only [Nat.zero_add] at h1
  rw [show 1+(2*k+2) = 2*k+3 from by ring, show (f+1)+(2*k+2) = f+(2*k+3) from by ring] at h1
  have h2 := r4_chain (d+1) (2*k+3) 0 0 (f+(2*k+3)); simp only [Nat.zero_add] at h2
  have h3 := opening_5 (2*k) d (f+(2*k+2))
  rw [show (f+(2*k+2))+1 = f+(2*k+3) from by ring] at h3
  have h4 := r2r1r1_chain k 4 0 3 (d-k) (f+(2*k+2)); simp only [Nat.zero_add] at h4
  rw [show (d-k)+1+k = d+1 from by omega, show 4+1+3*k = 3*k+5 from by ring,
      show 3+2*k = 2*k+3 from by ring] at h4
  have h5 := r2_drain_all (d-k+1) (4*k+3-d) 0 (2*k+3) (f+(2*k+2))
  simp only [Nat.zero_add] at h5
  rw [show (4*k+3-d)+1+(d-k+1) = 3*k+5 from by omega,
      show (4*k+3-d)+1 = 4*k+4-d from by omega] at h5
  have h6 := r3r1_chain (2*(d-k+1)) (4*k+3-d) 0 (2*k+3) (f+(2*k+2))
  rw [show (4*k+3-d)+1+(2*(d-k+1)) = 2*k+d+6 from by omega,
      show (2*k+3)+(2*(d-k+1)) = 2*d+5 from by omega,
      show (f+(2*k+2))+(2*(d-k+1)) = f+2*d+4 from by omega,
      show 0+(2*(d-k+1)) = 2*(d-k+1) from by ring,
      show (4*k+3-d)+1 = 4*k+4-d from by omega] at h6
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3
    (stepStar_trans h4 (stepStar_trans h5 h6))))

theorem main_trans_odd (k d f : ℕ) (hdk : d ≥ k) (hda : d ≤ 4*k + 5) :
    ⟨2*k+4, 0, 0, d+1, 0, f⟩ [fm]⊢⁺ ⟨2*k+d+7, 0, 0, 2*d+5, 0, f+2*d+4⟩ := by
  rw [show (2*k+4 : ℕ) = (2*k+3)+1 from by ring]; step fm
  have h1 := r3_chain (2*k+3) 0 1 (d+1) (f+1); simp only [Nat.zero_add] at h1
  rw [show 1+(2*k+3) = 2*k+4 from by ring, show (f+1)+(2*k+3) = f+(2*k+4) from by ring] at h1
  have h2 := r4_chain (d+1) (2*k+4) 0 0 (f+(2*k+4)); simp only [Nat.zero_add] at h2
  have h3 := opening_5 (2*k+1) d (f+(2*k+3))
  rw [show (2*k+1)+3 = 2*k+4 from by ring, show (f+(2*k+3))+1 = f+(2*k+4) from by ring] at h3
  have h4 := r2r1r1_chain k 4 1 3 (d-k) (f+(2*k+3))
  rw [show (d-k)+1+k = d+1 from by omega, show 4+1+3*k = 3*k+5 from by ring,
      show 3+2*k = 2*k+3 from by ring, show 1+2*k = 2*k+1 from by ring] at h4
  -- R2 + R1 for c=1
  have h5 : ⟨3*k+5, 0, 1, 2*k+3, d-k+1, f+(2*k+3)⟩ [fm]⊢*
      ⟨3*k+6, 1, 0, 2*k+4, d-k, f+(2*k+3)⟩ := by
    rw [show 3*k+5 = (3*k+4)+1 from by ring,
        show d-k+1 = (d-k)+1 from by ring]
    step fm; step fm
    rw [show 3*k+4+2 = 3*k+6 from by ring, show 2*k+3+1 = 2*k+4 from by ring]; finish
  have h6 := r2_drain_all (d-k) (4*k+5-d) 1 (2*k+4) (f+(2*k+3))
  rw [show (4*k+5-d)+1+(d-k) = 3*k+6 from by omega,
      show (4*k+5-d)+1 = 4*k+6-d from by omega] at h6
  have h7 := r3r1_chain (1+2*(d-k)) (4*k+5-d) 0 (2*k+4) (f+(2*k+3))
  rw [show (4*k+5-d)+1+(1+2*(d-k)) = 2*k+d+7 from by omega,
      show (2*k+4)+(1+2*(d-k)) = 2*d+5 from by omega,
      show (f+(2*k+3))+(1+2*(d-k)) = f+2*d+4 from by omega,
      show 0+(1+2*(d-k)) = 1+2*(d-k) from by ring,
      show (4*k+5-d)+1 = 4*k+6-d from by omega] at h7
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3
    (stepStar_trans h4 (stepStar_trans h5 (stepStar_trans h6 h7)))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 3, 0, 2⟩)
  · execute fm 8
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d fv, q = ⟨a+3, 0, 0, d+1, 0, fv⟩ ∧ d ≤ 2*a+3 ∧ 2*d ≥ a)
  · intro c ⟨a, d, fv, hq, hd, hd2⟩; subst hq
    rcases Nat.even_or_odd a with ⟨k, hk⟩ | ⟨k, hk⟩
    · subst hk
      have hkk : k + k = 2 * k := by ring
      rw [hkk] at hd hd2 ⊢
      have hge : d ≥ k := by omega
      have hle : d ≤ 4*k+3 := by omega
      refine ⟨⟨2*k+d+6, 0, 0, 2*d+5, 0, fv+2*d+4⟩,
        ⟨2*k+d+3, 2*d+4, fv+2*d+4, ?_, ?_, ?_⟩,
        main_trans_even k d fv hge hle⟩
      · show (2*k+d+6, 0, 0, 2*d+5, 0, fv+2*d+4) = ((2*k+d+3)+3, 0, 0, (2*d+4)+1, 0, fv+2*d+4); congr 1
      · show 2*d+4 ≤ 2*(2*k+d+3)+3; omega
      · show 2*(2*d+4) ≥ 2*k+d+3; omega
    · subst hk
      have hge : d ≥ k := by omega
      have hle : d ≤ 4*k+5 := by omega
      refine ⟨⟨2*k+d+7, 0, 0, 2*d+5, 0, fv+2*d+4⟩,
        ⟨2*k+d+4, 2*d+4, fv+2*d+4, ?_, ?_, ?_⟩,
        by rw [show 2*k+1+3 = 2*k+4 from by ring]; exact main_trans_odd k d fv hge hle⟩
      · congr 1
      · show 2*d+4 ≤ 2*(2*k+d+4)+3; omega
      · show 2*(2*d+4) ≥ 2*k+d+4; omega
  · exact ⟨0, 2, 2, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_542
