import analysis.calculus.deriv
import algebra.group.pi

namespace asymptotics

open filter

open_locale topological_space

section normed_field

variables {α β : Type*} [normed_field β] {u v w : α → β} {l : filter α} {c : ℝ}

lemma is_O_with.eventually_mul_div_cancel (h : is_O_with c u v l) (hnneg : 0 ≤ c) :
  ∀ᶠ x in l, (u x / v x) * v x = u x :=
begin
  rw is_O_with at h,
  rw eventually_iff_exists_mem at *,
  rcases h with ⟨s, hsl, hs⟩,
  use [s, hsl],
  intros y hy,
  specialize hs y hy,
  by_cases hvy : v y = 0,
  { rw hvy at *,
    rw [norm_zero, mul_zero] at hs,
    have hs' := le_antisymm hs (norm_nonneg _),
    rw norm_eq_zero at hs',
    rw hs',
    norm_num },
  { rw div_mul_cancel _ hvy }
end

lemma is_O.eventually_mul_div_cancel (h : is_O u v l) : ∀ᶠ x in l, (u x / v x) * v x = u x :=
let ⟨c, hcnn, hc⟩ := h.exists_nonneg in hc.eventually_mul_div_cancel hcnn

lemma is_o.eventually_mul_div_cancel (h : is_o u v l) : ∀ᶠ x in l, (u x / v x) * v x = u x :=
((is_o_iff_forall_is_O_with.mp h) zero_lt_one).eventually_mul_div_cancel zero_le_one

lemma is_O_with_of_eq_mul (φ : α → β) (hφ : ∀ᶠ x in l, ∥φ x∥ ≤ c) (h : u =ᶠ[l] φ * v) :
  is_O_with c u v l :=
begin
  rw is_O_with,
  apply h.symm.rw (λ x a, ∥a∥ ≤ c * ∥v x∥) (hφ.mp (eventually_of_forall $ λ x hx, _)),
  simp only [normed_field.norm_mul, pi.mul_apply],
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
end

lemma is_O_with_iff_exists (hc : 0 ≤ c) : 
  is_O_with c u v l ↔ ∃ (φ : α → β) (hφ : ∀ᶠ x in l, ∥φ x∥ ≤ c), u =ᶠ[l] φ * v :=
begin
  split,
  { intro h,
    use (λ x, u x / v x),
    split,
    { rw is_O_with at h,
      rw eventually_iff_exists_mem at *,
      rcases h with ⟨s, hsl, hs⟩,
      use [s, hsl],
      intros y hy,
      have := div_le_iff_of_nonneg_of_le (norm_nonneg _) hc (hs y hy),
      simpa },
    { exact eventually_eq.symm (h.eventually_mul_div_cancel hc) } },
  { rintros ⟨φ, hφ, h⟩,
    exact is_O_with_of_eq_mul φ hφ h }
end

lemma is_O_iff_exists :
  is_O u v l ↔ ∃ (φ : α → β) (hφ : ∃ c, ∀ᶠ x in l, ∥φ x∥ ≤ c), u =ᶠ[l] φ * v :=
begin
  split,
  { rintros h,
    rcases h.exists_nonneg with ⟨c, hnnc, hc⟩,
    rcases (is_O_with_iff_exists hnnc).mp hc with ⟨φ, hφ, huvφ⟩,
    exact ⟨φ, ⟨c, hφ⟩, huvφ⟩ },
  { exact λ ⟨φ, ⟨c, hφ⟩, huvφ⟩, is_O_iff_is_O_with.mpr ⟨c, is_O_with_of_eq_mul φ hφ huvφ⟩ }
end

lemma is_o_iff_exists :
  is_o u v l ↔ ∃ (φ : α → β) (hφ : tendsto φ l (𝓝 0)), u =ᶠ[l] φ * v :=
begin
  split,
  { exact λ h, ⟨λ x, u x / v x, h.tendsto_0, eventually_eq.symm h.eventually_mul_div_cancel⟩ },
  { rw is_o,
    rintros ⟨φ, hφ, huvφ⟩ c hpos,
    simp_rw [metric.tendsto_nhds, dist_zero_right] at hφ,
    exact is_O_with_of_eq_mul _ ((hφ c hpos).mp (eventually_of_forall $ λ x, le_of_lt)) huvφ }
end

end normed_field

end asymptotics