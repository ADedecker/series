import analysis.calculus.deriv
import data.polynomial.erase_lead
import asymptotics2
import algebra.group.pi

namespace asymptotics

open filter

open_locale topological_space

section normed_group

variables {α β : Type*} [normed_group β] 

def is_equivalent (u v : α → β) (l : filter α) := is_o (u - v) v l

notation u ` ~[`:50 l:50 `] `:0 v:50 := is_equivalent u v l

variables {u v w : α → β} {l : filter α}

lemma is_equivalent.is_o (h : u ~[l] v) : is_o (u - v) v l := h

lemma is_equivalent.is_O (h : u ~[l] v) : is_O u v l :=
(is_O.congr_of_sub h.is_O.symm).mp (is_O_refl _ _)

lemma is_equivalent.is_O_symm (h : u ~[l] v) : is_O v u l :=
begin
  convert h.is_o.right_is_O_add,
  ext,
  simp
end

@[refl] lemma is_equivalent.refl : u ~[l] u :=
begin
  rw [is_equivalent, sub_self],
  exact is_o_zero _ _
end

@[symm] lemma is_equivalent.symm (h : u ~[l] v) : v ~[l] u :=
(h.is_o.trans_is_O h.is_O_symm).symm

@[trans] lemma is_equivalent.trans (huv : u ~[l] v) (hvw : v ~[l] w) : u ~[l] w :=
begin
  rw is_equivalent,
  convert (huv.is_o.trans_is_O hvw.is_O).add hvw.is_o,
  ext,
  repeat {rw pi.sub_apply},
  abel
end

lemma is_equivalent_zero_iff_eventually_zero : u ~[l] 0 ↔ u =ᶠ[l] 0 :=
begin
  rw [is_equivalent, sub_zero],
  exact is_o_zero_right_iff
end

lemma is_equivalent_const_iff_tendsto {c : β} (h : c ≠ 0) : u ~[l] (λ _, c) ↔ tendsto u l (𝓝 c) :=
begin
  rw [is_equivalent, is_o_const_iff h],
  split; intro h;
  [ { have := h.add tendsto_const_nhds, rw zero_add at this }, 
    { have := h.add tendsto_const_nhds, rw ← sub_self c} ];
  convert this; ext; simp [sub_eq_add_neg]
end

lemma is_equivalent.tendsto {c : β} (hu : u ~[l] (λ _, c)) : filter.tendsto u l (𝓝 c) :=
begin
  rcases (em $ c = 0) with ⟨rfl, h⟩,
  { exact (tendsto_congr' $ is_equivalent_zero_iff_eventually_zero.mp hu).mpr tendsto_const_nhds },
  { exact (is_equivalent_const_iff_tendsto h).mp hu }
end

end normed_group

section normed_field

variables {α β : Type*} [normed_field β] {t u v w : α → β} {l : filter α}

lemma is_equivalent_iff_exists_mul_eq : u ~[l] v ↔ 
  ∃ (φ : α → β) (hφ : tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v :=
begin
  rw [is_equivalent, is_o_iff_exists],
  split; rintros ⟨φ, hφ, h⟩; [use (φ + 1), use (φ - 1)]; split,
  { conv in (𝓝 _) { rw ← zero_add (1 : β) },
    exact hφ.add (tendsto_const_nhds) },
  { convert h.add (eventually_eq.refl l v); ext; simp [add_mul] },
  { conv in (𝓝 _) { rw ← sub_self (1 : β) },
    exact hφ.sub (tendsto_const_nhds) },
  { convert h.sub (eventually_eq.refl l v); ext; simp [sub_mul] }
end

lemma is_equivalent.mul (htu : t ~[l] u) (hvw : v ~[l] w) : t * v ~[l] u * w :=
begin
  rw is_equivalent_iff_exists_mul_eq at *,
  rcases htu with ⟨φ₁, hφ₁, h₁⟩,
  rcases hvw with ⟨φ₂, hφ₂, h₂⟩,
  rw ← one_mul (1 : β),
  refine ⟨φ₁ * φ₂, hφ₁.mul hφ₂, _⟩,
  convert h₁.mul h₂ using 1,
  ext,
  simp only [pi.mul_apply],
  ac_refl
end

lemma is_equivalent.inv (huv : u ~[l] v) : (λ x, (u x)⁻¹) ~[l] (λ x, (v x)⁻¹) :=
begin
  rw is_equivalent_iff_exists_mul_eq at *,
  rcases huv with ⟨φ, hφ, h⟩,
  rw ← inv_one,
  refine ⟨λ x, (φ x)⁻¹, tendsto.inv' (by norm_num) hφ, _⟩,
  convert h.inv,
  ext,
  simp [mul_inv']
end

lemma is_equivalent.div (htu : t ~[l] u) (hvw : v ~[l] w) : 
  (λ x, t x / v x) ~[l] (λ x, u x / w x) :=
htu.mul hvw.inv

end normed_field

end asymptotics

section polynomial

open polynomial asymptotics filter

variables {α : Type*} [normed_ring α] [ordered_ring α]

lemma polynomial.eval_is_o_at_top_eval_of_degree_lt {P Q : polynomial α} (h : P.degree < Q.degree) :
  is_o (λ x, eval x P) (λ x, eval x Q) at_top :=
begin
  sorry
end

lemma polynomial.eval_is_equivalent_at_top_eval_lead (P : polynomial α) : 
  (λ x, eval x P) ~[at_top] (λ x, eval x ((C P.leading_coeff) * X ^ P.nat_degree)) :=
begin
  rw is_equivalent,
  have : (λ x, eval x P) - (λ x, eval x ((C P.leading_coeff) * X ^ P.nat_degree)) = 
    λ x, eval x P.erase_lead,
  { simp_rw [← self_sub_C_mul_X_pow, eval_sub], refl },
  rw this,
  sorry
end

end polynomial

#lint