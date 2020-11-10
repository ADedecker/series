import analysis.calculus.deriv
import data.polynomial.erase_lead
import asymptotics2
import normed_linear_ordered_field
import normed_linear_ordered_group
import topology.algebra.ordered
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

lemma is_equivalent.tendsto_const {c : β} (hu : u ~[l] (λ _, c)) : filter.tendsto u l (𝓝 c) :=
begin
  rcases (em $ c = 0) with ⟨rfl, h⟩,
  { exact (tendsto_congr' $ is_equivalent_zero_iff_eventually_zero.mp hu).mpr tendsto_const_nhds },
  { exact (is_equivalent_const_iff_tendsto h).mp hu }
end

end normed_group

section normed_linear_ordered_group

variables {α β : Type*} [normed_linear_ordered_group β] {u v : α → β} {l : filter α}

end normed_linear_ordered_group 

section normed_field

variables {α β : Type*} [normed_field β] {t u v w : α → β} {l : filter α}

lemma is_equivalent_iff_exists_mul_eq : u ~[l] v ↔ 
  ∃ (φ : α → β) (hφ : tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v :=
begin
  rw [is_equivalent, is_o_iff_exists_eq_mul],
  split; rintros ⟨φ, hφ, h⟩; [use (φ + 1), use (φ - 1)]; split,
  { conv in (𝓝 _) { rw ← zero_add (1 : β) },
    exact hφ.add (tendsto_const_nhds) },
  { convert h.add (eventually_eq.refl l v); ext; simp [add_mul] },
  { conv in (𝓝 _) { rw ← sub_self (1 : β) },
    exact hφ.sub (tendsto_const_nhds) },
  { convert h.sub (eventually_eq.refl l v); ext; simp [sub_mul] }
end

lemma is_equivalent.exists_mul_eq (huv : u ~[l] v) : 
  ∃ (φ : α → β) (hφ : tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v :=
is_equivalent_iff_exists_mul_eq.mp huv

lemma is_equivalent.tendsto_nhds {c : β} (huv : u ~[l] v) (hv : tendsto u l (𝓝 c)) : 
  tendsto v l (𝓝 c) :=
begin
  rw ← one_mul c,
  rcases huv.symm.exists_mul_eq with ⟨φ, hφ, h⟩,
  exact (tendsto_congr' h.symm).mp (hφ.mul hv)
end

lemma is_equivalent.tendsto_nhds_iff {c : β} (huv : u ~[l] v) : 
  tendsto u l (𝓝 c) ↔ tendsto v l (𝓝 c) := ⟨huv.tendsto_nhds, huv.symm.tendsto_nhds⟩

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
  refine ⟨λ x, (φ x)⁻¹, tendsto.inv' hφ (by norm_num) , _⟩,
  convert h.inv,
  ext,
  simp [mul_inv']
end

lemma is_equivalent.div (htu : t ~[l] u) (hvw : v ~[l] w) : 
  (λ x, t x / v x) ~[l] (λ x, u x / w x) :=
htu.mul hvw.inv

end normed_field

section normed_linear_ordered_field

variables {α β : Type*} [normed_linear_ordered_field β] {u v : α → β} {l : filter α}

lemma is_equivalent.tendsto_at_top [order_topology β] (huv : u ~[l] v) (hu : tendsto u l at_top) :
  tendsto v l at_top :=
let ⟨φ, hφ, h⟩ := huv.symm.exists_mul_eq in
tendsto.congr' h.symm ((mul_comm u φ) ▸ (tendsto_mul_at_top zero_lt_one hu hφ))

lemma is_equivalent.tendsto_at_top_iff [order_topology β] (huv : u ~[l] v) :
  tendsto u l at_top ↔ tendsto v l at_top := ⟨huv.tendsto_at_top, huv.symm.tendsto_at_top⟩

end normed_linear_ordered_field

end asymptotics

section polynomial

open polynomial asymptotics filter finset
open_locale big_operators topological_space

variables {α : Type*}

lemma polynomial.eval_eq_range_sum [semiring α] {P : polynomial α} (x : α) : 
  eval x P = ∑ i in range (P.nat_degree + 1), P.coeff i * x ^ i :=
begin
  rw eval_eq_sum,
  refine P.sum_of_support_subset _ _ _,
  { intros a,
    rw [mem_range, nat.lt_add_one_iff],
    exact le_nat_degree_of_mem_supp a },
  { intros,
    exact zero_mul _ }
end

variables [ordered_ring α]

set_option profiler true
lemma polynomial.eval_is_equivalent_at_top_eval_lead
  [normed_linear_ordered_field α] [order_topology α] (P : polynomial α) : 
  (λ x, eval x P) ~[at_top] (λ x, eval x ((C P.leading_coeff) * X ^ P.nat_degree)) :=
begin
  rw is_equivalent,
  have : (λ x, eval x P) - (λ x, eval x ((C P.leading_coeff) * X ^ P.nat_degree)) = 
    λ x, eval x P.erase_lead,
  { simp_rw [← self_sub_C_mul_X_pow, eval_sub], refl },
  rw [this, C_mul_X_pow_eq_monomial, is_o_iff_tendsto'], 
  { conv 
    { congr, 
      funext, 
      rw [eval_monomial, polynomial.eval_eq_range_sum, sum_div,
          sum_congr rfl (λ n hn, (div_mul_div (P.erase_lead.coeff n) 
            (P.leading_coeff) (x^n) (x^P.nat_degree)).symm)],
      skip, 
      skip,
      congr,
      rw ← sum_eq_zero (λ n (hn : n ∈ range (P.erase_lead.nat_degree + 1)), rfl) },
    refine tendsto_finset_sum _ (λ c hc, _),
    rcases P.erase_lead_nat_degree_lt_or_erase_lead_eq_zero with h | h,
    { rw ← mul_zero (P.erase_lead.coeff c / P.leading_coeff),
      refine tendsto_const_nhds.mul _,
      rw [mem_range, nat.lt_add_one_iff] at hc,
      have : c < P.nat_degree := by linarith, 
      suffices h : tendsto (λ (x : α), x ^ ((c : ℤ) - P.nat_degree)) at_top (𝓝 0),
      { refine (tendsto_congr' ((eventually_gt_at_top (0 : α)).mono (λ x hx, _))).mp h,
        simp [fpow_sub hx.ne.symm] },
      rw [← neg_sub, ← int.coe_nat_sub this.le],
      have : 1 ≤ P.nat_degree - c := nat.sub_pos_of_lt this,
      exact @tendsto_pow_neg_at_top α _ _ (by apply_instance) _ this, },
    { simp [h, tendsto_const_nhds] } },
  { sorry },
end

#check int.coe_nat_sub

lemma polynomial.eval_is_equivalent_at_top_eval_lead [normed_field α] (P : polynomial α) : 
  (λ x, eval x P) ~[at_top] (λ x, eval x ((C P.leading_coeff) * X ^ P.nat_degree)) :=
begin
  rw is_equivalent,
  have : (λ x, eval x P) - (λ x, eval x ((C P.leading_coeff) * X ^ P.nat_degree)) = 
    λ x, eval x P.erase_lead,
  { simp_rw [← self_sub_C_mul_X_pow, eval_sub], refl },
  rw [this, is_o_iff_exists_eq_mul, C_mul_X_pow_eq_monomial],
  use (λ x, (eval x P.erase_lead) / (P.leading_coeff * x ^ P.nat_degree)),
  split,
  { conv 
    { congr, 
      funext, 
      rw [polynomial.eval_eq_range_sum, sum_div,
          sum_congr rfl (λ n hn, (div_mul_div (P.erase_lead.coeff n) 
            (P.leading_coeff) (x^n) (x^P.nat_degree)).symm)],
      skip, 
      skip,
      congr,
      rw ← sum_eq_zero (λ n (hn : n ∈ range (P.erase_lead.nat_degree + 1)), rfl) },
    refine tendsto_finset_sum _ (λ c hc, _),
    rw ← mul_zero (P.erase_lead.coeff c / P.leading_coeff),
    refine tendsto_const_nhds.mul _,
    rw mem_range at hc,
    rw nat.lt_add_one_iff at hc,
    have := P.erase_lead_nat_degree_lt_or_erase_lead_eq_zero,
    rcases this with h | h,
    { have : c + 1 ≤ P.nat_degree := by linarith, 
      simp [div_eq_mul_inv, ← pow_sub'], sorry },
    { simp only [h, le_zero_iff_eq, nat_degree_zero] at hc,
      simp only [hc, one_div, pow_zero],
      refine tendsto_inv_at_top_zero.comp tendsto_pow_at_t, } },
  { simp,
    symmetry,
     },
end

lemma polynomial.eval_is_o_at_top_eval_of_degree_lt [normed_ring α] {P Q : polynomial α} (h : P.degree < Q.degree) :
  is_o (λ x, eval x P) (λ x, eval x Q) at_top :=
begin
  sorry
end

lemma polynomial.eval_is_equivalent_at_top_eval_lead [normed_ring α] (P : polynomial α) : 
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