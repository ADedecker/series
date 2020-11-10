import analysis.asymptotics
import analysis.normed_space.basic
import algebra.ring.basic

@[protect_proj] class normed_linear_ordered_group (α : Type*)
extends linear_ordered_add_comm_group α, has_norm α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))

@[protected] instance normed_linear_ordered_group.to_normed_group (α : Type*)
  [normed_linear_ordered_group α] : normed_group α :=
⟨normed_linear_ordered_group.dist_eq⟩

namespace normed_linear_ordered_group

variables {α : Type*} [normed_linear_ordered_group α]

end normed_linear_ordered_group