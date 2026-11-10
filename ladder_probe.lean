import SubsetSumL25

/-! Ladder axiom probe — MEASURED rung status for the five-row upgrade map.

Every declaration below is the *statement-of-record* for one rung of the
O1–O8 / B1–B5 / V1 ladder that the subset-sum conditional rows consume
(BRIDGE.md). One `#print axioms` line each: a rung is "proved, unconditional"
only if its banner is exactly [propext, Classical.choice, Quot.sound].

Run: lake env lean ladder_probe.lean
-/

-- O1 — OpenAI L2.1 Isolation (the lemma this lane ports/receipts)
#print axioms SubsetSumL25.L2_1_isolation
#print axioms SubsetSumL25.L2_1_isolation_prob

-- O2 — OpenAI L2.2 deficiency + L2.3 random restrictions
#print axioms SubsetSumL25.L2_2_deficiency_empty
#print axioms SubsetSumL25.L2_2_deficiency_nonneg
#print axioms SubsetSumL25.L2_2_deficiency_insert
#print axioms SubsetSumL25.L2_2_deficiency_superadd
#print axioms SubsetSumL25.L2_2_deficiency_exchange
#print axioms SubsetSumL25.L2_3_halfVariance
#print axioms SubsetSumL25.L2_3_expectation_mono

-- O3 — OpenAI L2.5 prime collisions, including the UNCONDITIONAL form
#print axioms SubsetSumL25.L2_5_prime_collision
#print axioms SubsetSumL25.L2_5_prime_collision_two
#print axioms SubsetSumL25.erdos_dyadic_primes
#print axioms SubsetSumL25.L2_5_prime_collision_unconditional

-- O6 — OpenAI L5.2 sparse distinctions
#print axioms SubsetSumL25.L5_2_sparse_distinctions

-- B1 — Base L3.1/L3.2/L3.3
#print axioms SubsetSumL25.L3_1_covering
#print axioms SubsetSumL25.L3_2_sampling
#print axioms SubsetSumL25.L3_3_good_layer

-- B2 — Base Corollary D (averaged small layer)
#print axioms SubsetSumL25.Base_cor_D

-- B3 — Base Lemma A5 + Corollary A6
#print axioms SubsetSumL25.lem_A5_product
#print axioms SubsetSumL25.lem_A5_threshold
#print axioms SubsetSumL25.cor_A6_per_alias

-- O8 — OpenAI §6 word-RAM accounting
#print axioms SubsetSumL25.o8_time_bound
#print axioms SubsetSumL25.o8_draws_le
#print axioms SubsetSumL25.o8_trial_count_bound

-- O4 — OpenAI L3.2 finite filtering data
#print axioms SubsetSumL25.o4_avg_err_le
#print axioms SubsetSumL25.o4_gibbs

-- O5 + O7 — OpenAI Thm 4.1 / Thm 5.1
#print axioms SubsetSumL25.o5_time_bound
#print axioms SubsetSumL25.o7_union_le

-- B4 — Base Theorem B region analysis
#print axioms SubsetSumL25.region_existence
#print axioms SubsetSumL25.row_errors_le_six_eps

-- B5 — Base preliminary search (Prop P) + A7 envelope
#print axioms SubsetSumL25.prop_p_chebyshev
#print axioms SubsetSumL25.a7_envelope

-- V1 — jv1000 sine extension
#print axioms SubsetSumL25.v1_pos
#print axioms SubsetSumL25.v1_lipschitz
