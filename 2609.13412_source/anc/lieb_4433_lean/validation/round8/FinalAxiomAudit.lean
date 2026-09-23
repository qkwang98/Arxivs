import Bridge.Young.FinalBridge

/-! Independent round-eight audit: the complete public final interface,
the actual coefficient/trace identification, and the kernel dependencies
of the certificate, contraction, normalization, and PSD coverage. -/

#check LiebBridge.Young.FinalBridge.classPairing_moment
#check LiebBridge.Young.FinalBridge.gram_witness_nonnegative
#check LiebBridge.Young.FinalBridge.psd_witness_nonnegative
#check LiebBridge.Young.FinalBridge.computed_witness_nonnegative
#check LiebBridge.Young.FinalBridge.matrix_bridge
#check LiebBridge.Young.FinalBridge.bridge_inequality
#check LiebBridge.Young.FinalBridge.normalized_bridge
#check LiebBridge.Young.FinalBridge.pdc4433_of_four_pate
#check LiebBridge.Young.TensorWitnessPositivity.concrete_witness_nonneg
#check LiebBridge.Young.WitnessTrace.trace_witness_eq_computedCoeff
#check LiebBridge.exists_gram_of_posSemidef
#check LiebBridge.Young.OrdinaryImmanants.complexImmanant_real

#print axioms LiebBridge.Young.FinalBridge.classPairing_moment
#print axioms LiebBridge.Young.FinalBridge.gram_witness_nonnegative
#print axioms LiebBridge.Young.FinalBridge.psd_witness_nonnegative
#print axioms LiebBridge.Young.FinalBridge.computed_witness_nonnegative
#print axioms LiebBridge.Young.FinalBridge.matrix_bridge
#print axioms LiebBridge.Young.FinalBridge.bridge_inequality
#print axioms LiebBridge.Young.FinalBridge.normalized_bridge
#print axioms LiebBridge.Young.FinalBridge.pdc4433_of_four_pate
#print axioms LiebBridge.Young.TensorWitnessPositivity.concrete_witness_nonneg
#print axioms LiebBridge.Young.WitnessTrace.trace_witness_eq_computedCoeff
#print axioms LiebBridge.Young.WitnessCoefficientPositivity.coefficient_pairing
#print axioms LiebBridge.Young.WitnessCoefficientPositivity.realWitnessForm_nonneg
#print axioms LiebBridge.Young.TensorPairing.character_pairing
#print axioms LiebBridge.Young.TensorPairing.moment_conjugate
#print axioms LiebBridge.Young.TensorPairing.evaluation_pairing
#print axioms LiebBridge.Certificate.aggregateComputedIdentity
#print axioms LiebBridge.Certificate.realWeightedIdentity
#print axioms LiebBridge.Certificate.bridge_of_witness_nonnegative
#print axioms LiebBridge.Certificate.computedCoeff_eq_storedCoeff_of_partition
#print axioms LiebBridge.Certificate.witnessMetadataCheck
#print axioms LiebBridge.Certificate.tableauSafetyCheck
#print axioms LiebBridge.Certificate.mem_partitions14_iff
#print axioms Bridge.Normalization.degree_balance
#print axioms Bridge.Normalization.normalized_weights_positive
#print axioms Bridge.Normalization.normalized_weights_sum
#print axioms Bridge.Normalization.bridge_iff_normalizedBridge
#print axioms Bridge.Normalization.pdc4433_of_bridge
#print axioms LiebBridge.pairSwap_expectation_eq
#print axioms LiebBridge.witness_eq_adjoint_sandwich
#print axioms LiebBridge.projectedSwapWitness_nonneg
#print axioms LiebBridge.exists_gram_of_posSemidef
#print axioms LiebBridge.Young.OrdinaryImmanants.complexImmanant_real

-- Expose the only four mathematical inputs remaining in the final theorem.
#print LiebBridge.Pate653
#print LiebBridge.Pate644
#print LiebBridge.Pate554
#print LiebBridge.Pate5333
