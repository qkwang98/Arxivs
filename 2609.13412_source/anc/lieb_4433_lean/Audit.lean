import Bridge

/-! Axiom inventory of every public theorem in the delivered mathematical modules. -/

-- CertificateEnumeration
#print axioms LiebBridge.Certificate.positive_length_le_sum
#print axioms LiebBridge.Certificate.entry_le_sum
#print axioms LiebBridge.Certificate.mem_partitionsAux_of_valid
#print axioms LiebBridge.Certificate.partitions14_complete
#print axioms LiebBridge.Certificate.partitions14_soundCheck
#print axioms LiebBridge.Certificate.partitions14_sound
#print axioms LiebBridge.Certificate.mem_partitions14_iff
#print axioms LiebBridge.Certificate.partitions14_nodup

-- CertificateChecks
#print axioms LiebBridge.Certificate.partitions14_length
#print axioms LiebBridge.Certificate.witness01_computed
#print axioms LiebBridge.Certificate.witness02_computed
#print axioms LiebBridge.Certificate.witness03_computed
#print axioms LiebBridge.Certificate.witness04_computed
#print axioms LiebBridge.Certificate.witness05_computed
#print axioms LiebBridge.Certificate.witness06_computed
#print axioms LiebBridge.Certificate.witness07_computed
#print axioms LiebBridge.Certificate.witness08_computed
#print axioms LiebBridge.Certificate.witness09_computed
#print axioms LiebBridge.Certificate.witness10_computed
#print axioms LiebBridge.Certificate.witness11_computed
#print axioms LiebBridge.Certificate.witness12_computed
#print axioms LiebBridge.Certificate.witness13_computed
#print axioms LiebBridge.Certificate.witness14_computed
#print axioms LiebBridge.Certificate.witness15_computed
#print axioms LiebBridge.Certificate.witness16_computed
#print axioms LiebBridge.Certificate.witness17_computed
#print axioms LiebBridge.Certificate.witness18_computed
#print axioms LiebBridge.Certificate.witness19_computed
#print axioms LiebBridge.Certificate.witness20_computed
#print axioms LiebBridge.Certificate.rowsComputedCheck
#print axioms LiebBridge.Certificate.computedCoeff_eq_storedCoeff
#print axioms LiebBridge.Certificate.weightsPositiveCheck
#print axioms LiebBridge.Certificate.weightsPositive
#print axioms LiebBridge.Certificate.degree_4433
#print axioms LiebBridge.Certificate.degree_653
#print axioms LiebBridge.Certificate.degree_644
#print axioms LiebBridge.Certificate.degree_554
#print axioms LiebBridge.Certificate.degree_5333

-- Certificate
#print axioms LiebBridge.Certificate.rationalWeightedIdentity
#print axioms LiebBridge.Certificate.aggregateStoredIdentity
#print axioms LiebBridge.Certificate.realWeightedIdentity
#print axioms LiebBridge.Certificate.bridge_of_witness_nonnegative
#print axioms LiebBridge.Certificate.computedCoeff_eq_storedCoeff_of_partition
#print axioms LiebBridge.Certificate.witnessMetadataCheck
#print axioms LiebBridge.Certificate.tableauSafetyCheck
#print axioms LiebBridge.Certificate.rowEntriesPartitionCheck
#print axioms LiebBridge.Certificate.rowEntriesDistinctCheck
#print axioms LiebBridge.Certificate.rowEntriesNonzeroCheck
#print axioms LiebBridge.Certificate.rowEntries_partition
#print axioms LiebBridge.Certificate.storedCoeff_eq_zero_of_not_partition
#print axioms LiebBridge.Certificate.aggregateComputedIdentity
#print axioms LiebBridge.Certificate.hookDegree_square_sum
#print axioms LiebBridge.Certificate.rowHookDegreeCancellationCheck

-- Contraction
#print axioms LiebBridge.pairSwap_expectation_eq
#print axioms LiebBridge.pairSwap_expectation_nonneg
#print axioms LiebBridge.kronecker_mulVec_split
#print axioms LiebBridge.dotProduct_adjoint_mulVec
#print axioms LiebBridge.filtered_pairSwap_nonneg
#print axioms LiebBridge.pairSwapMatrix_mulVec
#print axioms LiebBridge.local_swap_sandwich_nonneg
#print axioms LiebBridge.witness_eq_adjoint_sandwich
#print axioms LiebBridge.projected_local_swap_nonneg
#print axioms LiebBridge.conjTranspose_kronecker
#print axioms LiebBridge.pairSwapMatrix_mul_apply
#print axioms LiebBridge.mul_pairSwapMatrix_apply
#print axioms LiebBridge.outside_lift_commutes_swap
#print axioms LiebBridge.projectedSwapWitness_nonneg

-- TensorGram
#print axioms LiebBridge.tensorPerm_one
#print axioms LiebBridge.tensorPerm_mul
#print axioms LiebBridge.tensorInner_perm
#print axioms LiebBridge.tensorInner_perm_left
#print axioms LiebBridge.tensorInner_pureTensor
#print axioms LiebBridge.tensorPerm_pureTensor
#print axioms LiebBridge.tensorInner_perm_pureTensor
#print axioms LiebBridge.exists_gram_of_posSemidef

-- Immanant
#print axioms LiebBridge.tensorInner_smul_right
#print axioms LiebBridge.tensorInner_sum_right
#print axioms LiebBridge.characterOperator_gram_expectation
#print axioms LiebBridge.star_permutation_monomial
#print axioms LiebBridge.complexImmanant_star

-- TensorWitness
#print axioms LiebBridge.regroupTensor_inner
#print axioms LiebBridge.regroup_pureTensor
#print axioms LiebBridge.pureTensor_projectedSwap_nonneg

-- CentralAveraging
#print axioms Bridge.CentralAveraging.centralCoefficient_isClassFunction
#print axioms Bridge.CentralAveraging.pairing_centralCoefficient_classFunction
#print axioms Bridge.CentralAveraging.pairing_centralCoefficient_eq_conjugate_average
#print axioms Bridge.CentralAveraging.pairing_centralCoefficient_nonneg
#print axioms Bridge.CentralAveraging.reconstruction_of_span
#print axioms Bridge.CentralAveraging.centralCoefficient_character_expansion
#print axioms Bridge.CentralAveraging.pairing_centralCoefficient_character_expansion
#print axioms Bridge.CentralAveraging.character_weighted_pairings_nonneg

-- CharacterProjector
#print axioms Bridge.CharacterProjector.weightedOperator_trace
#print axioms Bridge.CharacterProjector.weightedOperator_mul
#print axioms Bridge.CharacterProjector.weightedOperator_idempotent
#print axioms Bridge.CharacterProjector.weightedOperator_commutes
#print axioms Bridge.CharacterProjector.weightedOperator_isHermitian
#print axioms Bridge.CharacterProjector.weightedOperator_posSemidef
#print axioms Bridge.CharacterProjector.characterProjector_eq_inverse_sum
#print axioms Bridge.CharacterProjector.characterCoefficient_star
#print axioms Bridge.CharacterProjector.characterCoefficient_convolution
#print axioms Bridge.CharacterProjector.characterProjector_isHermitian
#print axioms Bridge.CharacterProjector.characterProjector_commutes
#print axioms Bridge.CharacterProjector.characterProjector_idempotent
#print axioms Bridge.CharacterProjector.characterProjector_posSemidef

-- ProjectorConvention
#print axioms Bridge.ProjectorConvention.characterOperator_matrix_eq_characterProjector

-- Normalization
#print axioms Bridge.Normalization.degree_balance
#print axioms Bridge.Normalization.normalized_weights_positive
#print axioms Bridge.Normalization.normalized_weights_sum
#print axioms Bridge.Normalization.bridge_iff_normalizedBridge
#print axioms Bridge.Normalization.normalizedBridge_of_bridge
#print axioms Bridge.Normalization.bridge_of_normalizedBridge
#print axioms Bridge.Normalization.pdc4433_of_normalizedBridge
#print axioms Bridge.Normalization.pdc4433_of_bridge

-- PateInterfaces
#print axioms LiebBridge.normalizedBridge_of_matrixBridge
#print axioms LiebBridge.pdc4433_of_bridge_and_four_pate
