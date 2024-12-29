import Mathlib

#check PowerSeries
#check DiscreteValuationRing
#check UniqueFactorizationMonoid

/-- If a commutative ring is a discrete valuation ring,
  then the power series ring over R is a unique factorization domain. -/
def ufd_of_dvr_power_series (R : Type*) [CommRing R]
  [IsDomain R] [DiscreteValuationRing R] :
  UniqueFactorizationMonoid (PowerSeries R) := by
  
  sorry
