/-!
# Global Configuration Constants

Central location for configuration parameters used across the witness budget
verification framework. This ensures consistency and reproducibility.

**Design**: All configuration values are defined as `def` (not `abbrev` or `reducible`)
to prevent accidental unfolding in proofs. This makes the constants opaque in type
checking but extractable for computation.
-/

namespace WitnessBudget

/-! ## Precision Settings -/

/-- Default bit precision for interval arithmetic.

    **Value**: 53 bits (matches IEEE 754 double precision mantissa)

    **Rationale**:
    - Sufficient for PDE accuracy requirements (typical tolerance: 10⁻⁶ to 10⁻¹⁰)
    - Balances precision vs. performance (higher precision → slower computation)
    - Matches hardware floating-point precision for validation comparisons

    **Usage**: All interval operations should use this as the default precision
    parameter unless a specific precision is explicitly required by the algorithm.

    **Validation**: Parseval tests show this achieves ~10⁻¹⁵ round-trip accuracy,
    exceeding typical PDE solver requirements by 5+ orders of magnitude.
-/
def defaultPrecision : Nat := 53

/-- High-precision mode for critical computations (experimental).

    Use for:
    - Long-time PDE integration where error accumulation is critical
    - Twiddle factor generation for very large FFTs (N > 2^20)
    - Final validation of proof-critical bounds

    **Warning**: ~2-4x slower than default precision.
-/
def highPrecision : Nat := 106  -- Double the mantissa bits

/-! ## FFT Configuration -/

/-- Maximum FFT size as a power of 2.

    **Value**: 2^20 = 1,048,576 points

    **Rationale**:
    - Sufficient for 2D grids up to 1024×1024
    - Sufficient for 3D grids up to 128×128×64
    - Larger sizes require memory > 8GB for complex arrays

    This is used for:
    - Fuel parameter in recursive FFT (fuel ≥ log₂(N) required)
    - Validation of twiddle table sizes
-/
def maxFFTLogSize : Nat := 20

/-- Safety margin for FFT fuel parameter.

    The recursive FFT requires fuel ≥ log₂(N). We add this margin for safety:
    - Accounts for rounding in log₂ computation
    - Provides buffer for validation/debugging code

    **Value**: 5 (allows FFT of size up to 2^25 with default fuel)
-/
def fftFuelMargin : Nat := 5

/-! ## PDE Solver Configuration -/

/-- Default spatial resolution (number of modes per dimension).

    Used as M in grid size N = 2M+1 for spectral PDE solvers.

    **Value**: 32 modes → N = 65 points per dimension

    **Rationale**:
    - 2D: 65×65 = 4,225 points (fast iteration, good for testing)
    - 3D: 65×65×65 = 274,625 points (tractable on modern hardware)
    - Resolves features down to wavelength λ ≈ L/32 (Nyquist limit)
-/
def defaultSpatialModes : Nat := 32

/-- Aliasing padding factor for nonlinear PDE terms.

    For quadratic nonlinearities (u²): use 3N/2 padding (2/3 rule)
    For cubic nonlinearities (u³): use 2N padding (1/2 rule)

    **Value**: 2 (conservative, ensures clean dealiasing for cubic terms)

    **Usage**: `padded_size := paddingFactor * N` where N is original size
-/
def paddingFactor : Nat := 2

end WitnessBudget
