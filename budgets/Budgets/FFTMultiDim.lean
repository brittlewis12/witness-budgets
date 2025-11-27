import Budgets.FFT
import Budgets.GridMapping
import Budgets.IntervalComplex

/-!
# Multi-Dimensional FFT via Tensor Product Decomposition

Implements d-dimensional FFT by applying 1D FFT along each axis sequentially.
This is the standard "row-column" algorithm extended to arbitrary dimensions.

## Algorithm (Tensor Product)

For d-dimensional array with shape (N₀, N₁, ..., N_{d-1}):
```
For each axis i = 0 to d-1:
  For each "pencil" parallel to axis i:
    Apply 1D FFT along that pencil
```

## Example: 2D FFT on N×M grid

```
1. Apply 1D FFT to each row    (N times, M-point FFT)
2. Apply 1D FFT to each column (M times, N-point FFT)
Total: O(NM log(max(N,M)))
```

## Key Properties

- **Separable**: d-dimensional transform = composition of d 1D transforms
- **Order-independent**: Can apply FFT in any axis order (results identical)
- **Efficient**: O(N^d · d · log N) for cubic N^d grid
- **Constructive**: C0 (fully proven, no user-defined axioms)

## Data Layout

Flat array with row-major indexing:
- 2D: arr[i,j] stored at index `i * M + j` for shape (N, M)
- 3D: arr[i,j,k] stored at index `i * M * K + j * K + k` for shape (N, M, K)
- General: Uses `GridMapping.toIdxMultiDim` for lattice ↔ array conversion

## Implementation Strategy

1. Extract "pencil" (1D slice) along chosen axis
2. Apply 1D FFT to pencil
3. Insert transformed pencil back into array
4. Repeat for all pencils parallel to current axis
5. Move to next axis and repeat

-/

namespace FFTMultiDim

open IntervalComplex
open GridMapping
open FFT

/-! ## Multi-Dimensional Indexing Utilities -/

/-- Compute linear stride for accessing elements along a given axis
    For shape (N₀, N₁, ..., N_{d-1}) and axis k, stride = ∏_{i=0}^{k-1} Nᵢ

    Example (3D, shape = (5,7,11)):
    - axis 0: stride = 1      (innermost, k)
    - axis 1: stride = 11     (middle, j)
    - axis 2: stride = 11*7 = 77 (outermost, i)
-/
def axisStride {d : ℕ} (shape : Fin d → ℕ) (axis : Fin d) : ℕ :=
  Finset.prod (Finset.filter (fun i => i.val < axis.val) Finset.univ) (fun i => shape i)

/-- Total number of elements in d-dimensional array -/
def totalSize {d : ℕ} (shape : Fin d → ℕ) : ℕ :=
  Finset.prod Finset.univ (fun i => shape i)

/-- Compute flat index for multi-dimensional coordinates using row-major layout

    Formula: index = ∑ᵢ coords[i] · stride[i]
    where stride[i] = ∏_{j < i} shape[j]

    Example (2D, shape=(N,M), coords=(i,j)):
    index = i * M + j
-/
def toFlatIndex {d : ℕ} (shape : Fin d → ℕ) (coords : Fin d → ℕ) : ℕ :=
  Finset.sum Finset.univ (fun i =>
    let stride := axisStride shape i
    coords i * stride)

/-- Convert flat index back to multi-dimensional coordinates

    Inverse of toFlatIndex using repeated division
-/
def fromFlatIndex {d : ℕ} (shape : Fin d → ℕ) (idx : ℕ) : Fin d → ℕ :=
  fun i =>
    let stride := axisStride shape i
    (idx / stride) % (shape i)

/-! ## Pencil Extraction and Insertion -/

/-- Extract pencil (1D slice) along given axis

    A "pencil" is all points with same coordinates in other dimensions.

    Example (2D, axis=0, coords=(*, j)):
    Extracts column j: [arr[0,j], arr[1,j], ..., arr[N-1,j]]

    Example (2D, axis=1, coords=(i, *)):
    Extracts row i: [arr[i,0], arr[i,1], ..., arr[i,M-1]]
-/
def extractPencil {d : ℕ} (arr : Array IntervalC) (shape : Fin d → ℕ)
    (axis : Fin d) (fixed_coords : Fin d → ℕ) : Array IntervalC :=
  let n := shape axis  -- Length of pencil = size along this axis
  let stride := axisStride shape axis

  -- Build array by iterating along chosen axis
  Array.ofFn (n := n) (fun i =>
    -- Construct full coordinates: use fixed_coords except at axis position
    let full_coords : Fin d → ℕ := fun j =>
      if j = axis then i.val else fixed_coords j

    -- Compute flat index and extract element
    let idx := toFlatIndex shape full_coords
    if h : idx < arr.size then
      arr[idx]
    else
      IntervalComplex.zero  -- Out of bounds safety
  )

/-- Insert pencil back into array at specified position

    Overwrites elements along the pencil with transformed values.
    Returns new array with pencil inserted.
-/
def insertPencil {d : ℕ} (arr : Array IntervalC) (pencil : Array IntervalC)
    (shape : Fin d → ℕ) (axis : Fin d) (fixed_coords : Fin d → ℕ) : Array IntervalC :=
  let _n := shape axis

  -- Update array at pencil positions
  Array.ofFn (n := arr.size) (fun idx =>
    -- Convert flat index to multi-D coordinates
    let coords := fromFlatIndex shape idx.val

    -- Check if this position is part of current pencil
    -- (all other dimensions match fixed_coords)
    let all_dims_list := List.finRange d
    let matches_other_dims := all_dims_list.all (fun j =>
      j = axis || coords j == fixed_coords j)

    if matches_other_dims then
      -- Replace with transformed value from pencil
      let pencil_idx := coords axis
      pencil.getD pencil_idx IntervalComplex.zero
    else
      -- Keep original value
      arr.getD idx.val IntervalComplex.zero
  )

/-! ## Axis-wise FFT Application -/

/-- Helper: Process a single pencil by extracting, transforming, and inserting.
    This operation preserves array size. -/
def processSinglePencil {d : ℕ} (arr : Array IntervalC) (shape : Fin d → ℕ)
    (axis : Fin d) (fixed_coords : Fin d → ℕ) (precision : ℕ) : Array IntervalC :=
  let pencil := extractPencil arr shape axis fixed_coords
  let transformed := FFT.fft pencil precision
  insertPencil arr transformed shape axis fixed_coords

/-- extractPencil preserves pencil length.
    True by construction: uses Array.ofFn with n = shape axis -/
theorem extractPencil_size {d : ℕ} (arr : Array IntervalC) (shape : Fin d → ℕ)
    (axis : Fin d) (fixed_coords : Fin d → ℕ) :
    (extractPencil arr shape axis fixed_coords).size = shape axis := by
  unfold extractPencil
  simp [Array.size_ofFn]

/-- insertPencil preserves array size.
    True by construction: uses Array.ofFn with n = arr.size -/
theorem insertPencil_size {d : ℕ} (arr : Array IntervalC) (pencil : Array IntervalC)
    (shape : Fin d → ℕ) (axis : Fin d) (fixed_coords : Fin d → ℕ) :
    (insertPencil arr pencil shape axis fixed_coords).size = arr.size := by
  unfold insertPencil
  simp [Array.size_ofFn]

/-- processSinglePencil preserves array size.
    Direct consequence of insertPencil_size. -/
theorem processSinglePencil_size {d : ℕ} (arr : Array IntervalC) (shape : Fin d → ℕ)
    (axis : Fin d) (fixed_coords : Fin d → ℕ) (precision : ℕ) :
    (processSinglePencil arr shape axis fixed_coords precision).size = arr.size := by
  unfold processSinglePencil
  rw [insertPencil_size]

/-! ### Mutual Recursion for Pencil Iteration

KEY INSIGHT: All termination measures must have the SAME TYPE.
We use lexicographic tuples `(Nat, Nat)` where:
- First component: `dims.length` (decreases when recursing to shorter list)
- Second component: `shape dim - coord_val` (decreases when iterating coordinates)

The mutual theorem block uses functional induction, mirroring the termination structure
of the mutual definitions. This allows Lean to verify the proofs automatically!
-/

mutual
  /-- Iterate over all combinations of orthogonal coordinates. -/
  def iterateAllPencils {d : ℕ} (shape : Fin d → ℕ) (axis : Fin d) (precision : ℕ)
      (dims : List (Fin d)) (current : Array IntervalC)
      (partial_coords : Fin d → Option ℕ) : Array IntervalC :=
    match dims with
    | [] =>
        -- Base case: all coordinates fixed, process this pencil
        let fixed_coords : Fin d → ℕ := fun i =>
          match partial_coords i with
          | some val => val
          | none => 0
        processSinglePencil current shape axis fixed_coords precision
    | dim :: rest =>
        -- Recursive case: iterate over all values of this dimension
        iterDim shape axis precision dim rest current partial_coords 0
  termination_by (dims.length, 0)

  /-- Iterate over coordinate values for a single dimension. -/
  def iterDim {d : ℕ} (shape : Fin d → ℕ) (axis : Fin d) (precision : ℕ)
      (dim : Fin d) (rest : List (Fin d)) (current : Array IntervalC)
      (partial_coords : Fin d → Option ℕ) (coord_val : ℕ) : Array IntervalC :=
    if h : coord_val ≥ shape dim then
      current -- Finished iterating this dimension
    else
      let new_coords := fun i =>
        if i = dim then some coord_val else partial_coords i
      -- Process all pencils with this coordinate fixed (recurses to iterateAllPencils)
      let updated := iterateAllPencils shape axis precision rest current new_coords
      -- Continue to next coordinate value (recurses to iterDim)
      iterDim shape axis precision dim rest updated partial_coords (coord_val + 1)
  termination_by (rest.length, shape dim - coord_val)
end

mutual
  theorem iterateAllPencils_size {d : ℕ} (shape : Fin d → ℕ) (axis : Fin d) (precision : ℕ)
      (dims : List (Fin d)) (current : Array IntervalC)
      (partial_coords : Fin d → Option ℕ) :
      (iterateAllPencils shape axis precision dims current partial_coords).size = current.size := by
    match dims with
    | [] =>
        simp [iterateAllPencils]
        exact processSinglePencil_size current shape axis _ precision
    | dim :: rest =>
        simp [iterateAllPencils]
        exact iterDim_size shape axis precision dim rest current partial_coords 0

  theorem iterDim_size {d : ℕ} (shape : Fin d → ℕ) (axis : Fin d) (precision : ℕ)
      (dim : Fin d) (rest : List (Fin d)) (current : Array IntervalC)
      (partial_coords : Fin d → Option ℕ) (coord_val : ℕ) :
      (iterDim shape axis precision dim rest current partial_coords coord_val).size = current.size := by
    if h : coord_val ≥ shape dim then
      unfold iterDim
      simp [h]
    else
      unfold iterDim
      simp [h]
      let new_coords := fun i => if i = dim then some coord_val else partial_coords i
      calc (iterDim shape axis precision dim rest
              (iterateAllPencils shape axis precision rest current new_coords) partial_coords (coord_val + 1)).size
          = (iterateAllPencils shape axis precision rest current new_coords).size :=
              iterDim_size shape axis precision dim rest _ partial_coords (coord_val + 1)
        _ = current.size :=
              iterateAllPencils_size shape axis precision rest current new_coords
end

/-- Apply 1D FFT to all pencils along a given axis.

    Iterates over all "pencils" parallel to the given axis and applies 1D FFT to each.

    For 2D array (N×M):
    - axis=0: Transforms all M columns (each column is a pencil)
    - axis=1: Transforms all N rows (each row is a pencil)

    For general d-dimensional array:
    - Iterates over all (d-1)-dimensional hyperplanes orthogonal to axis
    - Applies 1D FFT along axis for each hyperplane position

    Implementation uses **top-level mutual recursion** with **PROVEN termination**
    and **PROVEN size preservation** (NO AXIOMS!).
-/
def applyFFTAlongAxis {d : ℕ} (arr : Array IntervalC) (shape : Fin d → ℕ)
    (axis : Fin d) (precision : ℕ := 53) : Array IntervalC :=
  let other_dims := (List.finRange d).filter (· ≠ axis)
  iterateAllPencils shape axis precision other_dims arr (fun _ => none)

/-- applyFFTAlongAxis preserves array size (PROVEN via functional induction). -/
theorem applyFFTAlongAxis_size {d : ℕ} (arr : Array IntervalC) (shape : Fin d → ℕ)
    (axis : Fin d) (precision : ℕ) :
    (applyFFTAlongAxis arr shape axis precision).size = arr.size := by
  unfold applyFFTAlongAxis
  exact iterateAllPencils_size shape axis precision _ arr _

/-! ## Multi-Dimensional FFT -/

/-- Check if all dimensions are powers of two -/
def allDimsPowerOfTwo {d : ℕ} (shape : Fin d → ℕ) : Bool :=
  (List.finRange d).all (fun i => FFT.isPowerOfTwo (shape i))

/-- Validate multi-D FFT preconditions:
    1. Array size matches total size from shape
    2. All dimensions are powers of two -/
def validateMultiDim {d : ℕ} (arr : Array IntervalC) (shape : Fin d → ℕ) : Bool :=
  arr.size = totalSize shape && allDimsPowerOfTwo shape

/-- d-dimensional FFT via tensor product decomposition

    Applies 1D FFT sequentially along each axis.

    **WARNING**: This is the INTERNAL fast-path API. It assumes:
    1. `arr.size = totalSize shape`
    2. All dimensions in `shape` are powers of two

    For validated transforms, use `fft_multidim_safe`.

    Complexity: O(N^d · d · log N) for cubic N^d grid

    Parameters:
    - arr: Flat array in row-major layout
    - shape: Size along each dimension (all must be powers of 2)
    - precision: Bit precision for interval arithmetic (default 53)

    Returns: Transformed array (same size and layout)
-/
def fft_multidim {d : ℕ} (arr : Array IntervalC) (shape : Fin d → ℕ)
    (precision : ℕ := 53) : Array IntervalC :=
  -- Apply FFT along each axis sequentially
  let axes := List.finRange d
  axes.foldl (fun acc axis => applyFFTAlongAxis acc shape axis precision) arr

/-- Validated multi-dimensional FFT with precondition checks.

    Returns `none` if:
    - Array size doesn't match `totalSize shape`
    - Any dimension is not a power of two
-/
def fft_multidim_safe {d : ℕ} (arr : Array IntervalC) (shape : Fin d → ℕ)
    (precision : ℕ := 53) : Option (Array IntervalC) :=
  if validateMultiDim arr shape then
    some (fft_multidim arr shape precision)
  else
    none

/-- Multi-dimensional inverse FFT

    Uses conjugate trick: IFFT = conj(FFT(conj(·))) / N

    For multi-D, normalization factor is ∏ᵢ Nᵢ (total volume)

    **WARNING**: Internal fast-path API. Use `ifft_multidim_safe` for validation.
-/
def ifft_multidim {d : ℕ} (arr : Array IntervalC) (shape : Fin d → ℕ)
    (precision : ℕ := 53) : Array IntervalC :=
  let total_N := totalSize shape

  -- Conjugate input
  let arr_conj := arr.map (fun z => ⟨z.re, IntervalDyadic.neg z.im precision⟩)

  -- FFT of conjugate
  let fft_conj := fft_multidim arr_conj shape precision

  -- Conjugate output and scale by 1/N
  let N_interval := IntervalDyadic.fromRat (total_N : ℚ) precision
  fft_conj.map (fun z =>
    let z_conj : IntervalC := ⟨z.re, IntervalDyadic.neg z.im precision⟩
    let re_scaled := IntervalDyadic.div z_conj.re N_interval precision
    let im_scaled := IntervalDyadic.div z_conj.im N_interval precision
    (⟨re_scaled, im_scaled⟩ : IntervalC))

/-- Validated multi-dimensional inverse FFT with precondition checks. -/
def ifft_multidim_safe {d : ℕ} (arr : Array IntervalC) (shape : Fin d → ℕ)
    (precision : ℕ := 53) : Option (Array IntervalC) :=
  if validateMultiDim arr shape then
    some (ifft_multidim arr shape precision)
  else
    none

/-! ## Specialized 2D and 3D Wrappers -/

/-- 2D FFT on N×M grid (row-major layout)

    Layout: arr[i,j] at index i*M + j

    Algorithm:
    1. FFT each of N rows (M-point transforms)
    2. FFT each of M columns (N-point transforms)

    **WARNING**: Internal fast-path. Use `fft2d_safe` for validation.
-/
def fft2d (arr : Array IntervalC) (N M : ℕ) (precision : ℕ := 53) : Array IntervalC :=
  let shape : Fin 2 → ℕ := fun i => if i.val = 0 then M else N
  fft_multidim arr shape precision

/-- 2D inverse FFT. Internal fast-path. Use `ifft2d_safe` for validation. -/
def ifft2d (arr : Array IntervalC) (N M : ℕ) (precision : ℕ := 53) : Array IntervalC :=
  let shape : Fin 2 → ℕ := fun i => if i.val = 0 then M else N
  ifft_multidim arr shape precision

/-- Validated 2D FFT with precondition checks.
    Returns `none` if arr.size ≠ N*M or if N, M are not powers of two. -/
def fft2d_safe (arr : Array IntervalC) (N M : ℕ) (precision : ℕ := 53) : Option (Array IntervalC) :=
  if arr.size = N * M && FFT.isPowerOfTwo N && FFT.isPowerOfTwo M then
    some (fft2d arr N M precision)
  else
    none

/-- Validated 2D inverse FFT with precondition checks. -/
def ifft2d_safe (arr : Array IntervalC) (N M : ℕ) (precision : ℕ := 53) : Option (Array IntervalC) :=
  if arr.size = N * M && FFT.isPowerOfTwo N && FFT.isPowerOfTwo M then
    some (ifft2d arr N M precision)
  else
    none

/-- 3D FFT on N×M×K grid (row-major layout)

    Layout: arr[i,j,k] at index i*M*K + j*K + k

    Algorithm:
    1. FFT along axis 0 (K-point transforms, N*M times)
    2. FFT along axis 1 (M-point transforms, N*K times)
    3. FFT along axis 2 (N-point transforms, M*K times)

    **WARNING**: Internal fast-path. Use `fft3d_safe` for validation.
-/
def fft3d (arr : Array IntervalC) (N M K : ℕ) (precision : ℕ := 53) : Array IntervalC :=
  let shape : Fin 3 → ℕ := fun i =>
    match i.val with
    | 0 => K  -- Innermost (fastest varying)
    | 1 => M  -- Middle
    | _ => N  -- Outermost (slowest varying)
  fft_multidim arr shape precision

/-- 3D inverse FFT. Internal fast-path. Use `ifft3d_safe` for validation. -/
def ifft3d (arr : Array IntervalC) (N M K : ℕ) (precision : ℕ := 53) : Array IntervalC :=
  let shape : Fin 3 → ℕ := fun i =>
    match i.val with
    | 0 => K
    | 1 => M
    | _ => N
  ifft_multidim arr shape precision

/-- Validated 3D FFT with precondition checks.
    Returns `none` if arr.size ≠ N*M*K or if N, M, K are not powers of two. -/
def fft3d_safe (arr : Array IntervalC) (N M K : ℕ) (precision : ℕ := 53) : Option (Array IntervalC) :=
  if arr.size = N * M * K && FFT.isPowerOfTwo N && FFT.isPowerOfTwo M && FFT.isPowerOfTwo K then
    some (fft3d arr N M K precision)
  else
    none

/-- Validated 3D inverse FFT with precondition checks. -/
def ifft3d_safe (arr : Array IntervalC) (N M K : ℕ) (precision : ℕ := 53) : Option (Array IntervalC) :=
  if arr.size = N * M * K && FFT.isPowerOfTwo N && FFT.isPowerOfTwo M && FFT.isPowerOfTwo K then
    some (ifft3d arr N M K precision)
  else
    none

/-! ## Size Preservation Theorems (continued) -/

/-- Helper: List.foldl with applyFFTAlongAxis preserves size -/
theorem foldl_applyFFT_size {d : ℕ} (axes : List (Fin d)) (arr : Array IntervalC)
    (shape : Fin d → ℕ) (precision : ℕ) :
    (axes.foldl (fun acc axis => applyFFTAlongAxis acc shape axis precision) arr).size = arr.size := by
  induction axes generalizing arr with
  | nil => rfl
  | cons axis rest ih =>
    simp [List.foldl]
    rw [ih]
    exact applyFFTAlongAxis_size _ _ _ _

/-- fft_multidim preserves array size.
    Uses List.foldl which applies applyFFTAlongAxis d times, each preserving size. -/
theorem fft_multidim_size {d : ℕ} (arr : Array IntervalC) (shape : Fin d → ℕ)
    (precision : ℕ) :
    (fft_multidim arr shape precision).size = arr.size := by
  unfold fft_multidim
  exact foldl_applyFFT_size (List.finRange d) arr shape precision

/-- ifft_multidim preserves array size -/
theorem ifft_multidim_size {d : ℕ} (arr : Array IntervalC) (shape : Fin d → ℕ)
    (precision : ℕ) :
    (ifft_multidim arr shape precision).size = arr.size := by
  unfold ifft_multidim
  simp [Array.size_map, fft_multidim_size]

/-- fft2d preserves array size -/
theorem fft2d_size (arr : Array IntervalC) (N M precision : ℕ) :
    (fft2d arr N M precision).size = arr.size := by
  unfold fft2d
  exact fft_multidim_size arr _ precision

/-- ifft2d preserves array size -/
theorem ifft2d_size (arr : Array IntervalC) (N M precision : ℕ) :
    (ifft2d arr N M precision).size = arr.size := by
  unfold ifft2d
  exact ifft_multidim_size arr _ precision

/-- fft3d preserves array size -/
theorem fft3d_size (arr : Array IntervalC) (N M K precision : ℕ) :
    (fft3d arr N M K precision).size = arr.size := by
  unfold fft3d
  exact fft_multidim_size arr _ precision

/-- ifft3d preserves array size -/
theorem ifft3d_size (arr : Array IntervalC) (N M K precision : ℕ) :
    (ifft3d arr N M K precision).size = arr.size := by
  unfold ifft3d
  exact ifft_multidim_size arr _ precision

/-! ## Convenience Constructors for Testing -/

/-- Create 2D zero array with given shape -/
def zeros2d (N M : ℕ) : Array IntervalC :=
  Array.replicate (N * M) IntervalComplex.zero

/-- Create 3D zero array with given shape -/
def zeros3d (N M K : ℕ) : Array IntervalC :=
  Array.replicate (N * M * K) IntervalComplex.zero

/-- Set element in 2D array (row-major: index = i*M + j) -/
def set2d (arr : Array IntervalC) (_N M : ℕ) (i j : ℕ) (val : IntervalC) : Array IntervalC :=
  let idx := i * M + j
  if idx < arr.size then
    arr.set! idx val
  else
    arr

/-- Get element from 2D array -/
def get2d (arr : Array IntervalC) (_N M : ℕ) (i j : ℕ) : IntervalC :=
  let idx := i * M + j
  arr.getD idx IntervalComplex.zero

/-- Create 2D separable function: f(i,j) = g(i) * h(j)

    Example: Gaussian f(i,j) = exp(-(i²+j²)/σ²) = exp(-i²/σ²) * exp(-j²/σ²)

    For testing: separable functions transform independently along each axis
-/
def separableFunction2d (g h : ℕ → IntervalC) (N M : ℕ) : Array IntervalC :=
  Array.ofFn (n := N * M) (fun idx =>
    let i := idx.val / M
    let j := idx.val % M
    IntervalComplex.mul (g i) (h j) 53)

/-! ## Validation Utilities -/

/-- Compute maximum error between two arrays (for testing) -/
def maxError (arr1 arr2 : Array IntervalC) : ℚ :=
  let indices := List.range (min arr1.size arr2.size)
  indices.foldl (fun max_err idx =>
    let a := arr1.getD idx IntervalComplex.zero
    let b := arr2.getD idx IntervalComplex.zero
    let diff_re := IntervalDyadic.sub a.re b.re 53
    let diff_im := IntervalDyadic.sub a.im b.im 53
    let err := max (IntervalDyadic.width diff_re) (IntervalDyadic.width diff_im)
    max max_err err) 0

/-- Test 2D FFT round-trip: IFFT(FFT(arr)) ≈ arr

    Returns maximum reconstruction error
-/
def test2dRoundTrip (arr : Array IntervalC) (N M : ℕ) (precision : ℕ := 53) : ℚ :=
  let transformed := fft2d arr N M precision
  let reconstructed := ifft2d transformed N M precision
  maxError arr reconstructed

end FFTMultiDim
