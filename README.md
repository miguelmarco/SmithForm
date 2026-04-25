# Verified computation of Smith form for matrices over Euclidean Domains

This project contains a computable implementation in Lean of Smith Form for matrices over euclidean domains.

For efficiency reasons, it uses an implementation of matrices where the internal representation is an array (unlike Mathlib, which implements matrices as functions).

In the current state, the main function exposed is 

``` lean4
SmithForm {m n : ℕ} {R : Type} [ED : EuclideanDomain R] [DecidableEq R] (A : Mat n m R) : LUM A
```

which takes a matrix `A` with `n` rows and `m` columns with entries in an euclidean domain, and returns a structure
`LUM A`, that contains five matrices `IR, IL, L, M, R` and props stating relations between them and `A`:

``` lean4
theorem SmithForm_eq (A : Mat n m R) : (SmithForm A).L * (SmithForm A).M * (SmithForm A).R = A :=
  (SmithForm A).h

theorem SmithForm_IL (A : Mat n m R) : (SmithForm A).L * (SmithForm A).IL = frommatrix 1 :=
  (SmithForm A).hIL

theorem SmithForm_IR (A : Mat n m R) : (SmithForm A).IR * (SmithForm A).R = frommatrix 1 :=
  (SmithForm A).hIR
```

Moreover, there are also the following theorems proving that the resulting `M` is indeed the Smith form of `A`:

```
theorem SmithFormDiagonal (A : Mat n m R) : is_diagonal _ (SmithForm A) 

theorem SmithFormdvd (A : Mat n m R) (i j : ℕ) (hi : i < j) (hjn : j < n) (hjm : j < m) :
    Aget (SmithForm A).M ⟨i,by omega⟩ ⟨i,by omega⟩ ∣ Aget (SmithForm A).M ⟨j, hjn⟩ ⟨j, hjm⟩ 
``` 

# Executable implementation

The implementation is actually computable, to the extent that you can produce an executable that runs it.
It is not fast compared to the state of the art (the underlying algorithm is the basic succesive row/column elimination).

## Ring of integers

Running `lake build SmithFormZ` will produce an executable called `SmithFormZ` in the `.lake/build/bin` directory.
This executable gets `n`, `m` and the coefficients of the matrix from `stdin`, and outputs the resulting matrices `IL, L, M, R, IR` where `M` is the Smith Form, `L * M * R` is the original matrix, and `IL` and `IR` are the inverses of `L` and `R`.

For example 

```
echo "2 2 4 7 2 3" | .lake/build/bin/SmithFormZ 
```

will output

```
0 1 
-1 3 

3 -1 
1 0 

1 0 
0 -2 

2 3 
-1 -1 

-1 -3 
1 2 
```

## Ring of polynomials with rational coefficients

Running `lake build SmithFormQ` will produce an executable called `SmithFormQ` in the `.lake/build/bin` directory.

This executable reads from stdin the following structure, separated by newlines

- `n` the number of rows
- `m` the number of columns
- One entry of the matrix in each line. The polynomial is written as several rationals separated by white spaces. They correspond to the coefficients of the polynomial in increasing degree. (That is, `3/2 7` will correspond to `3/2 + 7*x`.)

The binary will output the corresponding matrices as before.

For example, the input

```
2
2
3/2 - 1
4 1
0
0 1
```
 
that corresponds to the `2 x 2` matrix 

```
[3/2-x  4+x]
[0      x]
```
will output the result

```
2/35 0 
0+-8/35*X^1+2/35*X^2 1 

35/2 0 
0+4*X^1+-1*X^2 1 

1 0 
0 0+3/35*X^1+0*X^2+2/35*X^3 

3/35+0*X^1+2/35*X^2 8/35+2/35*X^1 
-4+1*X^1 1 

1 -8/35+-2/35*X^1 
4+-1*X^1 3/35+0*X^1+2/35*X^2 
```

