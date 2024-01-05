  $ ./llvmTests.exe <<- EOF | lli-16 -load ../../lib/runtime/runtime.so
  > let fibo n =
  > let rec fibo_cps n acc =
  > if n < 3 then acc 1 else fibo_cps (n - 1) (fun x ->  fibo_cps (n - 2) (fun y -> acc (x + y)))
  > in
  > fibo_cps n (fun x -> x)
  > let main = fibo 11
  > EOF