  $ ./llvmTests.exe <<- EOF | tee llvmTests.ll ; echo "---" ; lli-16 -load ../../lib/runtime/runtime.so llvmTests.ll
  > let rec factorial n = if n <= 1 then 1 else n * factorial (n - 1)
  > let main = factorial 0
  > EOF