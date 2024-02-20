  $ cat <<-EOF > fib.ml
  > let rec fix f x = f (fix f) x
  > let fib self n a b = if n = 1 then b else self (n-1) b (a+b)
  > let fib x = fix fib x
  > let main = print_int (fib 5 0 1)
  > EOF
  $ ocaml fib.ml
  5
  $ cat fib.ml | ./demoLlvm.exe | lli-16 -load ../runtime/runtime.so
  5

  $ cat <<-EOF > fib.ml
  > let foo a b c = a+b+c
  > let main = print_int (foo (let _ = print_int 1 in 1) (let _ = print_int 2 in 1) (let _ = print_int 3 in 1))
  > EOF
  $ ocaml fib.ml
  3213
  $ cat fib.ml | ./demoLlvm.exe | lli-16 -load ../runtime/runtime.so
  3213
