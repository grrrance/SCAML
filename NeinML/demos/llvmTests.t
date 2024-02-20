  $ ./demoLlvm.exe <<-EOF | lli-16 -load ../runtime/runtime.so
  > let main = print_int 42
  > EOF
  42

  $ ./demoLlvm.exe <<-EOF | lli-16 -load ../runtime/runtime.so
  > let main = print_int (10 * 4 + 5 - 3)
  > EOF
  42

  $ ./demoLlvm.exe <<-EOF | lli-16 -load ../runtime/runtime.so
  > let main = print_int ((5 * 4) / 3)
  > EOF
  6

  $ ./demoLlvm.exe <<-EOF | lli-16 -load ../runtime/runtime.so
  > let const x y = x
  > let main = print_int (const 5 7)
  > EOF
  5

  $ ./demoLlvm.exe <<-EOF | lli-16 -load ../runtime/runtime.so
  > let const x y = x
  > let main = 
  >   let always_five = const 5 in
  >   print_int (always_five 7)
  > EOF
  5

  $ ./demoLlvm.exe <<-EOF | lli-16 -load ../runtime/runtime.so
  > let snd x y = y
  > let main =
  > let x = 5 + 7 in
  > let y = 5 - 7 in
  > print_int (snd x y)
  > EOF
  -2

  $ ./demoLlvm.exe <<-EOF | lli-16 -load ../runtime/runtime.so
  > let cond x = if x % 2 = 0 then true else false
  > let main = print_bool (cond 4)
  > EOF
  true

  $ ./demoLlvm.exe <<-EOF | lli-16 -load ../runtime/runtime.so
  > let cond x = if x % 2 = 0 then true else false
  > let main = print_bool (cond 5)
  > EOF
  false

  $ ./demoLlvm.exe <<-EOF | lli-16 -load ../runtime/runtime.so
  > let rec fac n = if n = 1 then 1 else n * fac (n - 1)
  > let main = print_int (fac 4)
  > EOF
  24

  $ ./demoLlvm.exe <<-EOF | lli-16 -load ../runtime/runtime.so
  > let fac n =
  >   let rec helper num acc =
  >     if num = 1 then acc 
  >     else helper (num - 1) (acc * num)
  >   in
  >   helper n 1
  > let main = print_int (fac 4)
  > EOF
  24

  $ ./demoLlvm.exe <<-EOF | lli-16 -load ../runtime/runtime.so
  > let sum x y z = x + y + z
  > let main = print_int (sum 10 30 2)
  > EOF
  42

  $ ./demoLlvm.exe <<-EOF | lli-16 -load ../runtime/runtime.so
  > let modify_int f i = f i
  > let main = 
  >   let plus_one x = x + 1 in
  >   print_int (modify_int plus_one 41)
  > EOF
  42

  $ ./demoLlvm.exe <<-EOF | lli-16 -load ../runtime/runtime.so
  > let modify_int f i = f i
  > let main =
  >   print_int (modify_int (fun x -> x + 1) 41)
  > EOF
  42

  $ ./demoLlvm.exe <<-EOF | lli-16 -load ../runtime/runtime.so
  > let fack k n = if 0 >= n then 1 else n * k (n - 1)
  > let main = print_int (fack (fun x -> x - 18) 21)
  > EOF
  42

(* more fixpoints to the fixpoints God *)
  $ ./demoLlvm.exe <<-EOF | lli-16 -load ../runtime/runtime.so
  > let rec fix f x = f (fix f) x
  > let fack k n = if 0 >= n then 1 else n * k (n - 1)
  > let fac = fix fack
  > let main = print_int (fac 5)
  > EOF
  120

  $ ./demoLlvm.exe <<-EOF | lli-16 -load ../runtime/runtime.so
  > let rec fack n k = if n <= 0 then k 1 else fack (n-1) (fun m -> k (m * n))
  > let main = print_int (fack 5 (fun x -> x))
  > EOF
  120

  $ ./demoLlvm.exe <<-EOF | lli-16 -load ../runtime/runtime.so
  > let id x = x
  > let main = print_int (id 44 - id 2)
  > EOF
  42

  $ ./demoLlvm.exe <<-EOF | lli-16 -load ../runtime/runtime.so
  > let id x = x
  > let main = 
  >   let new_id = id id in
  >   print_int (new_id 42)
  > EOF
  42

  $ ./demoLlvm.exe <<-EOF | lli-16 -load ../runtime/runtime.so
  > let id x = x
  > let main = print_int (id id 42)
  > EOF
  42

  $ ./demoLlvm.exe <<-EOF | lli-16 -load ../runtime/runtime.so
  > let fst x y = x
  > let id x = x
  > let succ x = x + 1
  > let main = print_int ((fst succ id) 5)
  > EOF
  6

  $ ./demoLlvm.exe <<-EOF | lli-16 -load ../runtime/runtime.so
  > let add x y = x + y
  > let sub x y = x - y
  > let f x cond = (if cond then add 4 else sub 4) x
  > let main = print_int (f 5 (6 % 2 = 0))
  > EOF
  9

  $ ./demoLlvm.exe <<-EOF | lli-16 -load ../runtime/runtime.so
  > let main = print_int (5 / 0)
  > EOF
  Oh no! Your program is trying to divide by 0. So sorry!
  [1]
