(* Expected that inner lets should be lifted except for variable declarations *)
  $ ./demoLambda.exe <<-EOF
  > let val =
  >   let var = 42 in
  >   let f x = x in
  >   f var
  > EOF
  let f x =
   x
  let val =
   let var =
   42 in
   f var


  $ ./demoLambda.exe <<-EOF
  > let foo a b c d = a+b+c+d
  > let main = print_int (foo (let _ = print_int 1 in 1) (let _ = print_int 2 in 2) (let _ = print_int 3 in 3) (let _ = print_int 4 in 4))
  > EOF
  let foo a b c d =
   a + b + c + d
  let main =
   let __neinml_uni2_ =
   print_int 4 in
  let __neinml_uni1_ =
   print_int 3 in
  let __neinml_uni0_ =
   print_int 2 in
  let _ =
   print_int 1 in
   print_int foo 1 2 3 4

(* Result is:
let g uni0x = uni0x
let f x = let uni1x = g x in let val = uni1x in g x + val
*)
  $ ./demoLambda.exe <<-EOF
  > let f x =
  >   let g x = x in
  >   let val =
  >     let x = g x in
  >     x
  >   in
  >   g x + val
  > EOF
  let g __neinml_uni0x =
   __neinml_uni0x
  let f x =
   let __neinml_uni1x =
   g x in
  let val =
   __neinml_uni1x in
   g x + val

  $ ./demoLambda.exe <<-EOF
  > let f = (fun x ->
  >   let g x = x in
  >   (if x then g else (fun y -> y + 5)) 4
  > )
  > EOF
  let g __neinml_uni0x =
   __neinml_uni0x
  let __neinml_ll_0 y =
   y + 5
  let f x =
   (if x then g else __neinml_ll_0) 4

  $ ./demoLambda.exe <<-EOF
  > let f1 x y = x + y
  > let f2 x y = x - y
  > let main x = (if x then f1 1 else f2 1) 4
  > EOF
  let f1 x y =
   x + y
  let f2 __neinml_uni0x __neinml_uni1y =
   __neinml_uni0x - __neinml_uni1y
  let main __neinml_uni2x =
   (if __neinml_uni2x then f1 1 else f2 1) 4

  $ ./demoLambda.exe <<-EOF
  > let fac n =
  >   let rec fack n k =
  >   if n <= 1 then k 1 1
  >   else fack (n - 1) (fun m z -> k (m * n) z)
  >   in
  >   fack n (fun x y -> x)
  > EOF
  let __neinml_ll_0 __neinml_uni0n k m z =
   k m * __neinml_uni0n z
  let fack __neinml_uni0n k =
   if __neinml_uni0n <= 1 then k 1 1 else fack __neinml_uni0n - 1 __neinml_ll_0 __neinml_uni0n k
  let __neinml_ll_1 x y =
   x
  let fac n =
   fack n __neinml_ll_1

  $ ./demoLambda.exe <<-EOF
  > let const x y = x
  > let main = 
  >   let five = const 5 in
  >   print_int (five 7)
  > EOF
  let const x y =
   x
  let five =
   const 5
  let main =
   print_int five 7
