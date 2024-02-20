  $ ./demoClosure.exe <<-EOF
  > let a c d =
  > let m = c + d in
  > let xx y = 1 + y in
  > let k l = l + m + xx l in
  > k (5 + m)
  > EOF
  let a c d =
   let m =
   c + d in
   let xx y =
   1 + y in
   let k m xx l =
   l + m + xx l in
   k m xx 5 + m

  $ ./demoClosure.exe <<-EOF
  > let fac n =
  >   let rec fack n k =
  >   if n <= 1 then k 1 1
  >   else fack (n - 1) (fun m z -> k (m * n) z)
  >   in
  > fack n (fun x y -> x)
  > EOF
  let fac n =
   let fack __neinml_uni0n k =
   (if __neinml_uni0n <= 1 then k 1 1 else fack __neinml_uni0n - 1 (fun __neinml_uni0n k m z -> k m * __neinml_uni0n z) __neinml_uni0n k) in
   fack n (fun x y -> x)

  $ ./demoClosure.exe <<-EOF
  > let f x =
  >   let rec g y =
  >      if y <= 1 then x
  >      else
  >         x * y + g (y - 1)
  >   in g x
  > EOF
  let f x =
   let g x y =
   (if y <= 1 then x else x * y + g x y - 1) in
   g x x

  $ ./demoClosure.exe <<-EOF
  > let f x =
  >   let g = 4 in
  >   let g y = x + y + g in
  >   g x
  > EOF
  let f x =
   let g =
   4 in
   let __neinml_uni0g g x y =
   x + y + g in
   __neinml_uni0g g x x

  $ ./demoClosure.exe <<-EOF
  > let gg x =
  > let func1 x y z = x + y + z in
  > let func2 = func1 4 in
  > func2 5 x
  > EOF
  let gg x =
   let func1 __neinml_uni0x y z =
   __neinml_uni0x + y + z in
   let func2 func1 =
   func1 4 in
   func2 func1 5 x

  $ ./demoClosure.exe <<-EOF
  > let add x y = x + y
  > let sub x y = x - y
  > let f x cond = (if cond then add 4 else sub 4) x
  > EOF
  let add x y =
   x + y
  let sub __neinml_uni0x __neinml_uni1y =
   __neinml_uni0x - __neinml_uni1y
  let f __neinml_uni2x cond =
   (if cond then add 4 else sub 4) __neinml_uni2x
