  $ ./demoAnf.exe <<-EOF
  > let condition x = if x % 2 = 0 then true else false
  > let test x = if condition x then x else x * 2
  > EOF
  let condition x =
   let __neinml_anf_2 =
   x % 2 in
  let __neinml_anf_1 =
   __neinml_anf_2 = 0 in
  let __neinml_anf_0 =
   if __neinml_anf_1 then 
   true
   else 
   false in
   __neinml_anf_0
  let test __neinml_uni0x =
   let __neinml_anf_1 =
   condition __neinml_uni0x in
  let __neinml_anf_0 =
   if __neinml_anf_1 then 
   __neinml_uni0x
   else let __neinml_anf_2 =
   __neinml_uni0x * 2 in
   __neinml_anf_2 in
   __neinml_anf_0


  $ ./demoAnf.exe <<-EOF
  > let rec fac n =
  > let aboba = 1 + 5 * 7 in
  > let biba = aboba + n in
  > if n = 1 then 1 else n * fac (n - 1)
  > EOF
  let rec fac n =
   let __neinml_anf_6 =
   5 * 7 in
  let __neinml_anf_5 =
   1 + __neinml_anf_6 in
  let aboba =
   __neinml_anf_5 in
  let __neinml_anf_7 =
   aboba + n in
  let biba =
   __neinml_anf_7 in
  let __neinml_anf_1 =
   n = 1 in
  let __neinml_anf_0 =
   if __neinml_anf_1 then 
   1
   else let __neinml_anf_4 =
   n - 1 in
  let __neinml_anf_3 =
   fac __neinml_anf_4 in
  let __neinml_anf_2 =
   n * __neinml_anf_3 in
   __neinml_anf_2 in
   __neinml_anf_0

  $ ./demoAnf.exe <<-EOF
  > let rec fac n =
  >   if n = 1 then 1 else n * fac (n - 1)
  > EOF
  let rec fac n =
   let __neinml_anf_1 =
   n = 1 in
  let __neinml_anf_0 =
   if __neinml_anf_1 then 
   1
   else let __neinml_anf_4 =
   n - 1 in
  let __neinml_anf_3 =
   fac __neinml_anf_4 in
  let __neinml_anf_2 =
   n * __neinml_anf_3 in
   __neinml_anf_2 in
   __neinml_anf_0

  $ ./demoAnf.exe <<-EOF
  > let main =
  > let aboba = 4 + 7 in
  > print_int aboba
  > EOF
  let main =
   let __neinml_anf_1 =
   4 + 7 in
  let aboba =
   __neinml_anf_1 in
  let __neinml_anf_0 =
   print_int aboba in
   __neinml_anf_0


  $ ./demoAnf.exe <<-EOF
  > let main =
  > print_bool (5 % 2 = 0)
  > EOF
  let main =
   let __neinml_anf_2 =
   5 % 2 in
  let __neinml_anf_1 =
   __neinml_anf_2 = 0 in
  let __neinml_anf_0 =
   print_bool __neinml_anf_1 in
   __neinml_anf_0


  $ ./demoAnf.exe <<-EOF
  > let f1 x y = x + y
  > let f2 x y = x - y
  > let main x = (if x then f1 1 else f2 1) 4
  > EOF
  let f1 x y =
   let __neinml_anf_0 =
   x + y in
   __neinml_anf_0
  let f2 __neinml_uni0x __neinml_uni1y =
   let __neinml_anf_0 =
   __neinml_uni0x - __neinml_uni1y in
   __neinml_anf_0
  let main __neinml_uni2x =
   let __neinml_anf_1 =
   if __neinml_uni2x then let __neinml_anf_2 =
   f1 1 in
   __neinml_anf_2
   else let __neinml_anf_3 =
   f2 1 in
   __neinml_anf_3 in
  let __neinml_anf_4 =
   __neinml_anf_1 in
  let __neinml_anf_0 =
   __neinml_anf_4 4 in
   __neinml_anf_0
