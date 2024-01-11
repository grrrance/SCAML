  $ ./liftingTests.exe <<-EOF
  > let fac n =
  > let rec fack n k =
  > if n <= 1 then k else fack (n - 1) (fun m -> k (m * n))
  > in 
  > fack n (fun x -> x)
  > EOF
  let  id_1 k n m  = (k (m * n))
  let rec id_0 n k  = (if (n <= 1) then k else ((id_0 (n - 1)) ((id_1 k) n)))
  let  id_2 x  = x
  let  fac n  = ((id_0 n) id_2)
  $ ./liftingTests.exe <<-EOF
  > let a c d =
  > let m = c + d in
  > let k l = l + m in
  > k (5 + m)
  > EOF
  let  id_0 m l  = (l + m)
  let  a c d  = let m = (c + d) in ((id_0 m) (5 + m))
  $ ./liftingTests.exe <<-EOF
  > let fac n =
  > let rec fack n k =
  > if n <= 1 then k else fack (n - 1) ((fun k -> (fun n -> (fun m -> k (m * n)))) k n)
  > in
  > fack n (fun x -> x)
  > EOF
  let  id_1 k n m  = (k (m * n))
  let rec id_0 n k  = (if (n <= 1) then k else ((id_0 (n - 1)) ((id_1 k) n)))
  let  id_2 x  = x
  let  fac n  = ((id_0 n) id_2)
  $ ./liftingTests.exe <<-EOF
  > let rec factorial n = if n <= 1 then 1 else n * factorial (n - 1)
  > let main = factorial 5
  > EOF
  let rec factorial n  = (if (n <= 1) then 1 else (n * (factorial (n - 1))))
  let  main   = (factorial 5)
  $ ./liftingTests.exe <<-EOF
  > let plus a =
  > let sum b = a + b in
  > sum 5
  > EOF
  let  id_0 a b  = (a + b)
  let  plus a  = ((id_0 a) 5)
  $ ./liftingTests.exe <<-EOF
  > let s1 x =
  > let s2 = x + 5 in
  > let s3 = s2 + 5 in
  > s3
  > EOF
  let  s1 x  = let s2 = (x + 5) in let s3 = (s2 + 5) in s3
  $ ./liftingTests.exe <<-EOF
  > let fibo n =
  > let rec fibo_cps n acc =
  > if n < 3 then acc 1 else fibo_cps (n - 1) (fun x ->  fibo_cps (n - 2) (fun y -> acc (x + y)))
  > in
  > fibo_cps n (fun x -> x)
  > EOF
  let  id_2 acc x y  = (acc (x + y))
  let  id_1 acc fibo_cps n x  = ((fibo_cps (n - 2)) ((id_2 acc) x))
  let rec id_0 n acc  = (if (n < 3) then (acc 1) else ((id_0 (n - 1)) (((id_1 acc) id_0) n)))
  let  id_3 x  = x
  let  fibo n  = ((id_0 n) id_3)
  $ ./liftingTests.exe <<-EOF
  > let a,b = 1,2
  > let c = a + b
  > let test a =
  > let m,k,l = a in
  > let n = m + 2 in
  > let snd (s, t) = t in
  > let thrd (f, g, h) = h in
  > thrd (m,k,l)
  > EOF
  let  id_5   = (1, 2)
  let  a   = id_5[0]
  let  b   = id_5[1]
  let  c   = (a + b)
  let  id_0 id_1  = let t = id_1[1] in let s = id_1[0] in t
  let  id_2 id_3  = let h = id_3[2] in let g = id_3[1] in let f = id_3[0] in h
  let  test a  = let id_4 = a in let l = id_4[2] in let k = id_4[1] in let m = id_4[0] in let n = (m + 2) in (id_2 (m, k, l))

