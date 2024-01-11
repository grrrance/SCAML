  $ ./inferencerTests.exe <<-EOF
  > let rec factorial n = if n <= 1  then 1 else factorial (n - 1) * n
  > let x5 = factorial 5 
  > EOF
  factorial : int -> int
  x5 : int
  $ ./inferencerTests.exe <<-EOF
  > let rec fibonacci n = if n <= 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)
  > let x5 = fibonacci 5 
  > EOF
  fibonacci : int -> int
  x5 : int
  $ ./inferencerTests.exe <<-EOF
  > let fack1 k n m = k (n * m)
  > let rec fack n k = if n <= 1 then k 1 else fack (n-1) (fack1 k n)
  > let id x = x
  > let fac n = fack n id
  > EOF
  fack1 : (int -> 'd) -> int -> int -> 'd
  fack : int -> (int -> 'm) -> 'm
  id : 'n -> 'n
  fac : int -> int
  $ ./inferencerTests.exe <<-EOF
  > let id x = x
  > let acc1 acc x y = acc (x + y)
  > let acc2 fib_func n acc x = fib_func (n - 2) (acc1 acc x)
  > let rec fibo_cps n acc = if n < 3 then acc 1 else fibo_cps (n - 1) (acc2 fibo_cps n acc)
  > let fibo n = fibo_cps n id
  > EOF
  id : 'a -> 'a
  acc1 : (int -> 'e) -> int -> int -> 'e
  acc2 : (int -> (int -> 'k) -> 'n) -> int -> (int -> 'k) -> int -> 'n
  fibo_cps : int -> (int -> 'y) -> 'y
  fibo : int -> int
  $ ./inferencerTests.exe <<-EOF
  > let a,b = (1,2)
  > let c = a + b
  > let k = (true,false)
  > let l = (1,2,3)
  > let b,n,m = l
  > let snd (x,y) = y
  > let (x, (a,b)) = (1, (false,3))
  > EOF
  (a, b) : (int * int)
  c : int
  k : (bool * bool)
  l : (int * int * int)
  (b, n, m) : (int * int * int)
  snd : ('f * 'g) -> 'g
  (x, (a, b)) : (int * (bool * int))
  $ ./inferencerTests.exe <<-EOF
  > let a, _ = (1, 2)
  > EOF
  (a, _) : (int * int)
  $ ./inferencerTests.exe <<-EOF
  > let (a ,b ,c) = (1,2)
  > EOF
  unification failed on (int * int) and ('a * 'b * 'c)
  $ ./inferencerTests.exe <<-EOF
  > let (a, (b, c)) = (1,2, 3)
  > EOF
  unification failed on (int * int * int) and ('a * ('b * 'c))
  $ ./inferencerTests.exe <<-EOF
  > let k = 
  > let (x, y) = (5,5) in x
  > EOF
  k : int
