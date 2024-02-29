  $ ./Asm_test.exe <<- EOF > Asm_test.s
  > let main = print_int ( (5 + 4) - 2 )
  > EOF
  $ nasm -f elf64 -o Asm_test.o Asm_test.s
  $ gcc -o asm.out Asm_test.o ../../lib/runtime/runtime.o 2> /dev/null 2> /dev/null
  $ ./asm.out
  7
  $ ./Asm_test.exe <<- EOF > Asm_test.s
  > let fibo n =
  > let rec fibo_cps n acc =
  > if n < 3 then acc 1 else fibo_cps (n - 1) (fun x ->  fibo_cps (n - 2) (fun y -> acc (x + y)))
  > in
  > fibo_cps n (fun x -> x)
  > let main = print_int (fibo 11)
  > EOF
  $ nasm -f elf64 -o Asm_test.o Asm_test.s
  $ gcc -o asm.out Asm_test.o ../../lib/runtime/runtime.o 2> /dev/null
  $ ./asm.out
  89
  $ ./Asm_test.exe <<- EOF > Asm_test.s
  > let fac n =
  > let rec fack n k =
  > if n <= 1 then k 1 else fack (n - 1) (fun m -> k (m * n))
  > in 
  > fack n (fun x -> x)
  > let main = print_int (fac 6)
  > EOF
  $ nasm -f elf64 -o Asm_test.o Asm_test.s
  $ gcc -o asm.out Asm_test.o ../../lib/runtime/runtime.o 2> /dev/null
  $ ./asm.out
  720
  $ ./Asm_test.exe <<- EOF > Asm_test.s
  > let x = (5 + (4 - 3)) - 2
  > let main = print_int x
  > EOF
  $ nasm -f elf64 -o Asm_test.o Asm_test.s
  $ gcc -o asm.out Asm_test.o ../../lib/runtime/runtime.o 2> /dev/null
  $ ./asm.out
  4
  $ ./Asm_test.exe <<- EOF > Asm_test.s
  > let s1 x =
  > let s2 = x + 5 in
  > let s3 = s2 + 5 in
  > s3
  > let main = print_int (s1 10)
  > EOF
  $ nasm -f elf64 -o Asm_test.o Asm_test.s
  $ gcc -o asm.out Asm_test.o ../../lib/runtime/runtime.o 2> /dev/null
  $ ./asm.out
  20
  $ ./Asm_test.exe <<- EOF > Asm_test.s
  > let rec factorial n = if n <= 1 then 1 else n * factorial (n - 1)
  > let main = print_int (factorial 5)
  > EOF
  $ nasm -f elf64 -o Asm_test.o Asm_test.s
  $ gcc -o asm.out Asm_test.o ../../lib/runtime/runtime.o 2> /dev/null
  $ ./asm.out
  120
  $ ./Asm_test.exe <<- EOF > Asm_test.s
  > let rec foo    a b c d e f g h i j k l m n  o p q  = q
  > let l = foo 1 2 3 4 5 6 7 8 9 0 1 2 3 4  5 6 7
  > let main = print_int l
  > EOF
  $ nasm -f elf64 -o Asm_test.o Asm_test.s
  $ gcc -o asm.out Asm_test.o ../../lib/runtime/runtime.o 2> /dev/null
  $ ./asm.out
  7
  $ ./Asm_test.exe <<- EOF > Asm_test.s
  > let rec foo    _ _ _ _ e f _  = e
  > let k = foo 1 2 3 4 5 6 7
  > let main = print_int k
  > EOF
  $ nasm -f elf64 -o Asm_test.o Asm_test.s
  $ gcc -o asm.out Asm_test.o ../../lib/runtime/runtime.o 2> /dev/null
  $ ./asm.out
  5
  $ ./Asm_test.exe <<- EOF > Asm_test.s
  > let main = print_int ( (5 + 4) - 2 )
  > EOF
  $ cat Asm_test.s
  extern print_bool
  extern print_int
  extern applyPAppli
  extern addNewPAppliClosure
  global main
  main:
    push rbp
    mov rbp, rsp
    sub rsp, 32
    mov rax, 5
    add rax, 4
    mov qword [rbp -8], rax
    mov rax, qword [rbp -8]
    sub rax, 2
    mov qword [rbp -16], rax
    mov rax, print_int
    mov rdi, rax
    mov rsi, 1
    call addNewPAppliClosure
    mov qword [rbp -24], rax
    mov rdi, qword [rbp -24]
    mov rsi, qword [rbp -16]
    call applyPAppli
    mov qword [rbp -32], rax
    mov rax, qword [rbp -32]
    add rsp, 32
    mov rsp, rbp
    pop rbp
    ret
  
