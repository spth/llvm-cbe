$sum_of_squares = comdat any

define i32 @sum_of_squares([4 x i32]* byval align 4 %tab) #0 comdat {
  %r = alloca i32, align 4
  %i = alloca i32, align 4
  %i1 = alloca i32, align 4
  store i32 0, i32* %r
  store i32 0, i32* %i
  br label %forcond

forcond:
  %1 = load i32, i32* %i
  %2 = icmp slt i32 %1, 4
  br i1 %2, label %forbody, label %endfor

forbody:
  %3 = load i32, i32* %i
  %4 = sext i32 %3 to i64
  %5 = getelementptr [4 x i32], [4 x i32]* %tab, i32 0, i64 %4
  %6 = load i32, i32* %i
  %7 = sext i32 %6 to i64
  %8 = getelementptr [4 x i32], [4 x i32]* %tab, i32 0, i64 %7
  %9 = load i32, i32* %8
  %10 = load i32, i32* %i
  %11 = sext i32 %10 to i64
  %12 = getelementptr [4 x i32], [4 x i32]* %tab, i32 0, i64 %11
  %13 = load i32, i32* %12
  %14 = mul i32 %9, %13
  store i32 %14, i32* %5
  br label %forinc

forinc:
  %15 = load i32, i32* %i
  %16 = add i32 %15, 1
  store i32 %16, i32* %i
  br label %forcond

endfor:
  store i32 0, i32* %i1
  br label %forcond2

forcond2:
  %17 = load i32, i32* %i1
  %18 = icmp slt i32 %17, 4
  br i1 %18, label %forbody3, label %endfor5

forbody3:
  %19 = load i32, i32* %i1
  %20 = sext i32 %19 to i64
  %21 = getelementptr [4 x i32], [4 x i32]* %tab, i32 0, i64 %20
  %22 = load i32, i32* %21
  %23 = load i32, i32* %r
  %24 = add i32 %23, %22
  store i32 %24, i32* %r
  br label %forinc4

forinc4:
  %25 = load i32, i32* %i1
  %26 = add i32 %25, 1
  store i32 %26, i32* %i1
  br label %forcond2

endfor5:
  %27 = load i32, i32* %r
  %28 = load i32, i32* %r
  ret i32 %28
}
