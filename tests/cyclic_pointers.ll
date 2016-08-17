; degenerated case, in pseudo C, this would give:
; static int* a = (int*)&b;
; static int* b = (int*)&a;
; This can happen from real C code (e.g using function inlining).
$a = comdat any
$b = comdat any

@a = private global i8* bitcast (i8** @b to i8*), comdat, align 8
@b = private global i8* bitcast (i8** @a to i8*), comdat, align 8

