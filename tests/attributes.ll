@a = common global i32 0, align 4
@b = common global i32 0, align 4

; volatile write
define void @f()
{
  store volatile i32 1234, i32* @a, align 4
  store i32 1234, i32* @b, align 4
  ret void
}

