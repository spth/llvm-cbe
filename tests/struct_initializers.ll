%MyStruct = type { i8* }

@MyInstance = global %MyStruct { i8* getelementptr inbounds ([14 x i8], [14 x i8]* @MyStringLiteral, i32 0, i32 0) }
@MyStringLiteral = unnamed_addr constant [14 x i8] c"Hello, world!\00"

