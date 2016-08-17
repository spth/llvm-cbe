; String literal forward declaration
%MyType = type {
    { i8* }
}

$MyValue = comdat any

@MyValue = global %MyType {
    { i8* } { i8* getelementptr inbounds ([6 x i8], [6 x i8]* @MyStringLiteral, i32 0, i32 0) }
}, comdat

@MyStringLiteral = private global [6 x i8] c"HELLO\00"

