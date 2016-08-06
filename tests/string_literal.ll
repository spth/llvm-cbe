$A = comdat any
@A = linkonce_odr global [6 x i8]* @MyStringLiteral
@MyStringLiteral = private unnamed_addr constant [6 x i8] c"HELLO\00" ; [#uses = 1])
