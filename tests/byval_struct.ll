
define void @MyFunction({ i64 }* byval %structuredArgument)
{
  %1 = load { i64 }, { i64 }* %structuredArgument
  ret void
}

